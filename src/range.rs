use std::cmp::{Ord, Ordering, PartialOrd};
use std::fmt;
#[cfg(not(feature = "miette"))]
use std::marker::PhantomData;

use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::{anychar, space0, space1};
use nom::combinator::{all_consuming, eof, map, map_res, opt, peek};
use nom::error::context;
use nom::multi::{many_till, separated_list0};
use nom::sequence::{delimited, preceded, terminated};
use nom::{Err, IResult, Parser};

use crate::{Identifier, SemverError, SemverErrorKind, SemverParseError, Version, extras, number};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct BoundSet {
    upper: Bound,
    lower: Bound,
}

impl BoundSet {
    fn new(lower: Bound, upper: Bound) -> Option<Self> {
        use Bound::{Lower, Upper};
        use Predicate::{Excluding, Including};

        match (lower, upper) {
            (Lower(Excluding(v1)), Upper(Including(v2)))
            | (Lower(Including(v1)), Upper(Excluding(v2)))
                if v1 == v2 =>
            {
                None
            }
            (Lower(Including(v1)), Upper(Including(v2))) if v1 == v2 => Some(Self {
                lower: Lower(Including(v1)),
                upper: Upper(Including(v2)),
            }),
            (lower, upper) if lower < upper => Some(Self { upper, lower }),
            _ => None,
        }
    }

    fn at_least(p: Predicate) -> Option<Self> {
        Self::new(Bound::Lower(p), Bound::upper())
    }

    fn at_most(p: Predicate) -> Option<Self> {
        Self::new(Bound::lower(), Bound::Upper(p))
    }

    fn exact(version: Version) -> Option<Self> {
        Self::new(
            Bound::Lower(Predicate::Including(version.clone())),
            Bound::Upper(Predicate::Including(version)),
        )
    }

    fn satisfies(&self, version: &Version) -> bool {
        use Bound::{Lower, Upper};
        use Predicate::{Excluding, Including, Unbounded};

        let lower_bound = match &self.lower {
            Lower(Including(lower)) => lower <= version,
            Lower(Excluding(lower)) => lower < version,
            Lower(Unbounded) => true,
            _ => unreachable!(
                "There should not have been an upper bound: {:#?}",
                self.lower
            ),
        };

        let upper_bound = match &self.upper {
            Upper(Including(upper)) => version <= upper,
            Upper(Excluding(upper)) => version < upper,
            Upper(Unbounded) => true,
            _ => unreachable!(
                "There should not have been an lower bound: {:#?}",
                self.lower
            ),
        };

        if !lower_bound || !upper_bound {
            return false;
        }

        if version.is_prerelease() {
            let lower_version = match &self.lower {
                Lower(Including(v) | Excluding(v)) => Some(v),
                _ => None,
            };
            if let Some(lower_version) = lower_version {
                if lower_version.is_prerelease()
                    && version.major == lower_version.major
                    && version.minor == lower_version.minor
                    && version.patch == lower_version.patch
                {
                    return true;
                }
            }

            let upper_version = match &self.upper {
                Upper(Including(v) | Excluding(v)) => Some(v),
                _ => None,
            };
            if let Some(upper_version) = upper_version {
                if upper_version.is_prerelease()
                    && version.major == upper_version.major
                    && version.minor == upper_version.minor
                    && version.patch == upper_version.patch
                {
                    return true;
                }
            }

            return false;
        }

        true
    }

    fn allows_all(&self, other: &Self) -> bool {
        self.lower <= other.lower && other.upper <= self.upper
    }

    fn allows_any(&self, other: &Self) -> bool {
        if other.upper < self.lower {
            return false;
        }

        if self.upper < other.lower {
            return false;
        }

        true
    }

    fn intersect(&self, other: &Self) -> Option<Self> {
        let lower = std::cmp::max(&self.lower, &other.lower);
        let upper = std::cmp::min(&self.upper, &other.upper);

        Self::new(lower.clone(), upper.clone())
    }

    fn difference(&self, other: &Self) -> Option<Vec<Self>> {
        use Bound::{Lower, Upper};

        if let Some(overlap) = self.intersect(other) {
            if &overlap == self {
                return None;
            }

            if self.lower < overlap.lower && overlap.upper < self.upper {
                return Some(vec![
                    Self::new(self.lower.clone(), Upper(overlap.lower.predicate().flip())).unwrap(),
                    Self::new(Lower(overlap.upper.predicate().flip()), self.upper.clone()).unwrap(),
                ]);
            }

            if self.lower < overlap.lower {
                return Self::new(self.lower.clone(), Upper(overlap.lower.predicate().flip()))
                    .map(|f| vec![f]);
            }

            Self::new(Lower(overlap.upper.predicate().flip()), self.upper.clone()).map(|f| vec![f])
        } else {
            Some(vec![self.clone()])
        }
    }
}

impl fmt::Display for BoundSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Bound::{Lower, Upper};
        use Predicate::{Excluding, Including, Unbounded};
        match (&self.lower, &self.upper) {
            (Lower(Unbounded), Upper(Unbounded)) => write!(f, "*"),
            (Lower(Unbounded), Upper(Including(v))) => write!(f, "<={v}"),
            (Lower(Unbounded), Upper(Excluding(v))) => write!(f, "<{v}"),
            (Lower(Including(v)), Upper(Unbounded)) => write!(f, ">={v}"),
            (Lower(Excluding(v)), Upper(Unbounded)) => write!(f, ">{v}"),
            (Lower(Including(v)), Upper(Including(v2))) if v == v2 => write!(f, "{v}"),
            (Lower(Including(v)), Upper(Including(v2))) => write!(f, ">={v} <={v2}"),
            (Lower(Including(v)), Upper(Excluding(v2))) => write!(f, ">={v} <{v2}"),
            (Lower(Excluding(v)), Upper(Including(v2))) => write!(f, ">{v} <={v2}"),
            (Lower(Excluding(v)), Upper(Excluding(v2))) => write!(f, ">{v} <{v2}"),
            _ => unreachable!("does not make sense"),
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
enum Operation {
    Exact,
    GreaterThan,
    GreaterThanEquals,
    LessThan,
    LessThanEquals,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum Predicate {
    Excluding(Version), // < and >
    Including(Version), // <= and >=
    Unbounded,          // *
}

impl Predicate {
    fn flip(self) -> Self {
        use Predicate::{Excluding, Including, Unbounded};
        match self {
            Excluding(v) => Including(v),
            Including(v) => Excluding(v),
            Unbounded => Unbounded,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum Bound {
    Lower(Predicate),
    Upper(Predicate),
}

impl Bound {
    const fn upper() -> Self {
        Self::Upper(Predicate::Unbounded)
    }

    const fn lower() -> Self {
        Self::Lower(Predicate::Unbounded)
    }

    fn predicate(self) -> Predicate {
        use Bound::{Lower, Upper};

        match self {
            Lower(p) | Upper(p) => p,
        }
    }
}

impl Ord for Bound {
    fn cmp(&self, other: &Self) -> Ordering {
        use Bound::{Lower, Upper};
        use Predicate::{Excluding, Including, Unbounded};

        match (self, other) {
            (Lower(Unbounded), Lower(Unbounded)) | (Upper(Unbounded), Upper(Unbounded)) => {
                Ordering::Equal
            }
            (Upper(Unbounded), _) | (_, Lower(Unbounded)) => Ordering::Greater,
            (Lower(Unbounded), _) | (_, Upper(Unbounded)) => Ordering::Less,
            (
                Upper(Including(v1)) | Lower(Including(v1)),
                Upper(Including(v2)) | Lower(Including(v2)),
            )
            | (Upper(Excluding(v1)), Upper(Excluding(v2)) | Lower(Excluding(v2)))
            | (Lower(Excluding(v1)), Lower(Excluding(v2))) => v1.cmp(v2),
            (Lower(Excluding(v1) | Including(v1)), Upper(Excluding(v2))) => {
                if v2 <= v1 {
                    Ordering::Greater
                } else {
                    Ordering::Less
                }
            }
            (Upper(Including(v1)), Upper(Excluding(v2)) | Lower(Excluding(v2)))
            | (Lower(Excluding(v1)), Upper(Including(v2))) => {
                if v2 < v1 {
                    Ordering::Greater
                } else {
                    Ordering::Less
                }
            }
            (Lower(Excluding(v1)), Lower(Including(v2))) => {
                if v1 < v2 {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            }
            (Lower(Including(v1)), Lower(Excluding(v2)))
            | (Upper(Excluding(v1)), Lower(Including(v2)) | Upper(Including(v2))) => {
                if v1 <= v2 {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            }
        }
    }
}

impl PartialOrd for Bound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Node-style semver range.
///
/// These ranges map mostly 1:1 to semver's except for some internal representation
/// details that allow some more interesting set-level operations.
///
/// For details on supported syntax, see <https://github.com/npm/node-semver#advanced-range-syntax>
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Range(Vec<BoundSet>);

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Operation::{Exact, GreaterThan, GreaterThanEquals, LessThan, LessThanEquals};
        match self {
            Exact => write!(f, ""),
            GreaterThan => write!(f, ">"),
            GreaterThanEquals => write!(f, ">="),
            LessThan => write!(f, "<"),
            LessThanEquals => write!(f, "<="),
        }
    }
}

impl Range {
    /// Parse a range from a string.
    pub fn parse<S: AsRef<str>>(input: S) -> Result<Self, SemverError> {
        let input = input.as_ref();

        match all_consuming(range_set).parse(input) {
            Ok((_, range)) => Ok(range),
            Err(err) => Err(match err {
                Err::Error(e) | Err::Failure(e) => SemverError {
                    input: input.into(),
                    #[cfg(feature = "miette")]
                    span: (e.input.as_ptr() as usize - input.as_ptr() as usize, 0).into(),
                    kind: if let Some(kind) = e.kind {
                        kind
                    } else if let Some(ctx) = e.context {
                        SemverErrorKind::Context(ctx)
                    } else {
                        SemverErrorKind::Other
                    },
                },
                Err::Incomplete(_) => SemverError {
                    input: input.into(),
                    #[cfg(feature = "miette")]
                    span: (input.len() - 1, 0).into(),
                    kind: SemverErrorKind::IncompleteInput,
                },
            }),
        }
    }

    /// Creates a new range that matches any version.
    #[must_use]
    pub fn any() -> Self {
        Self(vec![BoundSet::new(Bound::lower(), Bound::upper()).unwrap()])
    }

    /// Returns true if `version` is satisfied by this range.
    #[must_use]
    pub fn satisfies(&self, version: &Version) -> bool {
        for range in &self.0 {
            if range.satisfies(version) {
                return true;
            }
        }

        false
    }

    /// Returns true if `other` is a strict superset of this range.
    #[must_use]
    pub fn allows_all(&self, other: &Self) -> bool {
        for this in &self.0 {
            for that in &other.0 {
                if this.allows_all(that) {
                    return true;
                }
            }
        }

        false
    }

    /// Returns true if `other` has overlap with this range.
    #[must_use]
    pub fn allows_any(&self, other: &Self) -> bool {
        for this in &self.0 {
            for that in &other.0 {
                if this.allows_any(that) {
                    return true;
                }
            }
        }

        false
    }

    /// Returns a new range that is the set-intersection between this range and `other`.
    #[must_use]
    pub fn intersect(&self, other: &Self) -> Option<Self> {
        let mut sets = Vec::new();

        for lefty in &self.0 {
            for righty in &other.0 {
                if let Some(set) = lefty.intersect(righty) {
                    sets.push(set);
                }
            }
        }

        if sets.is_empty() {
            None
        } else {
            Some(Self(sets))
        }
    }

    /// Returns a new range that is the set-difference between this range and `other`.
    #[must_use]
    pub fn difference(&self, other: &Self) -> Option<Self> {
        let mut predicates = Vec::new();

        for lefty in &self.0 {
            for righty in &other.0 {
                if let Some(mut range) = lefty.difference(righty) {
                    predicates.append(&mut range);
                }
            }
        }

        if predicates.is_empty() {
            None
        } else {
            Some(Self(predicates))
        }
    }

    /// Returns the minimum version that satisfies this range.
    #[must_use]
    pub fn min_version(&self) -> Option<Version> {
        if let Some(min_bound) = self.0.iter().map(|range| &range.lower).min() {
            match min_bound {
                Bound::Lower(pred) => match pred {
                    Predicate::Including(v) => Some(v.clone()),
                    Predicate::Excluding(v) => {
                        let mut v = v.clone();
                        if v.is_prerelease() {
                            v.pre_release.push(Identifier::Numeric(0));
                        } else {
                            v.patch += 1;
                        }
                        Some(v)
                    }
                    Predicate::Unbounded => {
                        let mut zero = Version::from((0, 0, 0));
                        if self.satisfies(&zero) {
                            return Some(zero);
                        }

                        zero.pre_release.push(Identifier::Numeric(0));
                        if self.satisfies(&zero) {
                            return Some(zero);
                        }
                        None
                    }
                },
                Bound::Upper(_) => None,
            }
        } else {
            None
        }
    }
}

impl fmt::Display for Range {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, range) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, "||")?;
            }
            write!(f, "{range}")?;
        }
        Ok(())
    }
}

impl std::str::FromStr for Range {
    type Err = SemverError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

// ---- Parser ----
// Grammar from https://github.com/npm/node-semver#range-grammar
//
// range-set  ::= range ( logical-or range ) *
// logical-or ::= ( ' ' ) * '||' ( ' ' ) *
// range      ::= hyphen | simple ( ' ' simple ) * | ''
// hyphen     ::= partial ' - ' partial
// simple     ::= primitive | partial | tilde | caret
// primitive  ::= ( '<' | '>' | '>=' | '<=' | '=' ) partial
// partial    ::= xr ( '.' xr ( '.' xr qualifier ? )? )?
// xr         ::= 'x' | 'X' | '*' | nr
// nr         ::= '0' | ['1'-'9'] ( ['0'-'9'] ) *
// tilde      ::= '~' partial
// caret      ::= '^' partial
// qualifier  ::= ( '-' pre )? ( '+' build )?
// pre        ::= parts
// build      ::= parts
// parts      ::= part ( '.' part ) *
// part       ::= nr | [-0-9A-Za-z]+
//
//
// Loose mode (all LHS are invalid in strict mode):
// * 01.02.03 -> 1.2.3
// * 1.2.3alpha -> 1.2.3-alpha
// * v 1.2.3 -> 1.2.3 (v1.2.3 is actually a valid "plain" version)
// * =1.2.3 -> 1.2.3 (already a valid range)
// * - 10 -> >=10.0.0 <11.0.0
// * 1.2.3 foo 4.5.6 -> 1.2.3 4.5.6
// * 1.2.3.4 -> invalid range
// * foo -> invalid range
// * 1.2beta4 -> invalid range
//
// TODO: add tests for all these

// range-set ::= range ( logical-or range ) *
fn range_set(input: &str) -> IResult<&str, Range, SemverParseError<&str>> {
    map_res(bound_sets, |sets| {
        if sets.is_empty() {
            Err(SemverParseError {
                #[cfg(feature = "miette")]
                input,
                kind: Some(SemverErrorKind::NoValidRanges),
                context: None,
                #[cfg(not(feature = "miette"))]
                _phantom: PhantomData,
            })
        } else {
            Ok(Range(sets))
        }
    })
    .parse(input)
}

// logical-or ::= ( ' ' ) * '||' ( ' ' ) *
fn bound_sets(input: &str) -> IResult<&str, Vec<BoundSet>, SemverParseError<&str>> {
    map(separated_list0(logical_or, range), |sets| {
        sets.into_iter().flatten().collect()
    })
    .parse(input)
}
fn logical_or(input: &str) -> IResult<&str, (), SemverParseError<&str>> {
    map(delimited(space0, tag("||"), space0), |_| ()).parse(input)
}

fn range(input: &str) -> IResult<&str, Vec<BoundSet>, SemverParseError<&str>> {
    // TODO: loose parsing means that `1.2.3 foo` translates to `1.2.3`, so we
    // need to do some stuff here to filter out unwanted BoundSets.
    map(separated_list0(space1, simple), |bs| {
        bs.into_iter()
            .flatten()
            .fold(Vec::new(), |mut acc: Vec<BoundSet>, bs| {
                if let Some(last) = acc.pop() {
                    if let Some(bound) = last.intersect(&bs) {
                        acc.push(bound);
                    } else {
                        acc.push(last);
                        acc.push(bs);
                    }
                } else {
                    acc.push(bs);
                }
                acc
            })
    })
    .parse(input)
}

// simple ::= primitive | partial | tilde | caret | garbage
fn simple(input: &str) -> IResult<&str, Option<BoundSet>, SemverParseError<&str>> {
    alt((
        terminated(hyphen, peek(alt((space1, tag("||"), eof)))),
        terminated(primitive, peek(alt((space1, tag("||"), eof)))),
        terminated(partial, peek(alt((space1, tag("||"), eof)))),
        terminated(tilde, peek(alt((space1, tag("||"), eof)))),
        terminated(caret, peek(alt((space1, tag("||"), eof)))),
        garbage,
    ))
    .parse(input)
}

fn garbage(input: &str) -> IResult<&str, Option<BoundSet>, SemverParseError<&str>> {
    map(
        many_till(anychar, alt((peek(space1), peek(tag("||")), eof))),
        |_| None,
    )
    .parse(input)
}

// primitive  ::= ( '<' | '>' | '>=' | '<=' | '=' ) partial
fn primitive(input: &str) -> IResult<&str, Option<BoundSet>, SemverParseError<&str>> {
    use Operation::{Exact, GreaterThan, GreaterThanEquals, LessThan, LessThanEquals};
    context(
        "operation range (ex: >= 1.2.3)",
        map((operation, preceded(space0, partial_version)), |parsed| {
            match parsed {
                (GreaterThanEquals, partial) => {
                    BoundSet::at_least(Predicate::Including(partial.into()))
                }
                (
                    GreaterThan,
                    Partial {
                        major: Some(major),
                        minor: Some(minor),
                        patch: None,
                        ..
                    },
                ) => BoundSet::at_least(Predicate::Including((major, minor + 1, 0).into())),
                (
                    GreaterThan,
                    Partial {
                        major: Some(major),
                        minor: None,
                        patch: None,
                        ..
                    },
                ) => BoundSet::at_least(Predicate::Including((major + 1, 0, 0).into())),
                (GreaterThan, partial) => BoundSet::at_least(Predicate::Excluding(partial.into())),
                (
                    LessThan,
                    Partial {
                        major: Some(major),
                        minor: Some(minor),
                        patch: None,
                        ..
                    },
                ) => BoundSet::at_most(Predicate::Excluding((major, minor, 0, 0).into())),
                (
                    LessThan,
                    Partial {
                        major,
                        minor,
                        patch,
                        pre_release,
                        build,
                        ..
                    },
                ) => BoundSet::at_most(Predicate::Excluding(Version {
                    major: major.unwrap_or(0),
                    minor: minor.unwrap_or(0),
                    patch: patch.unwrap_or(0),
                    build,
                    pre_release,
                })),
                (
                    LessThanEquals,
                    Partial {
                        major,
                        minor,
                        patch: None,
                        ..
                    },
                ) => BoundSet::at_most(Predicate::Including(
                    (major.unwrap_or(0), minor.unwrap_or(0), 0, 0).into(),
                )),
                (LessThanEquals, partial) => {
                    BoundSet::at_most(Predicate::Including(partial.into()))
                }
                (
                    Exact,
                    Partial {
                        major: Some(major),
                        minor: Some(minor),
                        patch: Some(patch),
                        pre_release,
                        ..
                    },
                ) => BoundSet::exact( Version {
                    major,
                    minor,
                    patch,
                    pre_release,
                    build: vec![],
                }),
                (
                    Exact,
                    Partial {
                        major: Some(major),
                        minor: Some(minor),
                        ..
                    },
                ) => BoundSet::new(
                    Bound::Lower(Predicate::Including(
                        (major, minor, 0).into(),
                    )),
                    Bound::Upper(Predicate::Excluding(Version {
                        major,
                        minor: minor + 1,
                        patch: 0,
                        pre_release: vec![Identifier::Numeric(0)],
                        build: vec![],
                    })),
                ),
                (
                    Exact,
                    Partial {
                        major: Some(major),
                        ..
                    },
                ) => BoundSet::new(
                    Bound::Lower(Predicate::Including(
                        (major, 0, 0).into(),
                    )),
                    Bound::Upper(Predicate::Excluding(Version {
                        major: major + 1,
                        minor: 0,
                        patch: 0,
                        pre_release: vec![Identifier::Numeric(0)],
                        build: vec![],
                    })),
                ),
                _ => unreachable!("Failed to parse operation. This should not happen and should be reported as a bug, while parsing {}", input),
            }
        }),
    ).parse(input)
}

fn operation(input: &str) -> IResult<&str, Operation, SemverParseError<&str>> {
    use Operation::{Exact, GreaterThan, GreaterThanEquals, LessThan, LessThanEquals};
    alt((
        map(tag(">="), |_| GreaterThanEquals),
        map(tag(">"), |_| GreaterThan),
        map(tag("="), |_| Exact),
        map(tag("<="), |_| LessThanEquals),
        map(tag("<"), |_| LessThan),
    ))
    .parse(input)
}

fn partial(input: &str) -> IResult<&str, Option<BoundSet>, SemverParseError<&str>> {
    context(
        "plain version range (ex: 1.2)",
        map(partial_version, |partial| match partial {
            Partial { major: None, .. } => {
                BoundSet::at_least(Predicate::Including((0, 0, 0).into()))
            }
            Partial {
                major: Some(major),
                minor: None,
                ..
            } => BoundSet::new(
                Bound::Lower(Predicate::Including((major, 0, 0).into())),
                Bound::Upper(Predicate::Excluding(Version {
                    major: major + 1,
                    minor: 0,
                    patch: 0,
                    pre_release: vec![Identifier::Numeric(0)],
                    build: vec![],
                })),
            ),
            Partial {
                major: Some(major),
                minor: Some(minor),
                patch: None,
                ..
            } => BoundSet::new(
                Bound::Lower(Predicate::Including((major, minor, 0).into())),
                Bound::Upper(Predicate::Excluding(Version {
                    major,
                    minor: minor + 1,
                    patch: 0,
                    pre_release: vec![Identifier::Numeric(0)],
                    build: vec![],
                })),
            ),
            partial => BoundSet::exact(partial.into()),
        }),
    )
    .parse(input)
}

#[derive(Debug, Clone)]
struct Partial {
    major: Option<u64>,
    minor: Option<u64>,
    patch: Option<u64>,
    pre_release: Vec<Identifier>,
    build: Vec<Identifier>,
}

impl From<Partial> for Version {
    fn from(partial: Partial) -> Self {
        Self {
            major: partial.major.unwrap_or(0),
            minor: partial.minor.unwrap_or(0),
            patch: partial.patch.unwrap_or(0),
            pre_release: partial.pre_release,
            build: partial.build,
        }
    }
}

// partial ::= xr ( '.' xr ( '.' xr qualifier ? )? )?
// xr      ::= 'x' | 'X' | '*' | nr
// nr      ::= '0' | ['1'-'9'] ( ['0'-'9'] ) *
// NOTE: Loose mode means nr is actually just `['0'-'9']`.
fn partial_version(input: &str) -> IResult<&str, Partial, SemverParseError<&str>> {
    let (input, _) = opt(tag("v")).parse(input)?;
    let (input, _) = space0(input)?;
    let (input, major) = component(input)?;
    let (input, minor) = opt(preceded(tag("."), component)).parse(input)?;
    let (input, patch) = opt(preceded(tag("."), component)).parse(input)?;
    let (input, (pre, build)) = if patch.is_some() {
        extras(input)?
    } else {
        (input, (vec![], vec![]))
    };
    Ok((
        input,
        Partial {
            major,
            minor: minor.flatten(),
            patch: patch.flatten(),
            pre_release: pre,
            build,
        },
    ))
}

fn component(input: &str) -> IResult<&str, Option<u64>, SemverParseError<&str>> {
    alt((map(x_or_asterisk, |()| None), map(number, Some))).parse(input)
}

fn x_or_asterisk(input: &str) -> IResult<&str, (), SemverParseError<&str>> {
    map(alt((tag("x"), tag("X"), tag("*"))), |_| ()).parse(input)
}

fn tilde_gt(input: &str) -> IResult<&str, Option<&str>, SemverParseError<&str>> {
    map(
        (tag("~"), space0, opt(tag(">")), space0),
        |(_, _, gt, _)| gt,
    )
    .parse(input)
}

fn tilde(input: &str) -> IResult<&str, Option<BoundSet>, SemverParseError<&str>> {
    context(
        "tilde version range (ex: ~1.2.3)",
        map((tilde_gt, partial_version), |parsed| match parsed {
            (
                Some(_gt),
                Partial {
                    major: Some(major),
                    minor: None,
                    patch: None,
                    ..
                },
            ) => BoundSet::new(
                Bound::Lower(Predicate::Including((major, 0, 0).into())),
                Bound::Upper(Predicate::Excluding((major + 1, 0, 0, 0).into())),
            ),
            (
                Some(_gt),
                Partial {
                    major: Some(major),
                    minor: Some(minor),
                    patch,
                    pre_release,
                    ..
                },
            ) => BoundSet::new(
                Bound::Lower(Predicate::Including(Version {
                    major,
                    minor,
                    patch: patch.unwrap_or(0),
                    pre_release,
                    build: vec![],
                })),
                Bound::Upper(Predicate::Excluding((major, minor + 1, 0, 0).into())),
            ),
            (
                None,
                Partial {
                    major: Some(major),
                    minor: Some(minor),
                    patch: Some(patch),
                    pre_release,
                    ..
                },
            ) => BoundSet::new(
                Bound::Lower(Predicate::Including(Version {
                    major,
                    minor,
                    patch,
                    pre_release,
                    build: vec![],
                })),
                Bound::Upper(Predicate::Excluding((major, minor + 1, 0, 0).into())),
            ),
            (
                None,
                Partial {
                    major: Some(major),
                    minor: Some(minor),
                    patch: None,
                    ..
                },
            ) => BoundSet::new(
                Bound::Lower(Predicate::Including((major, minor, 0).into())),
                Bound::Upper(Predicate::Excluding((major, minor + 1, 0, 0).into())),
            ),
            (
                None,
                Partial {
                    major: Some(major),
                    minor: None,
                    patch: None,
                    ..
                },
            ) => BoundSet::new(
                Bound::Lower(Predicate::Including((major, 0, 0).into())),
                Bound::Upper(Predicate::Excluding((major + 1, 0, 0, 0).into())),
            ),
            _ => unreachable!("This should not have parsed: {}", input),
        }),
    )
    .parse(input)
}

fn caret(input: &str) -> IResult<&str, Option<BoundSet>, SemverParseError<&str>> {
    context(
        "caret version range (ex: ^1.2.3)",
        map(
            preceded((tag("^"), space0), partial_version),
            |parsed| match parsed {
                Partial {
                    major: Some(0),
                    minor: None,
                    patch: None,
                    ..
                } => BoundSet::at_most(Predicate::Excluding((1, 0, 0, 0).into())),
                Partial {
                    major: Some(0),
                    minor: Some(minor),
                    patch: None,
                    ..
                } => BoundSet::new(
                    Bound::Lower(Predicate::Including((0, minor, 0).into())),
                    Bound::Upper(Predicate::Excluding((0, minor + 1, 0, 0).into())),
                ),
                // TODO: can be compressed?
                Partial {
                    major: Some(major),
                    minor: None,
                    patch: None,
                    ..
                } => BoundSet::new(
                    Bound::Lower(Predicate::Including((major, 0, 0).into())),
                    Bound::Upper(Predicate::Excluding((major + 1, 0, 0, 0).into())),
                ),
                Partial {
                    major: Some(major),
                    minor: Some(minor),
                    patch: None,
                    ..
                } => BoundSet::new(
                    Bound::Lower(Predicate::Including((major, minor, 0).into())),
                    Bound::Upper(Predicate::Excluding((major + 1, 0, 0, 0).into())),
                ),
                Partial {
                    major: Some(major),
                    minor: Some(minor),
                    patch: Some(patch),
                    pre_release,
                    ..
                } => BoundSet::new(
                    Bound::Lower(Predicate::Including(Version {
                        major,
                        minor,
                        patch,
                        pre_release,
                        build: vec![],
                    })),
                    Bound::Upper(Predicate::Excluding(match (major, minor, patch) {
                        (0, 0, n) => Version::from((0, 0, n + 1, 0)),
                        (0, n, _) => Version::from((0, n + 1, 0, 0)),
                        (n, _, _) => Version::from((n + 1, 0, 0, 0)),
                    })),
                ),
                _ => None,
            },
        ),
    )
    .parse(input)
}

// hyphen ::= ' - ' partial /* loose */ | partial ' - ' partial
fn hyphen(input: &str) -> IResult<&str, Option<BoundSet>, SemverParseError<&str>> {
    context("hyphenated version range (ex: 1.2 - 2)", |input| {
        let (input, lower) = opt(partial_version).parse(input)?;
        let (input, _) = space1(input)?;
        let (input, _) = tag("-")(input)?;
        let (input, _) = space1(input)?;
        let (input, upper) = partial_version(input)?;
        let upper = match upper {
            Partial {
                major: None,
                minor: None,
                patch: None,
                ..
            } => Predicate::Excluding(Version {
                major: 0,
                minor: 0,
                patch: 0,
                pre_release: vec![Identifier::Numeric(0)],
                build: vec![],
            }),
            Partial {
                major: Some(major),
                minor: None,
                patch: None,
                ..
            } => Predicate::Excluding(Version {
                major: major + 1,
                minor: 0,
                patch: 0,
                pre_release: vec![Identifier::Numeric(0)],
                build: vec![],
            }),
            Partial {
                major: Some(major),
                minor: Some(minor),
                patch: None,
                ..
            } => Predicate::Excluding(Version {
                major,
                minor: minor + 1,
                patch: 0,
                pre_release: vec![Identifier::Numeric(0)],
                build: vec![],
            }),
            partial => Predicate::Including(partial.into()),
        };
        let bounds = if let Some(lower) = lower {
            BoundSet::new(
                Bound::Lower(Predicate::Including(lower.into())),
                Bound::Upper(upper),
            )
        } else {
            BoundSet::at_most(upper)
        };
        Ok((input, bounds))
    })
    .parse(input)
}

macro_rules! create_tests_for {
    ($func:ident $($name:ident => $version_range:expr , { $x:ident => $allows:expr, $y:ident => $denies:expr$(,)? }),+ ,$(,)?) => {

        #[cfg(test)]
        mod $func {
        use super::*;

            $(
                #[test]
                fn $name() {
                    let version_range = Range::parse($version_range).unwrap();

                    let allows: Vec<Range> = $allows.iter().map(|v| Range::parse(v).unwrap()).collect();
                    for version in &allows {
                        assert!(version_range.$func(version), "should have allowed: {}", version);
                    }

                    let ranges: Vec<Range> = $denies.iter().map(|v| Range::parse(v).unwrap()).collect();
                    for version in &ranges {
                        assert!(!version_range.$func(version), "should have denied: {}", version);
                    }
                }
            )+
        }
    }
}

create_tests_for! {
    // The function we are testing:
    allows_all

    greater_than_eq_123   => ">=1.2.3", {
        allows => [">=2.0.0", ">2", "2.0.0", "0.1 || 1.4", "1.2.3", "2 - 7", ">2.0.0"],
        denies => ["1.0.0", "<1.2", ">=1.2.2", "1 - 3", "0.1 || <1.2.0", ">1.0.0"],
    },

    greater_than_123      => ">1.2.3", {
        allows => [">=2.0.0", ">2", "2.0.0", "0.1 || 1.4", ">2.0.0"],
        denies => ["1.0.0", "<1.2", ">=1.2.3", "1 - 3", "0.1 || <1.2.0", "<=3"],
    },

    eq_123  => "1.2.3", {
        allows => ["1.2.3"],
        denies => ["1.0.0", "<1.2", "1.x", ">=1.2.2", "1 - 3", "0.1 || <1.2.0"],
    },

    lt_123  => "<1.2.3", {
        allows => ["<=1.2.0", "<1", "1.0.0", "0.1 || 1.4"],
        denies => ["1 - 3", ">1", "2.0.0", "2.0 || >9", ">1.0.0"],
    },

    lt_eq_123 => "<=1.2.3", {
        allows => ["<=1.2.0", "<1", "1.0.0", "0.1 || 1.4", "1.2.3"],
        denies => ["1 - 3", ">1.0.0", ">=1.0.0"],
    },

    eq_123_or_gt_400  => "1.2.3 || >4", {
        allows => [ "1.2.3", ">4", "5.x", "5.2.x", ">=8.2.1", "2.0 || 5.6.7"],
        denies => ["<2", "1 - 7", "1.9.4 || 2 - 3"],
    },

    between_two_and_eight => "2 - 8", {
        allows => [ "2.2.3", "4 - 5"],
        denies => ["1 - 4", "5 - 9", ">3", "<=5"],
    },
}

create_tests_for! {
    // The function we are testing:
    allows_any

    greater_than_eq_123   => ">=1.2.3", {
        allows => ["<=1.2.4", "3.0.0", "<2", ">=3", ">3.0.0"],
        denies => ["<=1.2.0", "1.0.0", "<1", "<=1.2"],
    },

    greater_than_123   => ">1.2.3", {
        allows => ["<=1.2.4", "3.0.0", "<2", ">=3", ">3.0.0"],
        denies => ["<=1.2.3", "1.0.0", "<1", "<=1.2"],
    },

    eq_123   => "1.2.3", {
        allows => ["1.2.3", "1 - 2"],
        denies => ["<1.2.3", "1.0.0", "<=1.2", ">4.5.6", ">5"],
    },

    lt_eq_123  => "<=1.2.3", {
        allows => ["<=1.2.0", "<1.0.0", "1.0.0", ">1.0.0", ">=1.2.0"],
        denies => ["4.5.6", ">2.0.0", ">=2.0.0"],
    },

    lt_123  => "<1.2.3", {
        allows => ["<=2.2.0", "<2.0.0", "1.0.0", ">1.0.0", ">=1.2.0"],
        denies => ["2.0.0", ">1.8.0", ">=1.8.0"],
    },

    between_two_and_eight => "2 - 8", {
        allows => ["2.2.3", "4 - 10", ">4", ">4.0.0", "<=4.0.0", "<9.1.2"],
        denies => [">10", "10 - 11", "0 - 1"],
    },

    eq_123_or_gt_400  => "1.2.3 || >4", {
        allows => [ "1.2.3", ">3", "5.x", "5.2.x", ">=8.2.1", "2 - 7", "2.0 || 5.6.7"],
        denies => [ "1.9.4 || 2 - 3"],
    },
}

#[cfg(test)]
mod intersection {
    use super::*;

    fn v(range: &'static str) -> Range {
        range.parse().unwrap()
    }

    #[test]
    fn gt_eq_123() {
        let base_range = v(">=1.2.3");

        let samples = vec![
            ("<=2.0.0", Some(">=1.2.3 <=2.0.0")),
            ("<2.0.0", Some(">=1.2.3 <2.0.0")),
            (">=2.0.0", Some(">=2.0.0")),
            (">2.0.0", Some(">2.0.0")),
            (">1.0.0", Some(">=1.2.3")),
            (">1.2.3", Some(">1.2.3")),
            ("<=1.2.3", Some("1.2.3")),
            ("2.0.0", Some("2.0.0")),
            ("1.1.1", None),
            ("<1.0.0", None),
        ];

        assert_ranges_match(base_range, samples);
    }

    #[test]
    fn gt_123() {
        let base_range = v(">1.2.3");

        let samples = vec![
            ("<=2.0.0", Some(">1.2.3 <=2.0.0")),
            ("<2.0.0", Some(">1.2.3 <2.0.0")),
            (">=2.0.0", Some(">=2.0.0")),
            (">2.0.0", Some(">2.0.0")),
            ("2.0.0", Some("2.0.0")),
            (">1.2.3", Some(">1.2.3")),
            ("<=1.2.3", None),
            ("1.1.1", None),
            ("<1.0.0", None),
        ];

        assert_ranges_match(base_range, samples);
    }

    #[test]
    fn eq_123() {
        let base_range = v("1.2.3");

        let samples = vec![
            ("<=2.0.0", Some("1.2.3")),
            ("<2.0.0", Some("1.2.3")),
            (">=2.0.0", None),
            (">2.0.0", None),
            ("2.0.0", None),
            ("1.2.3", Some("1.2.3")),
            (">1.2.3", None),
            ("<=1.2.3", Some("1.2.3")),
            ("1.1.1", None),
            ("<1.0.0", None),
        ];

        assert_ranges_match(base_range, samples);
    }

    #[test]
    fn lt_123() {
        let base_range = v("<1.2.3");

        let samples = vec![
            ("<=2.0.0", Some("<1.2.3")),
            ("<2.0.0", Some("<1.2.3")),
            (">=2.0.0", None),
            (">=1.0.0", Some(">=1.0.0 <1.2.3")),
            (">2.0.0", None),
            ("2.0.0", None),
            ("1.2.3", None),
            (">1.2.3", None),
            ("<=1.2.3", Some("<1.2.3")),
            ("1.1.1", Some("1.1.1")),
            ("<1.0.0", Some("<1.0.0")),
        ];

        assert_ranges_match(base_range, samples);
    }

    #[test]
    fn lt_eq_123() {
        let base_range = v("<=1.2.3");

        let samples = vec![
            ("<=2.0.0", Some("<=1.2.3")),
            ("<2.0.0", Some("<=1.2.3")),
            (">=2.0.0", None),
            (">=1.0.0", Some(">=1.0.0 <=1.2.3")),
            (">2.0.0", None),
            ("2.0.0", None),
            ("1.2.3", Some("1.2.3")),
            (">1.2.3", None),
            ("<=1.2.3", Some("<=1.2.3")),
            ("1.1.1", Some("1.1.1")),
            ("<1.0.0", Some("<1.0.0")),
        ];

        assert_ranges_match(base_range, samples);
    }

    #[test]
    fn multiple() {
        let base_range = v("<1 || 3 - 4");

        let samples = vec![("0.5 - 3.5.0", Some(">=0.5.0 <1.0.0||>=3.0.0 <=3.5.0"))];

        assert_ranges_match(base_range, samples);
    }

    fn assert_ranges_match(base: Range, samples: Vec<(&'static str, Option<&'static str>)>) {
        for (other, expected) in samples {
            let other = v(other);
            let resulting_range = base.intersect(&other).map(|v| v.to_string());
            assert_eq!(
                resulting_range.clone(),
                expected.map(std::string::ToString::to_string),
                "{} ∩ {} := {}",
                base,
                other,
                resulting_range.unwrap_or_else(|| "⊗".into())
            );
        }
    }
}

#[cfg(test)]
mod difference {
    use super::*;

    fn v(range: &'static str) -> Range {
        range.parse().unwrap()
    }

    #[test]
    fn gt_eq_123() {
        let base_range = v(">=1.2.3");

        let samples = vec![
            ("<=2.0.0", Some(">2.0.0")),
            ("<2.0.0", Some(">=2.0.0")),
            (">=2.0.0", Some(">=1.2.3 <2.0.0")),
            (">2.0.0", Some(">=1.2.3 <=2.0.0")),
            (">1.0.0", None),
            (">1.2.3", Some("1.2.3")),
            ("<=1.2.3", Some(">1.2.3")),
            ("1.1.1", Some(">=1.2.3")),
            ("<1.0.0", Some(">=1.2.3")),
            ("2.0.0", Some(">=1.2.3 <2.0.0||>2.0.0")),
        ];

        assert_ranges_match(base_range, samples);
    }

    #[test]
    fn gt_123() {
        let base_range = v(">1.2.3");

        let samples = vec![
            ("<=2.0.0", Some(">2.0.0")),
            ("<2.0.0", Some(">=2.0.0")),
            (">=2.0.0", Some(">1.2.3 <2.0.0")),
            (">2.0.0", Some(">1.2.3 <=2.0.0")),
            (">1.0.0", None),
            (">1.2.3", None),
            ("<=1.2.3", Some(">1.2.3")),
            ("1.1.1", Some(">1.2.3")),
            ("<1.0.0", Some(">1.2.3")),
            ("2.0.0", Some(">1.2.3 <2.0.0||>2.0.0")),
        ];

        assert_ranges_match(base_range, samples);
    }

    #[test]
    fn eq_123() {
        let base_range = v("1.2.3");

        let samples = vec![
            ("<=2.0.0", None),
            ("<2.0.0", None),
            (">=2.0.0", Some("1.2.3")),
            (">2.0.0", Some("1.2.3")),
            (">1.0.0", None),
            (">1.2.3", Some("1.2.3")),
            ("1.2.3", None),
            ("<=1.2.3", None),
            ("1.1.1", Some("1.2.3")),
            ("<1.0.0", Some("1.2.3")),
            ("2.0.0", Some("1.2.3")),
        ];

        assert_ranges_match(base_range, samples);
    }

    #[test]
    fn lt_123() {
        let base_range = v("<1.2.3");

        let samples = vec![
            ("<=2.0.0", None),
            ("<2.0.0", None),
            (">=2.0.0", Some("<1.2.3")),
            (">2.0.0", Some("<1.2.3")),
            (">1.0.0", Some("<=1.0.0")),
            (">1.2.3", Some("<1.2.3")),
            ("<=1.2.3", None),
            ("1.1.1", Some("<1.1.1||>1.1.1 <1.2.3")),
            ("<1.0.0", Some(">=1.0.0 <1.2.3")),
            ("2.0.0", Some("<1.2.3")),
        ];

        assert_ranges_match(base_range, samples);
    }

    #[test]
    fn lt_eq_123() {
        let base_range = v("<=1.2.3");

        let samples = vec![
            ("<=2.0.0", None),
            ("<2.0.0", None),
            (">=2.0.0", Some("<=1.2.3")),
            (">2.0.0", Some("<=1.2.3")),
            (">1.0.0", Some("<=1.0.0")),
            (">1.2.3", Some("<=1.2.3")),
            ("<=1.2.3", None),
            ("1.1.1", Some("<1.1.1||>1.1.1 <=1.2.3")),
            ("<1.0.0", Some(">=1.0.0 <=1.2.3")),
            ("2.0.0", Some("<=1.2.3")),
        ];

        assert_ranges_match(base_range, samples);
    }

    #[test]
    fn multiple() {
        let base_range = v("<1 || 3 - 4");

        let samples = vec![("0.5 - 3.5.0", Some("<0.5.0||>3.5.0 <5.0.0-0"))];

        assert_ranges_match(base_range, samples);
    }

    fn assert_ranges_match(base: Range, samples: Vec<(&'static str, Option<&'static str>)>) {
        for (other, expected) in samples {
            let other = v(other);
            let resulting_range = base.difference(&other).map(|v| v.to_string());
            assert_eq!(
                resulting_range.clone(),
                expected.map(std::string::ToString::to_string),
                "{} \\ {} := {}",
                base,
                other,
                resulting_range.unwrap_or_else(|| "⊗".into())
            );
        }
    }
}

#[cfg(test)]
mod satisfies_ranges_tests {
    use super::*;

    macro_rules! refute {
        ($e:expr) => {
            assert!(!$e)
        };
        ($e:expr, $msg:expr) => {
            assert!(!$e, $msg)
        };
    }

    #[test]
    fn greater_than_equals() {
        let parsed = Range::parse(">=1.2.3").expect("unable to parse");

        refute!(parsed.satisfies(&(0, 2, 3).into()), "major too low");
        refute!(parsed.satisfies(&(1, 1, 3).into()), "minor too low");
        refute!(parsed.satisfies(&(1, 2, 2).into()), "patch too low");
        assert!(parsed.satisfies(&(1, 2, 3).into()), "exact");
        assert!(parsed.satisfies(&(2, 2, 3).into()), "above");
    }

    #[test]
    fn greater_than() {
        let parsed = Range::parse(">1.2.3").expect("unable to parse");

        refute!(parsed.satisfies(&(0, 2, 3).into()), "major too low");
        refute!(parsed.satisfies(&(1, 1, 3).into()), "minor too low");
        refute!(parsed.satisfies(&(1, 2, 2).into()), "patch too low");
        refute!(parsed.satisfies(&(1, 2, 3).into()), "exact");
        assert!(parsed.satisfies(&(1, 2, 4).into()), "above");
    }

    #[test]
    fn exact() {
        let parsed = Range::parse("=1.2.3").expect("unable to parse");

        refute!(parsed.satisfies(&(1, 2, 2).into()), "patch too low");
        assert!(parsed.satisfies(&(1, 2, 3).into()), "exact");
        refute!(parsed.satisfies(&(1, 2, 4).into()), "above");
    }

    #[test]
    fn less_than() {
        let parsed = Range::parse("<1.2.3").expect("unable to parse");

        assert!(parsed.satisfies(&(0, 2, 3).into()), "major below");
        assert!(parsed.satisfies(&(1, 1, 3).into()), "minor below");
        assert!(parsed.satisfies(&(1, 2, 2).into()), "patch below");
        refute!(parsed.satisfies(&(1, 2, 3).into()), "exact");
        refute!(parsed.satisfies(&(1, 2, 4).into()), "above");
    }

    #[test]
    fn less_than_equals() {
        let parsed = Range::parse("<=1.2.3").expect("unable to parse");

        assert!(parsed.satisfies(&(0, 2, 3).into()), "major below");
        assert!(parsed.satisfies(&(1, 1, 3).into()), "minor below");
        assert!(parsed.satisfies(&(1, 2, 2).into()), "patch below");
        assert!(parsed.satisfies(&(1, 2, 3).into()), "exact");
        refute!(parsed.satisfies(&(1, 2, 4).into()), "above");
    }

    #[test]
    fn only_major() {
        let parsed = Range::parse("1").expect("unable to parse");

        refute!(parsed.satisfies(&(0, 2, 3).into()), "major below");
        assert!(parsed.satisfies(&(1, 0, 0).into()), "exact bottom of range");
        assert!(parsed.satisfies(&(1, 2, 2).into()), "middle");
        refute!(parsed.satisfies(&(2, 0, 0).into()), "exact top of range");
        refute!(parsed.satisfies(&(2, 7, 3).into()), "above");
    }

    #[test]
    fn pre_release_version() {
        let range = Range::parse("^2").unwrap();

        refute!(
            range.satisfies(&Version::parse("2.0.0-alpha.0").unwrap()),
            "below"
        );
        refute!(
            range.satisfies(&Version::parse("2.1.0-alpha.0").unwrap()),
            "above but pre-release"
        );
    }

    #[test]
    fn pre_release_range() {
        let range = Range::parse("^1.2.3-rc.4").unwrap();

        refute!(range.satisfies(&Version::parse("1.2.2").unwrap()), "below");
        assert!(
            range.satisfies(&Version::parse("1.2.3").unwrap()),
            "equal non-prerelease"
        );
        assert!(range.satisfies(&Version::parse("1.2.4").unwrap()), "above");
    }

    #[test]
    fn pre_release_version_and_range() {
        let range = Range::parse("^1.2.3-rc.4").unwrap();

        refute!(
            range.satisfies(&Version::parse("1.2.3-rc.3").unwrap()),
            "below"
        );
        assert!(
            range.satisfies(&Version::parse("1.2.3-rc.4").unwrap()),
            "equal"
        );
        assert!(
            range.satisfies(&Version::parse("1.2.3-rc.5").unwrap()),
            "above"
        );
        refute!(
            range.satisfies(&Version::parse("1.2.4-rc.6").unwrap()),
            "above patch but pre-release"
        );
    }
}

/// <https://github.com/npm/node-semver/blob/master/test/fixtures/range-parse.js>
#[cfg(test)]
mod tests {
    use super::*;

    use pretty_assertions::assert_eq;

    macro_rules! range_parse_tests {
        ($($name:ident => $vals:expr),+ ,$(,)?) => {
            $(
                #[test]
                fn $name() {
                    let [input, expected] = $vals;

                    let parsed = Range::parse(input).expect("unable to parse");

                    assert_eq!(expected, parsed.to_string());
                }
            )+
        }

    }

    range_parse_tests![
        //       [input,   parsed and then `to_string`ed]
        exact => ["1.0.0", "1.0.0"],
        major_minor_patch_range => ["1.0.0 - 2.0.0", ">=1.0.0 <=2.0.0"],
        only_major_versions =>  ["1 - 2", ">=1.0.0 <3.0.0-0"],
        only_major_and_minor => ["1.0 - 2.0", ">=1.0.0 <2.1.0-0"],
        mixed_major_minor => ["1.2 - 3.4.5", ">=1.2.0 <=3.4.5"],
        mixed_major_minor_2 => ["1.2.3 - 3.4", ">=1.2.3 <3.5.0-0"],
        minor_minor_range => ["1.2 - 3.4", ">=1.2.0 <3.5.0-0"],
        single_sided_only_major => ["1", ">=1.0.0 <2.0.0-0"],
        single_sided_lower_equals_bound =>  [">=1.0.0", ">=1.0.0"],
        single_sided_lower_equals_bound_2 => [">=0.1.97", ">=0.1.97"],
        single_sided_lower_bound => [">1.0.0", ">1.0.0"],
        single_sided_upper_equals_bound => ["<=2.0.0", "<=2.0.0"],
        single_sided_upper_equals_bound_with_minor => ["<=2.0", "<=2.0.0-0"],
        single_sided_upper_bound => ["<2.0.0", "<2.0.0"],
        major_and_minor => ["2.3", ">=2.3.0 <2.4.0-0"],
        major_dot_x => ["2.x", ">=2.0.0 <3.0.0-0"],
        x_and_asterisk_version => ["2.x.x", ">=2.0.0 <3.0.0-0"],
        patch_x => ["1.2.x", ">=1.2.0 <1.3.0-0"],
        minor_asterisk_patch_asterisk => ["2.*.*", ">=2.0.0 <3.0.0-0"],
        patch_asterisk => ["1.2.*", ">=1.2.0 <1.3.0-0"],
        caret_zero => ["^0", "<1.0.0-0"],
        caret_zero_minor => ["^0.1", ">=0.1.0 <0.2.0-0"],
        caret_one => ["^1.0", ">=1.0.0 <2.0.0-0"],
        caret_minor => ["^1.2", ">=1.2.0 <2.0.0-0"],
        caret_patch => ["^0.0.1", ">=0.0.1 <0.0.2-0"],
        caret_with_patch =>   ["^0.1.2", ">=0.1.2 <0.2.0-0"],
        caret_with_patch_2 => ["^1.2.3", ">=1.2.3 <2.0.0-0"],
        tilde_one => ["~1", ">=1.0.0 <2.0.0-0"],
        tilde_minor => ["~1.0", ">=1.0.0 <1.1.0-0"],
        tilde_minor_2 => ["~2.4", ">=2.4.0 <2.5.0-0"],
        tilde_with_greater_than_patch => ["~>3.2.1", ">=3.2.1 <3.3.0-0"],
        tilde_major_minor_zero => ["~1.1.0", ">=1.1.0 <1.2.0-0"],
        grater_than_equals_one => [">=1", ">=1.0.0"],
        greater_than_one => [">1", ">=2.0.0"],
        less_than_one_dot_two => ["<1.2", "<1.2.0-0"],
        greater_than_one_dot_two => [">1.2", ">=1.3.0"],
        greater_than_with_prerelease => [">1.1.0-beta-10", ">1.1.0-beta-10"],
        either_one_version_or_the_other => ["0.1.20 || 1.2.4", "0.1.20||1.2.4"],
        either_one_version_range_or_another => [">=0.2.3 || <0.0.1", ">=0.2.3||<0.0.1"],
        either_x_version_works => ["1.2.x || 2.x", ">=1.2.0 <1.3.0-0||>=2.0.0 <3.0.0-0"],
        either_asterisk_version_works => ["1.2.* || 2.*", ">=1.2.0 <1.3.0-0||>=2.0.0 <3.0.0-0"],
        one_two_three_or_greater_than_four => ["1.2.3 || >4", "1.2.3||>=5.0.0"],
        any_version_asterisk => ["*", ">=0.0.0"],
        any_version_x => ["x", ">=0.0.0"],
        whitespace_1 => [">= 1.0.0", ">=1.0.0"],
        whitespace_2 => [">=  1.0.0", ">=1.0.0"],
        whitespace_3 => [">=   1.0.0", ">=1.0.0"],
        whitespace_4 => ["> 1.0.0", ">1.0.0"],
        whitespace_5 => [">  1.0.0", ">1.0.0"],
        whitespace_6 => ["<=   2.0.0", "<=2.0.0"],
        whitespace_7 => ["<= 2.0.0", "<=2.0.0"],
        whitespace_8 => ["<=  2.0.0", "<=2.0.0"],
        whitespace_9 => ["<    2.0.0", "<2.0.0"],
        whitespace_10 => ["<\t2.0.0", "<2.0.0"],
        whitespace_11 => ["^ 1", ">=1.0.0 <2.0.0-0"],
        whitespace_12 => ["~> 1", ">=1.0.0 <2.0.0-0"],
        whitespace_13 => ["~ 1.0", ">=1.0.0 <1.1.0-0"],
        beta          => ["^0.0.1-beta", ">=0.0.1-beta <0.0.2-0"],
        beta_tilde => ["~1.2.3-beta", ">=1.2.3-beta <1.3.0-0"],
        beta_4        => ["^1.2.3-beta.4", ">=1.2.3-beta.4 <2.0.0-0"],
        pre_release_on_both => ["1.0.0-alpha - 2.0.0-beta", ">=1.0.0-alpha <=2.0.0-beta"],
        single_sided_lower_bound_with_pre_release => [">1.0.0-alpha", ">1.0.0-alpha"],
        space_separated1 => [">=1.2.3 <4.5.6", ">=1.2.3 <4.5.6"],
        garbage1 => ["1.2.3 foo", "1.2.3"],
        garbage2 => ["foo 1.2.3", "1.2.3"],
        garbage3 => ["~1.y 1.2.3", "1.2.3"],
        garbage4 => ["1.2.3 ~1.y", "1.2.3"],
        loose1 => [">01.02.03", ">1.2.3"],
        loose2 => ["~1.2.3beta", ">=1.2.3-beta <1.3.0-0"],
        caret_weird => ["^ 1.2 ^ 1", ">=1.2.0 <2.0.0-0"],
        loose_eq1 => ["=0.7", ">=0.7.0 <0.8.0-0"],
        loose_eq2 => ["=1", ">=1.0.0 <2.0.0-0"],
        consistent => ["^1.0.1", ">=1.0.1 <2.0.0-0"],
        consistent2 => [">=1.0.1 <2.0.0-0", ">=1.0.1 <2.0.0-0"],
    ];

    // And these weirdos that I don't know what to do with.
    // [">X", "<0.0.0-0"],
    // ["<X", "<0.0.0-0"],
    // ["<x <* || >* 2.x", "<0.0.0-0"],

    #[cfg(feature = "serde")]
    mod serde_tests {
        use serde_derive::{Deserialize, Serialize};

        use super::{BoundSet, Predicate, Range, assert_eq};

        #[derive(Deserialize, Serialize, Eq, PartialEq)]
        struct WithVersionReq {
            req: Range,
        }

        #[test]
        fn read_version_req_from_string() {
            let v: WithVersionReq = serde_json::from_str(r#"{"req":"^1.2.3"}"#).unwrap();

            assert_eq!(v.req, "^1.2.3".parse().unwrap(),);
        }

        #[test]
        fn serialize_a_versionreq_to_string() {
            let output = serde_json::to_string(&WithVersionReq {
                req: Range(vec![
                    BoundSet::at_most(Predicate::Excluding("1.2.3".parse().unwrap())).unwrap(),
                ]),
            })
            .unwrap();
            let expected: String = r#"{"req":"<1.2.3"}"#.into();

            assert_eq!(output, expected);
        }
    }
}

#[cfg(test)]
mod ranges {
    use super::*;

    #[test]
    fn one() {
        let r = BoundSet::new(
            Bound::Lower(Predicate::Including((1, 2, 0).into())),
            Bound::Upper(Predicate::Excluding((3, 3, 4).into())),
        )
        .unwrap();

        assert_eq!(r.to_string(), ">=1.2.0 <3.3.4");
    }
}

// https://github.com/npm/node-semver/blob/main/test/ranges/min-version.js
#[cfg(test)]
mod min_version_tests {
    use super::*;

    #[test]
    fn test() {
        // [range, minimum]
        let tests = vec![
            // Stars
            ("*", Some("0.0.0")),
            ("* || >=2", Some("0.0.0")),
            (">=2 || *", Some("0.0.0")),
            (">2 || *", Some("0.0.0")),
            // equal
            ("1.0.0", Some("1.0.0")),
            ("1.0", Some("1.0.0")),
            ("1.0.x", Some("1.0.0")),
            ("1.0.*", Some("1.0.0")),
            ("1", Some("1.0.0")),
            ("1.x.x", Some("1.0.0")),
            ("1.x.x", Some("1.0.0")),
            ("1.*.x", Some("1.0.0")),
            ("1.x.*", Some("1.0.0")),
            ("1.x", Some("1.0.0")),
            ("1.*", Some("1.0.0")),
            ("=1.0.0", Some("1.0.0")),
            // Tilde
            ("~1.1.1", Some("1.1.1")),
            ("~1.1.1-beta", Some("1.1.1-beta")),
            ("~1.1.1 || >=2", Some("1.1.1")),
            // Carot
            ("^1.1.1", Some("1.1.1")),
            ("^1.1.1-beta", Some("1.1.1-beta")),
            ("^1.1.1 || >=2", Some("1.1.1")),
            ("^2.16.2 ^2.16", Some("2.16.2")),
            // "-" operator
            ("1.1.1 - 1.8.0", Some("1.1.1")),
            ("1.1 - 1.8.0", Some("1.1.0")),
            // Less / less or equal
            ("<2", Some("0.0.0")),
            ("<0.0.0-beta", Some("0.0.0-0")),
            ("<0.0.1-beta", Some("0.0.0")),
            ("<2 || >4", Some("0.0.0")),
            (">4 || <2", Some("0.0.0")),
            ("<=2 || >=4", Some("0.0.0")),
            (">=4 || <=2", Some("0.0.0")),
            ("<0.0.0-beta >0.0.0-alpha", Some("0.0.0-alpha.0")),
            (">0.0.0-alpha <0.0.0-beta", Some("0.0.0-alpha.0")),
            // Greater than or equal
            (">=1.1.1 <2 || >=2.2.2 <3", Some("1.1.1")),
            (">=2.2.2 <3 || >=1.1.1 <2", Some("1.1.1")),
            // Greater than but not equal
            (">1.0.0", Some("1.0.1")),
            (">1.0.0-0", Some("1.0.0-0.0")),
            (">1.0.0-beta", Some("1.0.0-beta.0")),
            (">2 || >1.0.0", Some("1.0.1")),
            (">2 || >1.0.0-0", Some("1.0.0-0.0")),
            (">2 || >1.0.0-beta", Some("1.0.0-beta.0")),
            // Impossible range
            // TODO: this seems to parse as ">=5.0.0||<3.0.0" which is different from node.
            // (">4 <3", None),
        ];

        for (range, version) in tests {
            let parsed_range = Range::parse(range).unwrap();
            let parsed_version = version.map(|v| Version::parse(v).unwrap());
            assert_eq!(
                parsed_range.min_version(),
                parsed_version,
                "expected min_version of {range:?} to be {version:?}"
            );
        }
    }
}
