#![doc = include_str!("../README.md")]

use std::cmp::{self, Ordering};
use std::fmt;
#[cfg(not(feature = "miette"))]
use std::marker::PhantomData;

use error::{SemverError, SemverErrorKind, SemverParseError};

use nom::branch::alt;
use nom::bytes::complete::{tag, take_while1};
use nom::character::complete::{digit1, space0};
use nom::combinator::{all_consuming, map, map_res, opt, recognize};
use nom::error::context;
use nom::multi::separated_list1;
use nom::sequence::preceded;
use nom::{AsChar, Err, IResult, Parser};

pub use range::*;

mod serde;

mod error;

mod range;

/// JavaScript's
/// [MAX_SAFE_INTEGER](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number/MAX_SAFE_INTEGER).
/// This is used to determine the maximum value for integer components in a
/// JS-compatible way.
pub const MAX_SAFE_INTEGER: u64 = 9_007_199_254_740_991;

/// Maximum length of a semver string.
pub const MAX_LENGTH: usize = 256;

/// An Identifier type for build and prerelease metadata.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Identifier {
    /// An identifier that's solely numbers.
    Numeric(u64),
    /// An identifier with letters and numbers.
    AlphaNumeric(String),
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Numeric(n) => write!(f, "{n}"),
            Self::AlphaNumeric(s) => write!(f, "{s}"),
        }
    }
}

/// A semantic version, conformant to the [semver spec](https://semver.org/spec/v2.0.0.html).
#[derive(Clone, Debug)]
pub struct Version {
    pub major: u64,
    pub minor: u64,
    pub patch: u64,
    pub build: Vec<Identifier>,
    pub pre_release: Vec<Identifier>,
}

impl Version {
    /// Create a [Version] with a major, minor, and patch version.
    pub const fn new(major: u64, minor: u64, patch: u64) -> Self {
        Self {
            major,
            minor,
            patch,
            build: Vec::new(),
            pre_release: Vec::new(),
        }
    }

    #[must_use]
    /// Create a [Version] with a major, minor, and patch version.
    pub const fn new(major: u64, minor: u64, patch: u64) -> Self {
        Self {
            major,
            minor,
            patch,
            build: Vec::new(),
            pre_release: Vec::new(),
        }
    }

    /// True if this [Version] satisfies the given [Range].
    #[must_use]
    pub fn satisfies(&self, range: &Range) -> bool {
        range.satisfies(self)
    }

    /// True is this [Version] has a prerelease component.
    #[must_use]
    pub fn is_prerelease(&self) -> bool {
        !self.pre_release.is_empty()
    }

    /// Parse a semver string into a [Version].
    ///
    /// # Errors
    /// If the input is longer than [`MAX_LENGTH`], or if the input is incomplete.
    pub fn parse<S: AsRef<str>>(input: S) -> Result<Self, SemverError> {
        let input = input.as_ref();

        if input.len() > MAX_LENGTH {
            return Err(SemverError {
                input: input.into(),
                #[cfg(feature = "miette")]
                span: (input.len() - 1, 0).into(),
                kind: SemverErrorKind::MaxLengthError,
            });
        }

        match all_consuming(version).parse(input) {
            Ok((_, arg)) => Ok(arg),
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
}

impl PartialEq for Version {
    fn eq(&self, other: &Self) -> bool {
        self.major == other.major
            && self.minor == other.minor
            && self.patch == other.patch
            && self.pre_release == other.pre_release
    }
}

impl Eq for Version {}

impl std::hash::Hash for Version {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.major.hash(state);
        self.minor.hash(state);
        self.patch.hash(state);
        self.pre_release.hash(state);
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)?;

        for (i, ident) in self.pre_release.iter().enumerate() {
            if i == 0 {
                write!(f, "-")?;
            } else {
                write!(f, ".")?;
            }
            write!(f, "{ident}")?;
        }

        for (i, ident) in self.build.iter().enumerate() {
            if i == 0 {
                write!(f, "+")?;
            } else {
                write!(f, ".")?;
            }
            write!(f, "{ident}")?;
        }

        Ok(())
    }
}

impl std::convert::From<(u64, u64, u64)> for Version {
    fn from((major, minor, patch): (u64, u64, u64)) -> Self {
        Self {
            major,
            minor,
            patch,
            build: Vec::new(),
            pre_release: Vec::new(),
        }
    }
}

impl std::str::FromStr for Version {
    type Err = SemverError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl std::convert::From<(u64, u64, u64, u64)> for Version {
    fn from((major, minor, patch, pre_release): (u64, u64, u64, u64)) -> Self {
        Self {
            major,
            minor,
            patch,
            build: Vec::new(),
            pre_release: vec![Identifier::Numeric(pre_release)],
        }
    }
}

impl cmp::PartialOrd for Version {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl cmp::Ord for Version {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        match self.major.cmp(&other.major) {
            Ordering::Equal => {}
            //if difference in major version, just return result
            order_result => return order_result,
        }

        match self.minor.cmp(&other.minor) {
            Ordering::Equal => {}
            //if difference in minor version, just return result
            order_result => return order_result,
        }

        match self.patch.cmp(&other.patch) {
            Ordering::Equal => {}
            //if difference in patch version, just return result
            order_result => return order_result,
        }

        match (self.pre_release.len(), other.pre_release.len()) {
            //if no pre_release string, they're equal
            (0, 0) => Ordering::Equal,
            //if other has a pre-release string, but this doesn't, this one is greater
            (0, _) => Ordering::Greater,
            //if this one has a pre-release string, but other doesn't this one is less than
            (_, 0) => Ordering::Less,
            // if both have pre_release strings, compare the strings and return the result
            (_, _) => self.pre_release.cmp(&other.pre_release),
        }
    }
}

enum Extras {
    Build(Vec<Identifier>),
    Release(Vec<Identifier>),
    ReleaseAndBuild((Vec<Identifier>, Vec<Identifier>)),
}

impl Extras {
    fn values(self) -> (Vec<Identifier>, Vec<Identifier>) {
        use Extras::{Build, Release, ReleaseAndBuild};
        match self {
            Release(ident) => (ident, Vec::new()),
            Build(ident) => (Vec::new(), ident),
            ReleaseAndBuild(ident) => ident,
        }
    }
}

/// <valid semver> ::= <version core>
///                 | <version core> "-" <pre-release>
///                 | <version core> "+" <build>
///                 | <version core> "-" <pre-release> "+" <build>
fn version(input: &str) -> IResult<&str, Version, SemverParseError<&str>> {
    context(
        "version",
        map(
            (opt(alt((tag("v"), tag("V")))), space0, version_core, extras),
            |(_, _, (major, minor, patch), (pre_release, build))| Version {
                major,
                minor,
                patch,
                build,
                pre_release,
            },
        ),
    )
    .parse(input)
}

fn extras(
    input: &str,
) -> IResult<&str, (Vec<Identifier>, Vec<Identifier>), SemverParseError<&str>> {
    map(
        opt(alt((
            map((pre_release, build), Extras::ReleaseAndBuild),
            map(pre_release, Extras::Release),
            map(build, Extras::Build),
        ))),
        |extras| extras.map_or_else(Default::default, Extras::values),
    )
    .parse(input)
}

/// <version core> ::= <major> "." <minor> "." <patch>
fn version_core(input: &str) -> IResult<&str, (u64, u64, u64), SemverParseError<&str>> {
    context(
        "version core",
        map(
            (number, tag("."), number, tag("."), number),
            |(major, _, minor, _, patch)| (major, minor, patch),
        ),
    )
    .parse(input)
}

// I believe build, pre_release, and identifier are not 100% spec compliant.
fn build(input: &str) -> IResult<&str, Vec<Identifier>, SemverParseError<&str>> {
    context(
        "build version",
        preceded(tag("+"), separated_list1(tag("."), identifier)),
    )
    .parse(input)
}

fn pre_release(input: &str) -> IResult<&str, Vec<Identifier>, SemverParseError<&str>> {
    context(
        "pre_release version",
        preceded(opt(tag("-")), separated_list1(tag("."), identifier)),
    )
    .parse(input)
}

fn identifier(input: &str) -> IResult<&str, Identifier, SemverParseError<&str>> {
    context(
        "identifier",
        map(
            take_while1(|x: char| (x as u8).is_alphanum() || x == '-'),
            |s: &str| {
                str::parse::<u64>(s).map_or_else(
                    |_err| Identifier::AlphaNumeric(s.to_string()),
                    Identifier::Numeric,
                )
            },
        ),
    )
    .parse(input)
}

pub(crate) fn number(input: &str) -> IResult<&str, u64, SemverParseError<&str>> {
    context(
        "number component",
        map_res(recognize(digit1), |raw| {
            let value = str::parse(raw).map_err(|e| SemverParseError {
                #[cfg(feature = "miette")]
                input,
                context: None,
                kind: Some(SemverErrorKind::ParseIntError(e)),
                #[cfg(not(feature = "miette"))]
                _phantom: PhantomData,
            })?;

            if value > MAX_SAFE_INTEGER {
                return Err(SemverParseError {
                    #[cfg(feature = "miette")]
                    input,
                    context: None,
                    kind: Some(SemverErrorKind::MaxIntError(value)),
                    #[cfg(not(feature = "miette"))]
                    _phantom: PhantomData,
                });
            }

            Ok(value)
        }),
    )
    .parse(input)
}

#[cfg(test)]
mod tests {
    use super::Identifier::*;
    use super::*;

    use pretty_assertions::assert_eq;

    #[test]
    fn trivial_version_number() {
        let v = Version::parse("1.2.34").unwrap();

        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 2,
                patch: 34,
                build: Vec::new(),
                pre_release: Vec::new(),
            }
        );
    }

    #[test]
    fn version_with_build() {
        let v = Version::parse("1.2.34+123.456").unwrap();

        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 2,
                patch: 34,
                build: vec![Numeric(123), Numeric(456)],
                pre_release: Vec::new(),
            }
        );
    }

    #[test]
    fn version_with_pre_release() {
        let v = Version::parse("1.2.34-abc.123").unwrap();

        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 2,
                patch: 34,
                pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
                build: Vec::new(),
            }
        );
    }

    #[test]
    fn version_with_pre_release_and_build() {
        let v = Version::parse("1.2.34-abc.123+1").unwrap();

        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 2,
                patch: 34,
                pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
                build: vec![Numeric(1),]
            }
        );
    }

    #[test]
    fn pre_release_that_could_look_numeric_at_first() {
        let v = Version::parse("1.0.0-rc.2-migration").unwrap();

        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 0,
                patch: 0,
                pre_release: vec![
                    Identifier::AlphaNumeric("rc".into()),
                    Identifier::AlphaNumeric("2-migration".into())
                ],
                build: vec![],
            }
        );
    }

    #[test]
    fn comparison_with_different_major_version() {
        let lesser_version = Version {
            major: 1,
            minor: 2,
            patch: 34,
            pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
            build: vec![],
        };
        let greater_version = Version {
            major: 2,
            minor: 2,
            patch: 34,
            pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
            build: vec![],
        };
        assert_eq!(lesser_version.cmp(&greater_version), Ordering::Less);
        assert_eq!(greater_version.cmp(&lesser_version), Ordering::Greater);
    }
    #[test]
    fn comparison_with_different_minor_version() {
        let lesser_version = Version {
            major: 1,
            minor: 2,
            patch: 34,
            pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
            build: vec![],
        };
        let greater_version = Version {
            major: 1,
            minor: 3,
            patch: 34,
            pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
            build: vec![],
        };
        assert_eq!(lesser_version.cmp(&greater_version), Ordering::Less);
        assert_eq!(greater_version.cmp(&lesser_version), Ordering::Greater);
    }

    #[test]
    fn comparison_with_different_patch_version() {
        let lesser_version = Version {
            major: 1,
            minor: 2,
            patch: 34,
            pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
            build: vec![],
        };
        let greater_version = Version {
            major: 1,
            minor: 2,
            patch: 56,
            pre_release: vec![AlphaNumeric("abc".into()), Numeric(123)],
            build: vec![],
        };
        assert_eq!(lesser_version.cmp(&greater_version), Ordering::Less);
        assert_eq!(greater_version.cmp(&lesser_version), Ordering::Greater);
    }

    // Confirms the comparison matches the pre-release comparison example in the SemVer spec.
    // ie. checks that 1.0.0-alpha < 1.0.0-alpha.1 < 1.0.0-alpha.beta < 1.0.0-beta < 1.0.0-beta.2 < 1.0.0-beta.11 < 1.0.0-rc.1 < 1.0.0.
    // for simplicity just checks them in order. Assumes that the transitive property holds. So if a < b & b < c then a < c.
    #[test]
    fn comparison_with_different_pre_release_version() {
        let v1_alpha = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("alpha".into())],
            build: vec![],
        };
        let v1_alpha1 = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("alpha".into()), Numeric(1)],
            build: vec![],
        };
        assert_eq!(v1_alpha.cmp(&v1_alpha1), Ordering::Less);
        let v1_alpha_beta = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("alpha".into()), AlphaNumeric("beta".into())],
            build: vec![],
        };
        assert_eq!(v1_alpha1.cmp(&v1_alpha_beta), Ordering::Less);
        let v1_beta = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("beta".into())],
            build: vec![],
        };
        assert_eq!(v1_alpha_beta.cmp(&v1_beta), Ordering::Less);
        let v1_beta2 = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("beta".into()), Numeric(2)],
            build: vec![],
        };
        assert_eq!(v1_beta.cmp(&v1_beta2), Ordering::Less);
        let v1_beta11 = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("beta".into()), Numeric(11)],
            build: vec![],
        };
        assert_eq!(v1_beta2.cmp(&v1_beta11), Ordering::Less);
        let v1_rc1 = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![AlphaNumeric("rc".into()), Numeric(1)],
            build: vec![],
        };
        assert_eq!(v1_beta11.cmp(&v1_rc1), Ordering::Less);
        let v1 = Version {
            major: 1,
            minor: 0,
            patch: 0,
            pre_release: vec![],
            build: vec![],
        };
        assert_eq!(v1_rc1.cmp(&v1), Ordering::Less);
    }

    #[test]
    fn individual_version_component_has_an_upper_bound() {
        let out_of_range = MAX_SAFE_INTEGER + 1;
        let v = Version::parse(format!("1.2.{out_of_range}"));
        assert_eq!(
            v.expect_err("Parse should have failed.").to_string(),
            "Integer component of semver string is larger than JavaScript's Number.MAX_SAFE_INTEGER: 9007199254740992"
        );
    }

    #[test]
    fn version_string_limited_to_256_characters() {
        let prebuild = (0..257).map(|_| "X").collect::<Vec<_>>().join("");
        let version_string = format!("1.1.1-{prebuild}");
        let v = Version::parse(version_string.clone());

        assert_eq!(
            v.expect_err("Parse should have failed").to_string(),
            "Semver string can't be longer than 256 characters."
        );

        let ok_version = version_string[0..255].to_string();
        let v = Version::parse(ok_version);
        assert!(v.is_ok());
    }

    #[test]
    fn version_prefixed_with_v() {
        // TODO: This is part of strict parsing for node-semver!
        let v = Version::parse("v1.2.3").unwrap();
        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 2,
                patch: 3,
                pre_release: vec![],
                build: vec![],
            }
        );
    }

    #[test]
    fn version_prefixed_with_v_space() {
        // TODO: Loose parsing supports this, so
        let v = Version::parse("v 1.2.3").unwrap();
        assert_eq!(
            v,
            Version {
                major: 1,
                minor: 2,
                patch: 3,
                pre_release: vec![],
                build: vec![],
            }
        );
    }

    #[cfg(feature = "serde")]
    mod serde_tests {
        use serde_derive::{Deserialize, Serialize};

        use super::{Identifier, Version};

        #[derive(Deserialize, Serialize, Eq, PartialEq)]
        struct Versioned {
            version: Version,
        }

        #[test]
        fn read_version_from_string() {
            let v: Versioned = serde_json::from_str(r#"{"version":"1.2.34-abc.213+2"}"#).unwrap();

            assert_eq!(
                v.version,
                Version {
                    major: 1,
                    minor: 2,
                    patch: 34,
                    pre_release: vec![
                        Identifier::AlphaNumeric("abc".into()),
                        Identifier::Numeric(213)
                    ],
                    build: vec![Identifier::Numeric(2)],
                }
            );
        }

        #[test]
        fn serialize_a_version_to_string() {
            let output = serde_json::to_string(&Versioned {
                version: Version {
                    major: 1,
                    minor: 2,
                    patch: 34,
                    pre_release: vec![
                        Identifier::AlphaNumeric("abc".into()),
                        Identifier::Numeric(213),
                    ],
                    build: vec![Identifier::Numeric(2)],
                },
            })
            .unwrap();
            let expected: String = r#"{"version":"1.2.34-abc.213+2"}"#.into();

            assert_eq!(output, expected);
        }
    }
}
