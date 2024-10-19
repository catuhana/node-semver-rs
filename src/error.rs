use std::{marker::PhantomData, num::ParseIntError};

use nom::error::{ContextError, ErrorKind, FromExternalError, ParseError};
use thiserror::Error;

use crate::MAX_LENGTH;

/**
Semver version or range parsing error wrapper.

This wrapper is used to hold some parsing-related metadata, as well as
a more specific [`SemverErrorKind`].
*/
#[derive(Debug, Clone, Error, Eq, PartialEq)]
#[error("{kind}")]
pub struct SemverError {
    pub input: String,
    #[cfg(feature = "miette")]
    pub span: SourceSpan,
    pub kind: SemverErrorKind,
}

impl SemverError {
    /// Returns the input that was given to the parser.
    pub fn input(&self) -> &str {
        &self.input
    }

    #[cfg(feature = "miette")]
    /// Returns the SourceSpan of the error.
    pub const fn span(&self) -> &SourceSpan {
        &self.span
    }

    #[cfg(feature = "miette")]
    /// Returns the (0-based) byte offset where the parsing error happened.
    pub const fn offset(&self) -> usize {
        self.span.offset()
    }

    /// Returns the more specific [`SemverErrorKind`] for this error.
    ///
    /// This value can also be fetched through [`std::error::Error::source`],
    /// but that would require downcasting to match types.
    pub const fn kind(&self) -> &SemverErrorKind {
        &self.kind
    }

    #[cfg(feature = "miette")]
    /// Returns the (0-indexed) line and column number where the parsing error
    /// happened.
    pub fn location(&self) -> (usize, usize) {
        // Taken partially from nom.
        let prefix = &self.input.as_bytes()[..self.offset()];

        // Count the number of newlines in the first `offset` bytes of input
        let line_number = bytecount::count(prefix, b'\n');

        // Find the line that includes the subslice:
        // Find the *last* newline before the substring starts
        let line_begin = prefix
            .iter()
            .rev()
            .position(|&b| b == b'\n')
            .map(|pos| self.offset() - pos)
            .unwrap_or(0);

        // Find the full line after that newline
        let line = self.input[line_begin..]
            .lines()
            .next()
            .unwrap_or(&self.input[line_begin..])
            .trim_end();

        // The (0-indexed) column number is the offset of our substring into that line
        let column_number = self.input[self.offset()..].as_ptr() as usize - line.as_ptr() as usize;

        (line_number, column_number)
    }
}

/**
The specific kind of error that occurred. Usually wrapped in a [`SemverError`].
*/
#[derive(Debug, Clone, Error, Eq, PartialEq)]
#[cfg_attr(feature = "miette", derive(Diagnostic))]
pub enum SemverErrorKind {
    /**
    Semver strings overall can't be longer than [`MAX_LENGTH`]. This is a
    restriction coming from the JavaScript `node-semver`.
    */
    #[error("Semver string can't be longer than {} characters.", MAX_LENGTH)]
    #[cfg_attr(
        feature = "miette",
        diagnostic(code(node_semver::too_long), url(docsrs))
    )]
    MaxLengthError,

    /**
    Input to `node-semver` must be "complete". That is, a version must be
    composed of major, minor, and patch segments, with optional prerelease
    and build metadata. If you're looking for alternative syntaxes, like `1.2`,
    that are meant for defining semver ranges, use [Range] instead.
    */
    #[error("Incomplete input to semver parser.")]
    #[cfg_attr(
        feature = "miette",
        diagnostic(code(node_semver::incomplete_input), url(docsrs))
    )]
    IncompleteInput,

    /**
    Components of a semver string (major, minor, patch, integer sections of
    build and prerelease) must all be valid, parseable integers. This error
    occurs when Rust's own integer parsing failed.
    */
    #[error("Failed to parse an integer component of a semver string: {0}")]
    #[cfg_attr(
        feature = "miette",
        diagnostic(code(node_semver::parse_int_error), url(docsrs))
    )]
    ParseIntError(ParseIntError),

    /**
    `node-semver` inherits the JavaScript implementation's limitation on
    limiting integer component sizes to [`MAX_SAFE_INTEGER`].
    */
    #[error("Integer component of semver string is larger than JavaScript's Number.MAX_SAFE_INTEGER: {0}")]
    #[cfg_attr(
        feature = "miette",
        diagnostic(code(node_semver::integer_too_large), url(docsrs))
    )]
    MaxIntError(u64),

    /**
    This is a generic error that a certain component of the semver string
    failed to parse.
    */
    #[error("Failed to parse {0}.")]
    #[cfg_attr(
        feature = "miette",
        diagnostic(code(node_semver::parse_component_error), url(docsrs))
    )]
    Context(&'static str),

    #[error("No valid ranges could be parsed")]
    #[cfg_attr(
        feature = "miette",
        diagnostic(code(node_semver::no_valid_ranges), url(docsrs), help("node-semver parses in so-called 'loose' mode. This means that if you have a slightly incorrect semver operator (`>=1.y`, for ex.), it will get thrown away. This error only happens if _all_ your input ranges were invalid semver in this way."))
    )]
    NoValidRanges,

    /**
    This error is mostly nondescript. Feel free to file an issue if you run
    into it.
    */
    #[error("An unspecified error occurred.")]
    #[cfg_attr(feature = "miette", diagnostic(code(node_semver::other), url(docsrs)))]
    Other,
}

#[cfg(feature = "miette")]
impl Diagnostic for SemverError {
    fn code<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        self.kind().code()
    }

    fn severity(&self) -> Option<miette::Severity> {
        self.kind().severity()
    }

    fn help<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        self.kind().help()
    }

    fn url<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        self.kind().url()
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(&self.input)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        Some(Box::new(std::iter::once(
            miette::LabeledSpan::new_with_span(Some("here".into()), *self.span()),
        )))
    }
}

#[derive(Debug)]
pub struct SemverParseError<I> {
    #[cfg(feature = "miette")]
    pub(crate) input: I,
    pub(crate) context: Option<&'static str>,
    pub(crate) kind: Option<SemverErrorKind>,

    #[cfg(not(feature = "miette"))]
    pub(crate) _phantom: PhantomData<I>,
}

impl<I> ParseError<I> for SemverParseError<I> {
    #[cfg(feature = "miette")]
    fn from_error_kind(input: I, _kind: nom::error::ErrorKind) -> Self {
        Self {
            input,
            context: None,
            kind: None,
        }
    }

    #[cfg(not(feature = "miette"))]
    fn from_error_kind(_input: I, _kind: nom::error::ErrorKind) -> Self {
        Self {
            context: None,
            kind: None,
            _phantom: PhantomData,
        }
    }

    fn append(_input: I, _kind: nom::error::ErrorKind, other: Self) -> Self {
        other
    }
}

impl<I> ContextError<I> for SemverParseError<I> {
    fn add_context(_input: I, ctx: &'static str, mut other: Self) -> Self {
        other.context = Some(ctx);
        other
    }
}

impl<'a> FromExternalError<&'a str, Self> for SemverParseError<&'a str> {
    fn from_external_error(_input: &'a str, _kind: ErrorKind, e: Self) -> Self {
        e
    }
}
