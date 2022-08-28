use std::{
    fmt,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use wy_pretty::color::{AsciiColor, StyleBuilder};
use wy_span::{Col, Coord, Row, Span};

const PAD_SPACE: usize = 4;

// Glyphs used in printing
const PIPE: char = '│';
// const FORK: char = '├';
const FOOT: char = '└';
const DASH: char = '─';
const CORNER: char = '┌';
const CARET: char = '^';

#[derive(Clone, Copy, PartialEq, Eq)]
struct Glyphs(&'static [char]);

impl fmt::Display for Glyphs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for c in self.0 {
            write!(f, "{c}")?;
        }
        Ok(())
    }
}

const TOP_LEFT: Glyphs = Glyphs(&[CORNER, DASH]);

struct Repeat<S>(usize, S);

impl<S> fmt::Display for Repeat<S>
where
    S: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut count = self.0;
        let it = &self.1;
        while count > 0 {
            write!(f, "{it}")?;
            count -= 1;
        }
        Ok(())
    }
}

impl<S> fmt::Debug for Repeat<S>
where
    S: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut count = self.0;
        let it = &self.1;
        while count > 0 {
            write!(f, "{it}")?;
            count -= 1;
        }
        Ok(())
    }
}

/// Describing the source path and position, primarily used in error reporting.
/// This should be included in every error message to be able to reproduce
/// tracking information regarding the source code involved during error
/// reporting.
///
/// The error should effectively be able to produce a string of the form
/// ```txt
///         [PATH/TO/FILE]:[ROW][COL]
/// ```
/// in error messages.
// TODO: GENERALIZE TO SHOW MULTIPLE ERRORS
pub struct Dialogue<'s, S: AsRef<str> = String, P: AsRef<Path> = PathBuf> {
    label: &'s str,
    message: String,
    srctext: &'s S,
    srcloc: &'s SrcLoc<P>,
    span: Span,
}

impl<'s, S: AsRef<str>, P: AsRef<Path>> Dialogue<'s, S, P> {
    pub fn new(
        label: &'s str,
        message: String,
        srctext: &'s S,
        srcloc: &'s SrcLoc<P>,
        span: Span,
    ) -> Self {
        Dialogue {
            label,
            message,
            srctext,
            srcloc,
            span,
        }
    }

    pub fn display(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }

    pub fn row_col(&self) -> (Row, Col) {
        let Coord { row, col } = self.srcloc.coord;
        (row, col)
    }

    pub fn gutter(&self) -> RowGutter {
        self.srcloc.gutter()
    }
}

impl Dialogue<'_> {
    pub fn write_bold_red(msg: impl fmt::Display, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        StyleBuilder::new()
            .set_fg_color(AsciiColor::Red)
            .set_bold(true)
            .build(msg)
            .fmt_display(f)
    }
}

impl<'s, S: AsRef<str>, P: AsRef<Path>> fmt::Display for Dialogue<'s, S, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // error label
        let label = StyleBuilder::new()
            .set_bold(true)
            .set_fg_color(AsciiColor::Red)
            .build(self.label);
        let message = StyleBuilder::new().set_bold(true).build(&self.message);

        let srcloc = self.srcloc;
        let (row, col) = self.row_col();
        let gutter = srcloc.gutter();
        // TODO: sometimes the error will be on the beginning of the next line
        // (or end of previous line??) with no line text shown at all.
        // womp. fix.
        let line = &&self.srctext.as_ref().lines()[row - 1usize];
        let trimmed = line.trim();
        // string with whitespace trimmed is *never* longer than the original
        let diff = line.len() - trimmed.len();
        let caretlen = self.span.len();
        let caret_offset = 0; //if caretlen == 1 { 1 } else { (diff + 2) / 2 };
        let dash_len =
            PAD_SPACE - 1 + caret_offset + col.as_usize().saturating_sub(diff.abs_diff(caretlen));
        let midline = Repeat(dash_len, DASH);
        let carets = StyleBuilder::new()
            .set_fg_color(AsciiColor::Red)
            .build(Repeat(caretlen, CARET));

        write!(
            f,
            "{label} {message}\n\
             {gutter}{TOP_LEFT}{srcloc}\n\
             {gutter}{PIPE}\n \
            [{row}]  {PIPE}    `{trimmed}`\n\
             {gutter}{FOOT}{midline}{carets}\n\
            "
        )
    }
}

impl<'s, S: AsRef<str>, P: AsRef<Path>> fmt::Debug for Dialogue<'s, S, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self)
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum SrcPath<P: AsRef<Path> = PathBuf> {
    Direct,
    File(P),
    Short { root: P, file: P },
}

impl<P: AsRef<Path>> SrcPath<P> {
    pub fn is_from_file(&self) -> bool {
        matches!(self, Self::File(_))
    }

    pub fn as_path(&self) -> Option<&Path> {
        match self {
            SrcPath::Direct => None,
            SrcPath::File(p) => Some(p.as_ref()),
            SrcPath::Short { root: _, file } => Some(file.as_ref()),
        }
    }

    pub fn borrowed(&self) -> SrcPath<&P> {
        match self {
            SrcPath::Direct => SrcPath::Direct,
            SrcPath::File(p) => SrcPath::File(p),
            SrcPath::Short { root, file } => SrcPath::Short { root, file },
        }
    }
}

impl<P: Copy + AsRef<Path>> Copy for SrcPath<P> {}

impl<P: AsRef<Path>> Default for SrcPath<P> {
    fn default() -> Self {
        Self::Direct
    }
}

impl<P: AsRef<Path>> fmt::Display for SrcPath<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SrcPath::Direct => write!(f, "<{}>", wy_pretty::color!(fg Red "STDIN")),
            SrcPath::File(p) => write!(f, "{}", p.as_ref().display()),
            SrcPath::Short { root, file } => {
                let root = root.as_ref();
                let file = file.as_ref();
                let root_len = root.components().count().saturating_sub(1);
                let mut fp = file.iter();
                for _ in 0..root_len {
                    fp.next();
                }
                write!(f, "{}", fp.as_path().display())
            }
        }
    }
}

impl<P: AsRef<Path>> PartialEq<&Path> for SrcPath<P> {
    fn eq(&self, other: &&Path) -> bool {
        match (self, other) {
            (Self::File(l0), p) => l0.as_ref() == *p,
            _ => false,
        }
    }
}

impl<P: AsRef<Path>> PartialEq<PathBuf> for SrcPath<P> {
    fn eq(&self, other: &PathBuf) -> bool {
        match (self, other) {
            (Self::File(l0), p) => l0.as_ref() == p.as_path(),
            _ => false,
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct SrcLoc<P: AsRef<Path> = PathBuf> {
    pub coord: Coord,
    pub pathstr: SrcPath<P>,
}

impl<P: AsRef<Path>> fmt::Display for SrcLoc<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // include only starting coordinates?
        write!(f, "{}:{}", &self.pathstr, &self.coord)
    }
}

impl<P: AsRef<Path>> fmt::Debug for SrcLoc<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl<P: AsRef<Path>> SrcLoc<P> {
    pub fn gutter(&self) -> RowGutter {
        RowGutter(self.coord.row)
    }
}

/// Error printing utility
#[derive(Copy, Clone, PartialEq, PartialOrd)]
pub struct RowGutter(Row);
impl fmt::Display for RowGutter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for _ in 0..(PAD_SPACE + self.0.strlen() as usize) {
            char::fmt(&' ', f)?;
        }
        Ok(())
    }
}

#[macro_export]
macro_rules! fails {
    (impl for $ty:ty $(| $val:ty)?) => {
        impl From<$ty> for $crate::Failure<$ty $(, $val)?> {
            fn from(it: $ty) -> Self {
                $crate::Failure::Err(it)
            }
        }
    };
}
