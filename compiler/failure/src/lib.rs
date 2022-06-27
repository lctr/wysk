use std::path::Path;

use wy_span::{Coord, Location, Row};

pub type Outcome<X, E> = Result<X, Failure<E>>;

#[derive(Debug)]
pub enum Failure<E> {
    Io(std::io::Error),
    Err(E),
}

pub fn normalize_io_err<E>(error: Failure<std::io::Error>) -> Failure<E> {
    match error {
        Failure::Io(e) | Failure::Err(e) => Failure::Io(e),
    }
}

pub struct It<X>(pub(crate) X);
impl<X> From<X> for It<X> {
    fn from(x: X) -> Self {
        Self(x)
    }
}

impl<X> AsRef<X> for It<X> {
    fn as_ref(&self) -> &X {
        &self.0
    }
}

impl<X> std::ops::Deref for It<X> {
    type Target = X;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<X> std::ops::DerefMut for It<X> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<X: Copy> Copy for It<X> {}

impl<X: Clone> Clone for It<X> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<X: PartialEq> PartialEq for It<X> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<X: Eq> Eq for It<X> {}

impl<X: std::hash::Hash> std::hash::Hash for It<X> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<X: Default> Default for It<X> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<X: std::fmt::Debug> std::fmt::Debug for It<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        X::fmt(&self.0, f)
    }
}

impl<X: std::fmt::Display> std::fmt::Display for It<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        X::fmt(&self.0, f)
    }
}

impl<E> std::fmt::Display for Failure<E>
where
    E: std::error::Error,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Failure::Io(err) => write!(f, "IO error: {}", err),
            Failure::Err(e) => write!(f, "{}", e),
        }
    }
}

impl<E> From<std::io::Error> for Failure<E> {
    fn from(ioerr: std::io::Error) -> Self {
        Failure::Io(ioerr)
    }
}

impl<E> From<Failure<Failure<E>>> for Failure<E> {
    fn from(e: Failure<Failure<E>>) -> Self {
        match e {
            Failure::Io(e) => Failure::Io(e),
            Failure::Err(e) => e,
        }
    }
}

impl<E> std::error::Error for Failure<E> where E: std::error::Error {}

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

//---------- FOR FILE-CONTENT-RELATED STUFF, such as parsing, lexing, etc
/// Describing the source path and position, primarily used in error reporting.
/// This should be included in every error message to be able to reproduce
/// tracking information regarding the source code involved during error
/// reporting.
///
/// This struct should effectively be able to produce a string of the form
/// ```txt
///         [PATH/TO/FILE]:[ROW][COL]
/// ```
/// in error messages.
#[derive(Clone, PartialEq)]
pub struct SrcLoc {
    pub coord: Coord,
    pub pathstr: Option<String>,
}

impl std::fmt::Display for SrcLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref s) = self.pathstr {
            write!(f, "{}", s)
        } else {
            write!(f, "<INTERACTIVE>")
        }?;
        // include only starting coordinates?
        write!(f, ":{}", self.coord)
    }
}

impl std::fmt::Debug for SrcLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // same as `Display`
        write!(f, "{}", self)
    }
}

impl SrcLoc {
    pub fn gutter(&self) -> RowGutter {
        RowGutter(self.coord.row)
    }
}

/// Error printing utility
#[derive(Copy, Clone, PartialEq, PartialOrd)]
pub struct RowGutter(Row);
impl std::fmt::Display for RowGutter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for _ in 0..(4 + self.0.strlen()) {
            char::fmt(&' ', f)?;
        }
        Ok(())
    }
}

pub enum SrcPath<P: AsRef<Path> = String> {
    Direct,
    File(P),
}

impl<P: AsRef<Path>> std::fmt::Display for SrcPath<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SrcPath::Direct => write!(f, "<INTERACTIVE>"),
            SrcPath::File(p) => write!(f, "{}", p.as_ref().display()),
        }
    }
}

pub struct Dialogue {
    path: SrcPath,
    gutter: RowGutter,
    top_msg: String,
    source: String,
    underlined: Location,
    // corners: Location,
}

impl Dialogue {
    pub fn new(srcloc: SrcLoc, top_msg: String, source: String, underlined: Location) -> Self {
        Self {
            gutter: srcloc.gutter(),
            path: if let Some(p) = srcloc.pathstr {
                SrcPath::File(p)
            } else {
                SrcPath::Direct
            },
            top_msg,
            source,
            underlined,
        }
    }
}

impl std::fmt::Display for Dialogue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let gutter = self.gutter;
        writeln!(f, "{}", &self.top_msg)?;
        writeln!(f, "{}=> {}", gutter, &self.path)?;
        writeln!(f, "{}|", gutter)?;
        writeln!(f, " [{}] |", &self.source[self.underlined])?;
        write!(f, "{}|", gutter)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
