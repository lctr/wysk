use wy_span::{Coord, Location, Row};

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

pub enum SrcPath<P = String> {
    Direct,
    File(P),
}

impl std::fmt::Display for SrcPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
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
    fn new(
        srcloc: SrcLoc,
        top_msg: String,
        source: String,
        underlined: Location,
    ) -> Self {
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
