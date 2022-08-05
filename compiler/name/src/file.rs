use std::{fmt, path::PathBuf};

use serde::{Deserialize, Serialize};
use wy_intern::Symbol;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct FileName(Symbol);

impl fmt::Debug for FileName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FileName({})", &self.0)
    }
}

impl fmt::Display for FileName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.0)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum FilePath {
    Stdin,
    File { path: PathBuf, depth: usize },
}

impl FilePath {
    pub fn file_text(&self) -> Option<String> {
        match self {
            FilePath::Stdin => None,
            FilePath::File { path, .. } => std::fs::read_to_string(path).ok(),
        }
    }

    pub fn qualified_name(&self) -> Option<String> {
        match self {
            FilePath::Stdin => None,
            FilePath::File { path, depth } => path.canonicalize().ok().map(|p| {
                use wy_common::text::capitalize_first;
                let mut parts = vec![];
                let mut depth = *depth;
                let mut path = p.components().rev();
                while depth > 0 {
                    let o = path.next().and_then(|c| c.as_os_str().to_str());
                    if !matches!(&o, &Some("src")) {
                        depth -= 1;
                        parts.extend(o);
                    }
                }
                parts.into_iter().rfold(String::new(), |mut a, c| {
                    if !a.is_empty() {
                        a.push('.');
                    }
                    a.push_str(&*capitalize_first(if c.ends_with(".wy") {
                        &c[0..c.len() - 3]
                    } else {
                        c
                    }));
                    a
                })
            }),
        }
    }
}

impl std::fmt::Debug for FilePath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Stdin => write!(f, "<stdin>"),
            Self::File { path, .. } => write!(f, "{:?}", path),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_get_file_name() {
        let fp = FilePath::File {
            path: PathBuf::from("../../language/prelude/src/function.wy"),
            depth: 1,
        };
        assert_eq!(Some(String::from("Function")), fp.qualified_name())
    }
}
