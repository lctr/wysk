//! This library deals with source files and exposes an API used to facilitate
//! bookkeeping of file-related sources.
use std::path::{Path, PathBuf};

pub const FILE_EXT: &'static str = "wy";

type IoResult<X> = Result<X, std::io::Error>;

pub fn ext_str(p: &impl AsRef<Path>) -> Option<&str> {
    p.as_ref().extension().and_then(std::ffi::OsStr::to_str)
}

pub fn is_target_file<P: AsRef<Path>>(p: &P) -> bool {
    wy_common::case!(Some("wy"), ext_str(p))
}

wy_common::newtype! { usize in FileId | Show (+=) }

#[derive(Clone, Debug)]
pub struct Atlas {
    sources: Vec<Src>,
}

impl Atlas {
    pub fn new() -> Self {
        Self { sources: vec![] }
    }

    pub fn new_within_dir(dir: impl AsRef<Path>) -> Result<Self, std::io::Error> {
        let mut atlas = Self::new();
        let paths = Self::walk_path(dir.as_ref())?;
        atlas.add_paths(paths);
        Ok(atlas)
    }

    pub fn add_paths(&mut self, pbs: Vec<PathBuf>) {
        for path in pbs {
            let fid = FileId(self.sources.len());
            self.sources.push(Src { fid, path })
        }
    }

    pub fn sources_iter(&self) -> std::slice::Iter<'_, Src> {
        self.sources.iter()
    }

    pub fn walk_path<P: AsRef<Path>>(p: P) -> IoResult<Vec<PathBuf>> {
        let mut paths = vec![];
        let mut queue: Vec<PathBuf> = vec![PathBuf::from(p.as_ref())];
        while let Some(x) = queue.pop() {
            if x.is_file() {
                if is_target_file(&x) {
                    paths.push(x);
                }
            } else if x.is_dir() {
                for dir in std::fs::read_dir(x) {
                    for entry in dir {
                        let e = entry?.path();
                        if e.is_dir() {
                            queue.push(e);
                        } else if is_target_file(&e) {
                            paths.push(e);
                        }
                    }
                }
            }
        }
        Ok(paths)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Src {
    fid: FileId,
    path: PathBuf,
}

impl Src {
    pub fn new(fid: FileId, path: PathBuf) -> Self {
        Src { fid, path }
    }
    pub fn file_id(&self) -> FileId {
        self.fid
    }
    pub fn path(&self) -> &Path {
        self.path.as_ref()
    }
    pub fn is_dir(&self) -> bool {
        self.path.is_dir()
    }
    pub fn is_file(&self) -> bool {
        self.path.is_file()
    }
    pub fn read_to_string(&self) -> IoResult<String> {
        std::fs::read_to_string(self.path())
    }
    pub fn is_main(&self) -> bool {
        self.path.ends_with("main.wy")
    }
}

impl AsRef<Path> for Src {
    fn as_ref(&self) -> &Path {
        self.path()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn inspect_directory() {
        let target_path = PathBuf::from("../../language");
        let paths = Atlas::walk_path(target_path);
        match paths {
            Ok(ps) => {
                // println!("", )
                println!("cwd: {:?}", std::env::current_dir());
                println!("files found: {}", ps.len());
                println!("paths found: {:?}", &ps);
            }
            Err(e) => {
                println!("{}", e)
            }
        }
    }
}
