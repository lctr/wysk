use std::{
    fs,
    path::{Path, PathBuf},
};

pub const FILE_EXT: &'static str = "wy";

type IoResult<X> = Result<X, std::io::Error>;

pub fn ext_str(p: &impl AsRef<Path>) -> Option<&str> {
    p.as_ref().extension().and_then(std::ffi::OsStr::to_str)
}

pub fn is_target_file<P: AsRef<Path>>(p: &P) -> bool {
    wy_common::case!(Some("wy"), ext_str(p))
}

pub fn is_manifest_file() {}

wy_common::newtype! { usize in FileId | Show (+=) }

/// Collection of source file paths which will be visited and
/// lexically/syntactically processed by the front-end. Note that this only
/// collects filepaths in a flat linear fashion, with no information (currently)
/// being stored to provide relationships between the given sources.
///
/// The `Atlas` provides an interface to uniquely enumerate all source files in
/// a program's or project. By default, the `Atlas` will search for all files
/// ending in `.wy` within the current directory (and its ancestors, if any).
///
/// However, it is possible to specify which subdirectories to ignore.
/// Additionally, a project generally contains all of the source files within
/// the `src` subdirectory contained within the directory within which the
/// compiler is run.
#[derive(Clone, Debug)]
pub struct Atlas {
    sources: Vec<Src>,
}

impl Atlas {
    pub fn new() -> Self {
        Self { sources: vec![] }
    }

    /// Shortcut for calling `Atlas::walk_dir` and building an `Atlas` from the
    /// results.
    pub fn try_with_path<P: AsRef<Path>>(p: P) -> IoResult<Self> {
        Self::walk_path(p).map(|pbs| Self {
            sources: pbs
                .into_iter()
                .enumerate()
                .map(|(n, path)| Src {
                    fid: FileId(n),
                    path,
                })
                .collect(),
        })
    }

    /// Returns the length of the inner vector containing all the `Src`
    /// instances. The value returned corresponds to the number of files found
    /// ending in `.wy` within the current directory as well as within ancestor
    /// directories.
    #[inline]
    pub fn len(&self) -> usize {
        self.sources.len()
    }

    #[inline]
    pub fn has(&self, mut f: impl FnMut(&Src) -> bool) -> bool {
        self.find_src(|s| f(*s)).is_some()
    }

    #[inline]
    pub fn has_src_path(&self, path: impl AsRef<Path>) -> bool {
        let p = path.as_ref();
        self.sources_iter().any(|src| src.path() == p)
    }

    pub fn find_src(&self, f: impl FnMut(&&Src) -> bool) -> Option<&Src> {
        self.sources_iter().find(f)
    }

    pub fn new_within_dir(dir: impl AsRef<Path>) -> Result<Self, std::io::Error> {
        let mut atlas = Self::new();
        let paths = Self::walk_path(dir.as_ref())?;
        atlas.add_paths(paths);
        Ok(atlas)
    }

    pub fn add_paths(&mut self, pbs: impl IntoIterator<Item = PathBuf>) {
        for path in pbs {
            let fid = FileId(self.sources.len());
            self.sources.push(Src { fid, path })
        }
    }

    pub fn add_source(&mut self, src: Src) {
        if !self.sources.contains(&src) {
            self.sources.push(Src {
                fid: FileId(self.len()),
                path: src.path,
            })
        }
    }

    pub fn add_sources(&mut self, sources: impl Iterator<Item = Src>) {
        let len = self.len();
        for (n, Src { path, .. }) in sources.enumerate() {
            self.add_source(Src {
                fid: FileId(len + n),
                path,
            })
        }
    }

    #[inline]
    pub fn sources_iter(&self) -> std::slice::Iter<'_, Src> {
        self.sources.iter()
    }

    #[inline]
    pub fn sources_iter_mut(&mut self) -> std::slice::IterMut<'_, Src> {
        self.sources.iter_mut()
    }

    /// Returns a vector containing the paths of **all** files ending in `.wy`
    /// contained within the given directory (and subdirectories). Returns an
    /// error if the given path is invalid.
    pub fn walk_path<P: AsRef<Path>>(p: P) -> IoResult<Vec<PathBuf>> {
        let mut paths = vec![];
        let mut queue: Vec<PathBuf> = vec![PathBuf::from(p.as_ref())];
        while let Some(x) = queue.pop() {
            if x.is_file() {
                if is_target_file(&x) {
                    paths.push(x);
                }
            } else if x.is_dir() {
                for dir in fs::read_dir(x) {
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

    /// Finds all files ending in the `.wy` extension within the current
    /// directory only, limited to one level of file directories -- i.e., only
    /// capturing source files within the given directory and excluding
    /// subdirectories. Returns an error if the given path is invalid.
    pub fn walk_one_level<P: AsRef<Path>>(p: P) -> IoResult<Vec<PathBuf>> {
        fs::read_dir(p.as_ref()).map(|dir| {
            dir.filter_map(|entry| match entry.as_ref().map(fs::DirEntry::path) {
                Ok(e) if e.is_file() && is_target_file(&e) => Some(e),
                _ => None,
            })
            .collect()
        })
    }

    /// Traverses only the `src` subdirectory contained within the given path.
    pub fn walk_src_dir<P: AsRef<Path>>(p: P) -> IoResult<Vec<PathBuf>> {
        Self::walk_path(p.as_ref().join("src/"))
    }

    /// Traverses a given directory and collects files satisfying the given
    /// predicate.
    pub fn walk_if<P: AsRef<Path>>(
        p: P,
        mut predicate: impl FnMut(&PathBuf) -> bool,
    ) -> IoResult<Vec<PathBuf>> {
        fs::read_dir(p.as_ref()).map(|dir| {
            dir.filter_map(|entry| match entry.as_ref().map(fs::DirEntry::path) {
                Ok(path) if predicate(&path) => Some(path),
                _ => None,
            })
            .collect()
        })
    }
}

impl Extend<Src> for Atlas {
    fn extend<T: IntoIterator<Item = Src>>(&mut self, iter: T) {
        self.add_sources(iter.into_iter())
    }
}

impl<S> Extend<S> for Atlas
where
    S: IntoIterator<Item = Src>,
{
    fn extend<T: IntoIterator<Item = S>>(&mut self, iter: T) {
        for sources in iter {
            self.add_sources(sources.into_iter())
        }
    }
}

impl FromIterator<PathBuf> for Atlas {
    fn from_iter<T: IntoIterator<Item = PathBuf>>(iter: T) -> Self {
        Self {
            sources: iter
                .into_iter()
                .enumerate()
                .map(|(n, p)| Src {
                    fid: FileId(n),
                    path: p,
                })
                .collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Src {
    fid: FileId,
    path: PathBuf,
}

impl Src {
    pub fn new<P: AsRef<Path>>(fid: FileId, path: P) -> Self {
        Src {
            fid,
            path: path.as_ref().to_path_buf(),
        }
    }

    /// Creates a new `Src` instance with the `FileId` generated from the
    /// iterator provided
    pub fn new_with<P: AsRef<Path>>(state: &mut impl Iterator<Item = usize>, path: P) -> Self {
        let n = state.next();
        assert!(n.is_some());
        Self::new(FileId(n.unwrap()), path)
    }

    /// Returns the `FileId` generated for this `Src` instance.
    pub fn file_id(&self) -> FileId {
        self.fid
    }

    #[inline]
    pub fn path(&self) -> &Path {
        self.path.as_ref()
    }

    #[inline]
    pub fn is_dir(&self) -> bool {
        self.path.is_dir()
    }

    #[inline]
    pub fn is_file(&self) -> bool {
        self.path.is_file()
    }

    /// Converts a given path-like type `P` implementing `AsRef<Path>` into an
    /// `Option<PathBuf>` based on whether the path is a directory.
    #[inline]
    pub fn some_dir(&self) -> Option<&Path> {
        match self.path() {
            p if p.is_dir() => Some(p),
            _ => None,
        }
    }

    /// Returns an optional list of paths corresponding to the subdirectories
    /// contained within the path found in a `Src` instance's `path` field.
    ///
    /// Note that this only goes a single level deep, i.e., only directories
    /// which are immediate descendants are included.  
    pub fn subdirs(&self) -> Vec<PathBuf> {
        self.some_dir()
            .into_iter()
            .flat_map(|path| {
                path.read_dir()
                    .into_iter()
                    .flat_map(|dir| {
                        Some(dir.filter_map(|entry| entry.ok().as_ref().map(fs::DirEntry::path)))
                    })
                    .flatten()
            })
            .collect()
    }

    pub fn all_subdirs() {}
    /// Transparent wrapper around the `std::fs::read_to_string` method of the
    /// Rust standard library.
    pub fn read_to_string(&self) -> IoResult<String> {
        fs::read_to_string(self.path())
    }
    pub fn is_main(&self) -> bool {
        self.path.ends_with("main.wy")
    }

    /// Returns the canonical (i.e., absolute) form of the path with all
    /// intermediate components normalized and symbolic links resolved.
    ///
    /// To mutably modify the path in place, use `normalize`.
    pub fn canonicalize(&self) -> IoResult<PathBuf> {
        self.path.canonicalize()
    }

    /// Attempts to update the `path` field with the `PathBuf` returned from
    /// calling `canonicalize` and returns a boolean value indicating whether
    /// such an attempt was successful.
    pub fn normalize(&mut self) -> bool {
        if let Ok(p) = self.canonicalize() {
            self.path = p;
            true
        } else {
            false
        }
    }
    /// Transparent wrapper over the `components` method from the `std::path`
    /// module of the Rust standard library.
    pub fn components(&self) -> std::path::Components {
        self.path.components()
    }
}

impl AsRef<Path> for Src {
    fn as_ref(&self) -> &Path {
        self.path()
    }
}

impl std::fmt::Display for Src {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}[{}]", self.fid, self.path().display())
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
