use std::{
    env,
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
};

use wy_common::iter::Counter;
use wy_failure::{Failure, Outcome};

use crate::manifest::Manifest;

pub const PRELUDE_PATH: &'static str = "../../language";

pub const WY_FILE_EXT: &'static str = "wy";

type IoResult<X> = Outcome<X, std::io::Error>;

pub fn ext_str(p: &impl AsRef<Path>) -> Option<&str> {
    p.as_ref().extension().and_then(OsStr::to_str)
}

pub fn is_target_file<P: AsRef<Path>>(p: &P) -> bool {
    wy_common::case!(Some(WY_FILE_EXT), ext_str(p))
}

pub fn some_target_entry(entry: fs::DirEntry) -> Option<PathBuf> {
    let path = entry.path();
    if is_target_file(&path) {
        Some(path)
    } else {
        None
    }
}

/// Checks whether the given path corresponds to a manifest file. Accepts
/// files named `manifest.toml` case insensitively.
pub fn is_manifest_file<P: AsRef<Path>>(p: &P) -> bool {
    let path = p.as_ref();
    path.ends_with("Manifest.toml")
        || path.ends_with("manifest.toml")
        || path.ends_with("MANIFEST.toml")
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(usize);

impl std::fmt::Debug for FileId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FileId({})", &self.0)
    }
}

impl std::fmt::Display for FileId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FileId({})", &self.0)
    }
}

impl From<&mut Counter> for FileId {
    fn from(counter: &mut Counter) -> Self {
        Self(counter.incremented())
    }
}

wy_common::newtype! {
    /// Manifest files are uniquely identified via their enumerated `MetaId`s.
    /// While a project has a single manifest file, projects containing other
    /// projects may contain their own manifest files, hence the need to
    /// enumerate them.
    usize in MetaId | Show (+=)
}

impl From<&mut Counter> for MetaId {
    fn from(counter: &mut Counter) -> Self {
        Self(counter.incremented())
    }
}

/// Will generate an `Atlas` given a path, but unlike the standard methods in
/// creating an `Atlas`, this function will *only* look at files contained
/// within the immediate descendant `src` directory.
pub fn new_sources(p: impl AsRef<Path>) -> Option<Atlas> {
    let p = p.as_ref();
    let path = if p.ends_with("src") {
        p.to_path_buf()
    } else {
        p.join("src")
    };
    if p.exists() {
        Atlas::new_within_dir(path).ok()
    } else {
        None
    }
}

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

impl<I: IntoIterator<Item = PathBuf>> From<(&mut Counter, I)> for Atlas {
    fn from((ct, iter): (&mut Counter, I)) -> Self {
        Self {
            sources: ct
                .zip(iter)
                .map(|(n, path)| Src {
                    fid: FileId(n),
                    path,
                })
                .collect(),
        }
    }
}

impl Atlas {
    pub fn new() -> Self {
        Self { sources: vec![] }
    }

    pub fn with_prelude() -> IoResult<Self> {
        Self::new_within_dir(PRELUDE_PATH)
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

    pub fn new_within_dir(dir: impl AsRef<Path>) -> IoResult<Self> {
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

    pub fn add_dir(&mut self, dir: Dir) {
        self.extend(dir.all_wysk_files())
    }

    pub fn add_dirs(&mut self, dirs: impl IntoIterator<Item = Dir>) {
        dirs.into_iter()
            .for_each(|dir| self.extend(dir.all_wysk_files()))
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

    pub fn sources(&self) -> &[Src] {
        self.sources.as_slice()
    }

    #[inline]
    pub fn sources_iter(&self) -> std::slice::Iter<'_, Src> {
        self.sources.iter()
    }

    #[inline]
    pub fn sources_iter_mut(&mut self) -> std::slice::IterMut<'_, Src> {
        self.sources.iter_mut()
    }

    pub fn walk_dir(dir: Dir) -> Self {
        Self::walk_path(dir.path()).into_iter().flatten().collect()
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
        fs::read_dir(p.as_ref())
            .map(|dir| {
                dir.filter_map(|entry| match entry.as_ref().map(fs::DirEntry::path) {
                    Ok(e) if e.is_file() && is_target_file(&e) => Some(e),
                    _ => None,
                })
                .collect()
            })
            .map_err(|e| Failure::Io(e))
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
        fs::read_dir(p.as_ref())
            .map(|dir| {
                dir.filter_map(|entry| match entry.as_ref().map(fs::DirEntry::path) {
                    Ok(path) if predicate(&path) => Some(path),
                    _ => None,
                })
                .collect()
            })
            .map_err(|e| Failure::Io(e))
    }
}

impl std::ops::Index<FileId> for Atlas {
    type Output = Src;

    fn index(&self, index: FileId) -> &Self::Output {
        &self.sources[index.0]
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

impl FromIterator<Src> for Atlas {
    fn from_iter<T: IntoIterator<Item = Src>>(iter: T) -> Self {
        Atlas {
            sources: iter.into_iter().collect(),
        }
    }
}

/// `Src` describes a filepath ending in the extension `.wy`, and hence cannot
/// be directly created. Instead, file system traversing helpers -- in `Atlas`
/// and `Dir` -- are used to generate `Src` instances. This helps prevent
/// non-wysk source files from inadvertently being included in the `Atlas` file
/// tree, etc.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Src {
    fid: FileId,
    path: PathBuf,
}

impl Src {
    pub const MAIN_PATH: &'static str = "main.wy";
    pub const LIB_PATH: &'static str = "lib.wy";
    pub const MOD_PATH: &'static str = "mod.wy";

    /// Returns the `FileId` generated for this `Src` instance.
    pub fn file_id(&self) -> FileId {
        self.fid
    }

    pub fn file_name(&self) -> &str {
        // safe to unwrap since *all* `Src` instances **must** end in the
        // file-extension `.wy`.
        self.path().file_name().and_then(|s| s.to_str()).unwrap()
    }

    /// Checks whether the first character of the file's name begins with an
    /// ascii alphabetic character
    pub fn name_is_valid(&self) -> bool {
        self.file_name()
            .starts_with(|c: char| c.is_ascii_alphabetic())
    }

    /// Returns a string corresponding to the file's name with the first letter
    /// capitalized. If the first letter of the filename is not able to be
    /// capitalized, `None` is returned.
    pub fn capitalize_init(&self) -> Option<String> {
        let mut valid = false;
        let name = self
            .file_name()
            .char_indices()
            .map(|(n, c)| {
                if n == 0 && c.is_ascii_alphabetic() {
                    valid = true;
                    c.to_ascii_uppercase()
                } else {
                    c
                }
            })
            .collect::<String>();
        if valid {
            Some(name)
        } else {
            None
        }
    }

    /// Identifies whether this file has a sibling with a name differing only by
    /// the case of the first letter. This check exists because all module names
    /// must begin with a capital letter, thus for example the two sibling files
    /// `foo.wy` and `Foo.wy` would normalize to a module name of `Foo` and
    /// hence have are ambiguously named.
    ///
    /// Note that this method will perform an IO search for files within the
    /// same directory. Additionally, this is not necessary for filesystems with
    /// case-insensitive filenames.
    pub fn ambiguous_sibling(&self) -> bool {
        let ext = self.path.extension();
        let mine = self.file_name();
        let len = mine.len();
        let init = mine.chars().next().unwrap();
        if let Some(pn) = self.path.parent() {
            for rd in fs::read_dir(pn) {
                for der in rd {
                    if let Ok(de) = der {
                        let their = de.path();
                        if is_target_file(&their) {
                            match their.file_name().and_then(|s| s.to_str()).map(|s| {
                                let c0 = s.chars().next().unwrap();
                                their.extension() == ext
                                    && s.len() == len
                                    && init == c0
                                    && &mine[1..] == &s[1..]
                            }) {
                                Some(true) => return true,
                                _ => (),
                            }
                        }
                    }
                }
            }
        }
        false
    }

    #[inline]
    pub fn path(&self) -> &Path {
        self.path.as_ref()
    }

    /// Returns the name of the parent folder
    pub fn parent_name(&self) -> Option<&str> {
        self.path()
            .parent()
            .and_then(|p| p.file_name().and_then(|s| s.to_str()))
    }

    /// Returns the parent directory.
    pub fn parent_dir(&self) -> Dir {
        let p = self
            .canonicalize()
            .ok()
            .and_then(|p| p.parent().map(Path::to_path_buf))
            .unwrap_or_else(|| PathBuf::from("."));
        Dir::new(0, p)
    }

    /// Converts a given path-like type `P` implementing `AsRef<Path>` into an
    /// `Option<PathBuf>` based on whether the path is a directory.
    #[inline]
    fn some_dir_path(&self) -> Option<&Path> {
        match self.path() {
            p if p.is_dir() => Some(p),
            _ => None,
        }
    }

    /// Returns a list of paths corresponding to all the subdirectories
    /// recursively found within the `path` field.
    pub fn siblings(&self) -> Vec<PathBuf> {
        self.some_dir_path()
            .and_then(|p| p.parent())
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

    /// Transparent wrapper around the `std::fs::read_to_string` method of the
    /// Rust standard library.
    pub fn read_to_string(&self) -> IoResult<String> {
        fs::read_to_string(self.path()).map_err(|e| Failure::Io(e))
    }

    #[inline]
    pub fn is_main(&self) -> bool {
        self.path.ends_with(Self::MAIN_PATH)
    }

    #[inline]
    pub fn is_lib(&self) -> bool {
        self.path.ends_with(Self::LIB_PATH)
    }

    /// Returns the canonical (i.e., absolute) form of the path with all
    /// intermediate components normalized and symbolic links resolved.
    ///
    /// To mutably modify the path in place, use `normalize`.
    pub fn canonicalize(&self) -> IoResult<PathBuf> {
        self.path.canonicalize().map_err(|e| Failure::Io(e))
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

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Dir {
    depth: usize,
    path: PathBuf,
}

impl AsRef<Path> for Dir {
    fn as_ref(&self) -> &Path {
        self.path.as_path()
    }
}

impl Dir {
    pub const SRC_DIR: &'static str = "src";

    pub fn new(depth: usize, path: impl AsRef<Path>) -> Self {
        let mut dir = Self {
            depth,
            path: path.as_ref().to_path_buf(),
        };
        dir.normalize();
        dir
    }

    /// Transparent wrapper around `std::env::current_dir()` with a depth of
    /// `0`.
    #[inline]
    pub fn current_dir() -> IoResult<Self> {
        env::current_dir()
            .and_then(|pb| pb.canonicalize().map(|pb| Dir::new(0, pb)))
            .map_err(|e| Failure::Io(e))
    }

    #[inline]
    pub fn path(&self) -> &Path {
        self.path.as_path()
    }

    /// Returns the relative number of directories between this directory and
    /// the "root" directory, where *root* directory here refers not to that of
    /// the OS but rather to the oldest `Dir` ancestor from which this `Dir` was
    /// formed.
    #[inline]
    pub fn depth(&self) -> usize {
        self.depth
    }

    pub fn is_src_dir(&self) -> bool {
        self.path.ends_with(Self::SRC_DIR)
    }

    pub fn has_manifest(&self) -> bool {
        self.path.join(Manifest::FILENAME).exists()
    }

    pub fn read_manifest(&self) -> Option<Manifest> {
        Manifest::from_path(self.path.join(Manifest::FILENAME))
    }

    pub fn has_src_dir(&self) -> bool {
        self.path.join(Self::SRC_DIR).exists()
    }

    /// Returns an iterator of immediate descendant `Src` files.
    pub fn imm_wysk_files(&self) -> impl Iterator<Item = Src> + '_ {
        self.path.read_dir().into_iter().flat_map(|rd| {
            rd.filter_map(|res| {
                res.ok().map(|de| {
                    let path = de.path();
                    if is_target_file(&path) {
                        Some(path)
                    } else {
                        None
                    }
                })
            })
            .flatten()
            .enumerate()
            .map(|(n, path)| Src {
                fid: FileId(n),
                path,
            })
        })
    }

    /// Recursively searches all children of this directory and returns an
    /// iterator containing `Src` instances.
    pub fn all_wysk_files(&self) -> impl Iterator<Item = Src> + '_ {
        self.all_sub_dirs()
            .into_iter()
            .flat_map(move |dir| dir.imm_wysk_files().collect::<Vec<_>>())
            .enumerate()
            .map(|(n, Src { path, .. })| Src {
                fid: FileId(n),
                path,
            })
    }

    #[inline]
    /// Returns the canonical (i.e., absolute) form of the path with all
    /// intermediate components normalized and symbolic links resolved.
    ///
    /// To mutably modify the path in place, use `normalize`.
    pub fn canonicalize(&self) -> IoResult<PathBuf> {
        self.path.canonicalize().map_err(|e| Failure::Io(e))
    }

    #[inline]
    /// Attempts to update the `path` field with the `PathBuf` returned from
    /// calling `canonicalize` and returns the difference in component size from
    /// canonicalization. If canonicalization failed, then `None` is returned.
    pub fn normalize(&mut self) -> Option<usize> {
        let old = self.path.components().count();
        if let Ok(p) = self.canonicalize() {
            self.path = p;
            Some(self.path.components().count() - old)
        } else {
            None
        }
    }

    #[inline]
    pub fn is_root(&self) -> bool {
        self.depth == 0
    }

    #[inline]
    /// Transparent wrapper over the `components` method from the `std::path`
    /// module of the Rust standard library.
    pub fn components(&self) -> std::path::Components {
        self.path.components()
    }

    /// Returns an iterator of `Dir`s corresponding to immediate descendant
    /// directories. Since the directories returned are immediate descendants of
    /// `Self`, it follows that all returned directories have a `depth` of
    /// `self.depth + 1`.
    pub fn imm_sub_dirs(&self) -> impl Iterator<Item = Dir> + '_ {
        self.path
            .read_dir()
            .into_iter()
            .map(|rd| {
                rd.filter_map(|de| {
                    de.ok()
                        .and_then(|de| {
                            let p = de.path();
                            if p.is_dir() {
                                Some(p)
                            } else {
                                None
                            }
                        })
                        .map(|path| Dir::new(self.depth + 1, path))
                })
            })
            .flatten()
    }

    /// Returns a list of `Dir`s corresponding to all the subdirectories
    /// recursively found within the `path` field.
    pub fn all_sub_dirs(&self) -> Vec<Self> {
        let mut depth = self.depth + 1;
        let mut dirs = vec![];
        let mut des = vec![];
        let mut paths = vec![];
        let reader = |p: &Path, des: &mut Vec<fs::DirEntry>| {
            if let Ok(rd) = p.read_dir() {
                rd.for_each(|res| {
                    if let Ok(de) = res {
                        des.push(de);
                    }
                })
            };
        };
        reader(self.path.as_path(), &mut des);
        loop {
            if des.is_empty() && paths.is_empty() {
                break;
            }
            while let Some(e) = des.pop() {
                let path = e.path();
                if path.is_dir() {
                    paths.push(path);
                }
            }
            depth += 1;
            while let Some(path) = paths.pop() {
                reader(path.as_path(), &mut des);
                dirs.push(Dir::new(depth, path))
            }
        }
        dirs
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

    #[test]
    fn test_subdirs() {
        let root = Dir {
            depth: 0,
            path: PathBuf::from("../../language"),
        };
        let subdirs = root.all_sub_dirs();
        println!("subdirectories: {:#?}", &subdirs);
        assert!(subdirs[2].is_src_dir());
        println!("{:?}", root.imm_wysk_files().collect::<Vec<_>>());
        println!("all {:?}", root.all_wysk_files().collect::<Vec<_>>());
    }
}
