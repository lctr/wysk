use std::{
    env,
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};

use crate::manifest::Manifest;

pub const PRELUDE_PATH: &'static str = "../../language/prelude";

pub const WY_FILE_EXT: &'static str = "wy";

pub type IoResult<X> = Result<X, std::io::Error>;

pub fn ext_str(p: &Path) -> Option<&str> {
    p.extension().and_then(OsStr::to_str)
}

pub fn is_target_file<P: AsRef<Path>>(p: P) -> bool {
    matches!(ext_str(p.as_ref()), Some(ext) if ext == WY_FILE_EXT)
}

/// Checks whether the given path corresponds to a manifest file. Accepts
/// files named `manifest.toml` case insensitively.
pub fn is_manifest_file(path: &Path) -> bool {
    path.ends_with("Manifest.toml")
        || path.ends_with("manifest.toml")
        || path.ends_with("MANIFEST.toml")
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CfgId(pub(crate) usize);

impl std::fmt::Debug for CfgId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CfgId({})", &self.0)
    }
}

impl std::fmt::Display for CfgId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CfgId({})", &self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CfgPath {
    id: CfgId,
    path: PathBuf,
}

impl CfgPath {
    pub fn id(&self) -> CfgId {
        self.id
    }

    pub fn path(&self) -> &Path {
        self.path.as_path()
    }
}

impl AsRef<Path> for CfgPath {
    fn as_ref(&self) -> &Path {
        self.path.as_path()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct FileId(pub(crate) usize);

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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AtlasItem<'atlas> {
    CfgPath(&'atlas CfgPath),
    FilePath(&'atlas FilePath),
}

impl<'a> AtlasItem<'a> {
    pub fn is_cfgpath(&self) -> bool {
        matches!(self, Self::CfgPath(_))
    }
    pub fn is_filepath(&self) -> bool {
        matches!(self, Self::FilePath(_))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum AtlasItemId {
    CfgId(CfgId),
    FileId(FileId),
}

wy_common::variant_preds! {
    AtlasItemId
    | is_cfg_id => CfgId(_)
    | is_file_id => FileId(_)
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
#[derive(Debug)]
pub struct Atlas {
    filepaths: Vec<FilePath>,
    cfgpaths: Vec<CfgPath>,
}

impl Atlas {
    pub fn new() -> Self {
        Self {
            filepaths: vec![],
            cfgpaths: vec![],
        }
    }

    pub fn with_prelude() -> IoResult<Self> {
        Self::new_within_dir(PRELUDE_PATH)
    }

    #[inline]
    pub fn filepath_count(&self) -> usize {
        self.filepaths.len()
    }

    pub fn cfgpath_count(&self) -> usize {
        self.cfgpaths.len()
    }

    #[inline]
    pub fn has_filepath(&self, path: impl AsRef<Path>) -> bool {
        let p = path.as_ref();
        self.filepaths_iter().any(|src| src.path() == p)
    }

    pub fn find_filepath(&self, f: impl FnMut(&&FilePath) -> bool) -> Option<&FilePath> {
        self.filepaths_iter().find(f)
    }

    #[inline]
    pub fn has_cfgpath(&self, path: impl AsRef<Path>) -> bool {
        let p = path.as_ref();
        self.cfgpaths.iter().any(|cfg| cfg.path() == p)
    }

    pub fn find_cfgpath(&self, f: impl FnMut(&&CfgPath) -> bool) -> Option<&CfgPath> {
        self.cfgpaths_iter().find(f)
    }

    pub fn new_within_dir(dir: impl AsRef<Path>) -> IoResult<Self> {
        let mut atlas = Self::new();
        let paths = Self::walk_path(dir.as_ref())?;
        atlas.add_paths(paths);
        Ok(atlas)
    }

    /// Returns `true` if a given path has been stored as either a
    /// `FilePath` or a `CfgPath`.
    pub fn contains_path(&self, path: impl AsRef<Path>) -> bool {
        let path = path.as_ref();
        self.cfgpaths_iter()
            .map(|cfg| cfg.path())
            .chain(self.filepaths_iter().map(|fp| fp.path()))
            .any(|p| p == path)
    }

    pub fn add_filepath<P: AsRef<Path>>(&mut self, path: P) -> Option<FileId> {
        let path = path.as_ref();
        if is_target_file(&path) {
            if let Some(n) = self.find_filepath(|fp| fp.path() == path) {
                Some(n.id())
            } else {
                let id = FileId(self.filepath_count());
                self.filepaths.push(FilePath {
                    id,
                    path: path.to_path_buf(),
                });
                Some(id)
            }
        } else {
            None
        }
    }

    pub fn add_cfgpath<P: AsRef<Path>>(&mut self, path: P) -> Option<CfgId> {
        let path = path.as_ref();
        if is_manifest_file(&path) {
            if let Some(n) = self.find_cfgpath(|fp| fp.path() == path) {
                Some(n.id())
            } else {
                let id = CfgId(self.cfgpath_count());
                self.cfgpaths.push(CfgPath {
                    id,
                    path: path.to_path_buf(),
                });
                Some(id)
            }
        } else {
            None
        }
    }

    pub fn add_path(&mut self, path: impl AsRef<Path>) -> Option<AtlasItemId> {
        let path = path.as_ref();
        if is_target_file(&path) {
            self.add_filepath(path).map(AtlasItemId::FileId)
        } else if is_manifest_file(path) {
            self.add_cfgpath(path).map(AtlasItemId::CfgId)
        } else {
            None
        }
    }

    pub fn add_paths<P: AsRef<Path>, I: IntoIterator<Item = P>>(
        &mut self,
        paths: I,
    ) -> Vec<AtlasItemId> {
        paths
            .into_iter()
            .flat_map(|path| self.add_path(path))
            .collect()
    }

    pub fn add_dir(&mut self, dir: Directory) {
        self.extend(dir.all_wysk_files())
    }

    pub fn add_dirs(&mut self, dirs: impl IntoIterator<Item = Directory>) {
        dirs.into_iter()
            .for_each(|dir| self.extend(dir.all_wysk_files()))
    }

    pub fn filepaths(&self) -> &[FilePath] {
        self.filepaths.as_slice()
    }

    #[inline]
    pub fn filepaths_iter(&self) -> std::slice::Iter<'_, FilePath> {
        self.filepaths.iter()
    }

    #[inline]
    pub fn filepaths_iter_mut(&mut self) -> std::slice::IterMut<'_, FilePath> {
        self.filepaths.iter_mut()
    }

    pub fn cfgpaths(&self) -> &[CfgPath] {
        self.cfgpaths.as_slice()
    }

    #[inline]
    pub fn cfgpaths_iter(&self) -> std::slice::Iter<'_, CfgPath> {
        self.cfgpaths.iter()
    }

    #[inline]
    pub fn cfgpaths_iter_mut(&mut self) -> std::slice::IterMut<'_, CfgPath> {
        self.cfgpaths.iter_mut()
    }

    pub fn stored_items(&self) -> impl Iterator<Item = AtlasItem> + '_ {
        self.cfgpaths_iter()
            .map(|cfg| AtlasItem::CfgPath(cfg))
            .chain(self.filepaths_iter().map(|fp| AtlasItem::FilePath(fp)))
    }

    /// Creates a new `Atlas` instance from a given `Directory`
    /// instance, discarding any IO-related errors. This will
    /// additionally add files in a disjoint manner -- rather than
    /// identifying what kind of file each path refers to as the path
    /// gets added, it will separate paths into file sourcepaths and
    /// manifest paths. Additionally, it will prioritize adding
    /// manifest files, `main` and `lib` files before `mod` and other
    /// files within the same directory.
    ///
    /// Finally, it will return a pair consisting of the new `Atlas`
    /// instnce and a vector of all the `AtlasItemId`s corresponding
    /// to the newly added paths.
    pub fn walk_dir(dir: &Directory) -> (Self, Vec<AtlasItemId>) {
        let (srcpaths, cfgpaths) = Self::walk_path(dir.path()).into_iter().flatten().fold(
            (vec![], vec![]),
            |(mut srcs, mut cfgs), path| {
                if is_target_file(path.as_path()) {
                    srcs.push(path)
                } else if is_manifest_file(path.as_path()) {
                    cfgs.push(path)
                };
                (srcs, cfgs)
            },
        );
        let mut atlas = Self::new();
        let (mains, nonmains): (Vec<_>, Vec<_>) = srcpaths
            .into_iter()
            .partition(|path| path.ends_with(FilePath::MAIN_PATH));
        let (libs, nonlibs): (Vec<_>, Vec<_>) = nonmains
            .into_iter()
            .partition(|path| path.ends_with(FilePath::LIB_PATH));
        let (mods, nonmods): (Vec<_>, Vec<_>) = nonlibs
            .into_iter()
            .partition(|path| path.ends_with(FilePath::MOD_PATH));
        let ids = atlas.add_paths(
            cfgpaths
                .into_iter()
                .chain(mains)
                .chain(libs)
                .chain(mods)
                .chain(nonmods),
        );
        (atlas, ids)
    }

    /// Returns a vector containing the paths of **all** manifest
    /// files (named `manifest.toml`) and wysk files (ending in `.wy`)
    /// contained within the given directory (and subdirectories).
    /// Returns an error if the given path is invalid.
    pub fn walk_path<P: AsRef<Path>>(p: P) -> IoResult<Vec<PathBuf>> {
        let mut paths = vec![];
        let mut queue: Vec<PathBuf> = vec![PathBuf::from(p.as_ref())];
        while let Some(x) = queue.pop() {
            if x.is_file() {
                if is_target_file(&x) || is_manifest_file(&x) {
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

impl std::ops::Index<FileId> for Atlas {
    type Output = FilePath;

    fn index(&self, index: FileId) -> &Self::Output {
        &self.filepaths[index.0]
    }
}

impl<P: AsRef<Path>> Extend<P> for Atlas {
    fn extend<T: IntoIterator<Item = P>>(&mut self, iter: T) {
        self.add_paths(iter);
    }
}

/// `FilePath` describes a filepath ending in the extension `.wy`, and
/// hence cannot be directly created. Instead, file system traversing
/// helpers -- in `Atlas` and `Dir` -- are used to generate `FilePath`
/// instances. This helps prevent non-wysk source files from
/// inadvertently being included in the `Atlas` file tree, etc.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FilePath {
    id: FileId,
    path: PathBuf,
}

impl FilePath {
    pub const MAIN_PATH: &'static str = "main.wy";
    pub const LIB_PATH: &'static str = "lib.wy";
    pub const MOD_PATH: &'static str = "mod.wy";

    /// Returns the `FileId` generated for this `Src` instance.
    pub fn id(&self) -> FileId {
        self.id
    }

    pub fn file_name(&self) -> &str {
        // safe to unwrap since *all* `Src` instances **must** end in the
        // file-extension `.wy`.
        self.path().file_name().and_then(|s| s.to_str()).unwrap()
    }

    /// Checks whether the first character of the file's name begins with an
    /// ascii alphabetic character
    pub fn name_is_valid(&self) -> bool {
        let filename = self.file_name();
        filename.starts_with(|c: char| c.is_ascii_alphabetic())
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
    pub fn has_ambiguous_sibling(&self) -> bool {
        let ext = self.path.extension();
        let mine = self.file_name();
        let len = mine.len();
        let init = mine.chars().next().unwrap();
        if let Some(pn) = self.path.parent() {
            for rd in fs::read_dir(pn) {
                for de in rd.flatten() {
                    let their = de.path();
                    if is_target_file(&their) {
                        if let Some(true) = their.file_name().and_then(|s| s.to_str()).map(|s| {
                            let c0 = s.chars().next().unwrap();
                            their.extension() == ext
                                && s.len() == len
                                && init == c0
                                && mine[1..] == s[1..]
                        }) {
                            return true;
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
    pub fn parent_dir(&self) -> Directory {
        let p = self
            .canonicalize()
            .ok()
            .and_then(|p| p.parent().map(Path::to_path_buf))
            .unwrap_or_else(|| PathBuf::from("."));
        Directory::new(p)
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
        fs::read_to_string(self.path())
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
}

impl AsRef<Path> for FilePath {
    fn as_ref(&self) -> &Path {
        self.path()
    }
}

impl std::fmt::Display for FilePath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.path().display())
    }
}

impl PartialEq<&Path> for FilePath {
    fn eq(&self, other: &&Path) -> bool {
        self.path() == *other
    }
}

impl PartialEq<FilePath> for &Path {
    fn eq(&self, other: &FilePath) -> bool {
        *self == other.as_ref()
    }
}

impl PartialEq<PathBuf> for FilePath {
    fn eq(&self, other: &PathBuf) -> bool {
        self.path() == other.as_path()
    }
}

impl PartialEq<FilePath> for PathBuf {
    fn eq(&self, other: &FilePath) -> bool {
        self.as_path() == other.path()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Directory {
    path: PathBuf,
}

impl AsRef<Path> for Directory {
    fn as_ref(&self) -> &Path {
        self.path.as_path()
    }
}

impl Directory {
    pub const SRC_DIR: &'static str = "src";

    pub fn new(path: impl AsRef<Path>) -> Self {
        let mut dir = Self {
            path: path.as_ref().to_path_buf(),
        };
        dir.normalize();
        dir
    }

    /// Transparent wrapper around `std::env::current_dir()` with a depth of
    /// `0`.
    #[inline]
    pub fn from_current_dir() -> IoResult<Self> {
        env::current_dir().and_then(|pb| pb.canonicalize().map(|pb| Directory::new(pb)))
    }

    #[inline]
    pub fn path(&self) -> &Path {
        self.path.as_path()
    }

    pub fn is_src_dir(&self) -> bool {
        self.path.ends_with(Self::SRC_DIR)
    }

    pub fn has_manifest(&self) -> bool {
        self.path.join(Manifest::FILENAME).exists()
    }

    pub fn manifest_paths(&self) -> impl Iterator<Item = PathBuf> + '_ {
        self.path.read_dir().into_iter().flat_map(|rd| {
            rd.filter_map(|res| {
                res.ok().map(|de| {
                    let path = de.path();
                    if is_manifest_file(&path) {
                        Some(path)
                    } else {
                        None
                    }
                })
            })
            .flatten()
        })
    }

    pub fn read_manifest(&self) -> Option<Manifest> {
        Manifest::from_path(self.path.join(Manifest::FILENAME))
    }

    pub fn has_src_dir(&self) -> bool {
        self.path.join(Self::SRC_DIR).exists()
    }

    /// Returns an iterator of immediate descendant paths ending
    /// in `.wy`.
    pub fn immediate_wysk_files(&self) -> impl Iterator<Item = PathBuf> + '_ {
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
        })
    }

    /// Recursively searches all children of this directory and returns an
    /// iterator containing paths ending in `.wy`.
    pub fn all_wysk_files(&self) -> impl Iterator<Item = PathBuf> + '_ {
        self.all_sub_dirs()
            .into_iter()
            .flat_map(move |dir| dir.immediate_wysk_files().collect::<Vec<_>>())
    }

    #[inline]
    /// Returns the canonical (i.e., absolute) form of the path with all
    /// intermediate components normalized and symbolic links resolved.
    ///
    /// To mutably modify the path in place, use `normalize`.
    pub fn canonicalize(&self) -> IoResult<PathBuf> {
        self.path.canonicalize()
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

    /// Returns an iterator of `Dir`s corresponding to immediate descendant
    /// directories. Since the directories returned are immediate descendants of
    /// `Self`, it follows that all returned directories have a `depth` of
    /// `self.depth + 1`.
    pub fn child_dirs(&self) -> impl Iterator<Item = Directory> + '_ {
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
                        .map(|path| Directory::new(path))
                })
            })
            .flatten()
    }

    /// Returns a list of `Dir`s corresponding to all the subdirectories
    /// recursively found within the `path` field.
    pub fn all_sub_dirs(&self) -> Vec<Self> {
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
            while let Some(path) = paths.pop() {
                reader(path.as_path(), &mut des);
                dirs.push(Directory::new(path))
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
        let root = Directory {
            path: PathBuf::from("../../language"),
        };
        let subdirs = root.all_sub_dirs();
        println!("subdirectories: {:#?}", &subdirs);
        assert!(subdirs[3].is_src_dir());
        println!("{:?}", root.immediate_wysk_files().collect::<Vec<_>>());
        println!("all {:?}", root.all_wysk_files().collect::<Vec<_>>());
        println!(
            "displayed: {:#?}",
            root.all_wysk_files().collect::<Vec<_>>()
        )
    }
}
