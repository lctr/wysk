//! This library deals with source files and exposes an API used to facilitate
//! bookkeeping of file-related sources.

use std::path::Path;

use files::{File, SourceMap};
use manifest::Manifest;
use paths::{Atlas, Directory, FileId, FilePath};

pub mod files;
pub mod manifest;
pub mod paths;

pub struct ProjectBuilder {
    root_dir: Option<Directory>,
    atlas: Atlas,
    manifest: Option<Manifest>,
    submodules: Vec<FileId>,
}

impl ProjectBuilder {
    pub fn new(root_dir: Directory) -> Self {
        let (atlas, _) = Atlas::walk_dir(&root_dir);
        let manifest = None;
        let submodules = vec![];
        ProjectBuilder {
            root_dir: Some(root_dir),
            atlas,
            manifest,
            submodules,
        }
    }
    pub fn read_manifest(mut self) -> Self {
        if let Some(root_dir) = self.root_dir.take() {
            self.manifest = root_dir.read_manifest();
            self.root_dir = Some(root_dir);
        }
        self
    }

    pub fn store_manifest_submodules(mut self) -> Self {
        if let Some(manifest) = self.manifest.take() {
            manifest
                .workspaces()
                .flat_map(|p| self.atlas.add_filepath(p))
                .for_each(|f| {
                    if self.submodules.contains(&f) {
                        self.submodules.push(f)
                    }
                });

            self.manifest = Some(manifest);
        }
        self
    }

    pub fn walk_root_dir(mut self) -> Self {
        if let Some(dir) = self.root_dir.take() {
            self.atlas.add_dir(dir.clone());
            self.root_dir = Some(dir);
        }
        self
    }

    pub fn build_project(self) -> Option<Project> {
        let ProjectBuilder {
            root_dir,
            atlas,
            manifest,
            submodules: _,
        } = self;
        root_dir.map(|root_dir| {
            let mut source_map = SourceMap::new();
            let mut submodules = vec![];
            atlas.filepaths_iter().for_each(|fp| {
                if let Ok(file) = source_map.add_from_filepath(fp.clone()) {
                    submodules.push(file.src_path().id())
                }
            });
            Project {
                atlas,
                manifest,
                source_map,
                root_dir,
                submodules,
            }
        })
    }
}

#[derive(Debug)]
pub struct Project {
    atlas: Atlas,
    manifest: Option<Manifest>,
    source_map: SourceMap,
    root_dir: Directory,
    submodules: Vec<FileId>,
}

impl Project {
    /// Given a `Dir` instance, finds all Wysk source files contained
    /// (recursively) in either `src` or in the directories listed in the
    /// `workspaces` field of the manifest file `manifest.toml`.
    pub fn new_from_dir(dir: Directory) -> Option<Project> {
        ProjectBuilder::new(dir)
            .read_manifest()
            .store_manifest_submodules()
            .walk_root_dir()
            .build_project()
    }
    pub fn root_dir(&self) -> &Directory {
        &self.root_dir
    }

    pub fn atlas(&self) -> &Atlas {
        &self.atlas
    }
    pub fn atlas_mut(&mut self) -> &mut Atlas {
        &mut self.atlas
    }
    pub fn manifest(&self) -> Option<&Manifest> {
        self.manifest.as_ref()
    }
    pub fn manifest_mut(&mut self) -> Option<&mut Manifest> {
        self.manifest.as_mut()
    }
    pub fn filepaths(&self) -> std::slice::Iter<'_, FilePath> {
        self.atlas.filepaths_iter()
    }
    pub fn source_map(&self) -> &SourceMap {
        &self.source_map
    }
    pub fn source_map_mut(&mut self) -> &mut SourceMap {
        &mut self.source_map
    }
    pub fn stored_files(&self) -> std::slice::Iter<'_, std::sync::Arc<File>> {
        self.source_map.iter_files()
    }
    pub fn file_count(&self) -> usize {
        self.source_map.file_count()
    }
    pub fn submodule_ids(&self) -> &[FileId] {
        self.submodules.as_slice()
    }
}

/// Alias for the associated method `Project::new_from_dir`
pub fn new_project(path: impl AsRef<Path>) -> Option<Project> {
    Project::new_from_dir(Directory::new(path))
}

pub fn prelude_project() -> Project {
    let proj = new_project(paths::PRELUDE_PATH);
    assert!(proj.is_some(), "failed to initialize `prelude`!");
    proj.unwrap()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn inspect_prelude_project() {
        let dir = Directory::new(paths::PRELUDE_PATH);
        let project = new_project(dir);
        println!("{:#?}", &project)
    }
}
