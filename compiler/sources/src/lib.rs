//! This library deals with source files and exposes an API used to facilitate
//! bookkeeping of file-related sources.

use std::{path::Path, sync::Arc};

use files::{File, SourceMap};
use manifest::Manifest;
use paths::{Atlas, Directory, FileId, FilePath};

pub mod files;
pub mod manifest;
pub mod paths;

pub struct ProjectBuilder {
    root_dir: Option<Directory>,
    atlas: Atlas,
    manifests: Vec<Manifest>,
    submodules: Vec<FileId>,
}

impl ProjectBuilder {
    pub fn new(root_dir: Directory) -> Self {
        let (atlas, _) = Atlas::walk_dir(&root_dir);
        let manifests = vec![];
        let submodules = vec![];
        ProjectBuilder {
            root_dir: Some(root_dir),
            atlas,
            manifests,
            submodules,
        }
    }
    pub fn read_manifests(mut self) -> Self {
        if let Some(root_dir) = self.root_dir.take() {
            if let Some(manifest) = root_dir.read_manifest() {
                if !self.manifests.contains(&manifest) {
                    self.manifests.push(manifest)
                }
            }
            self.atlas.cfgpaths().into_iter().for_each(|p| {
                if let Some(manifest) = p.read_manifest() {
                    if !self.manifests.contains(&manifest) {
                        self.manifests.push(manifest)
                    }
                }
            });
            self.root_dir = Some(root_dir);
        }
        self
    }

    pub fn store_manifest_submodules(mut self) -> Self {
        self.manifests.iter().clone().for_each(|m| {
            m.workspaces()
                .flat_map(|p| self.atlas.add_filepath(p))
                .for_each(|id| {
                    if self.submodules.contains(&id) {
                        self.submodules.push(id);
                    }
                })
        });
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
            manifests,
            mut submodules,
        } = self;
        root_dir.map(|root_dir| {
            let mut source_map = SourceMap::new();
            atlas.filepaths_iter().for_each(|fp| {
                if let Ok(file) = source_map.add_from_filepath(fp.clone()) {
                    let file_id = file.id();
                    if !submodules.contains(&file_id) {
                        submodules.push(file_id)
                    }
                }
            });
            Project {
                atlas,
                manifests,
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
    manifests: Vec<Manifest>,
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
            .read_manifests()
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

    pub fn manifests(&self) -> &[Manifest] {
        self.manifests.as_slice()
    }

    pub fn manifests_mut(&mut self) -> &mut [Manifest] {
        self.manifests.as_mut_slice()
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

    pub fn get_file_id_for_stored(&self, p: impl AsRef<Path>) -> Option<FileId> {
        let path = p.as_ref();
        self.stored_files().find_map(|file| {
            if file.src_path().path() == path {
                Some(file.id())
            } else {
                None
            }
        })
    }

    pub fn get_stored_file_by_path(&self, p: impl AsRef<Path>) -> Option<&Arc<File>> {
        let path = p.as_ref();
        self.stored_files()
            .find(|file| file.src_path().path() == path)
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
    fn test_prelude_project() {
        let dir = Directory::new(paths::PRELUDE_PATH);
        let project = new_project(dir);
        assert!(project.is_some());
        let project = project.unwrap();
        assert!(!project.manifests.is_empty());
        let manifest = &project.manifests;
        assert!(&manifest[0].library.is_some());
        let man_lib = (&manifest[0]).library.as_ref().unwrap();
        assert!(man_lib.submodules.is_some());
        let submodules = man_lib.submodules.as_ref().unwrap();
        assert!(project.submodules.len() == submodules.len());
    }
}
