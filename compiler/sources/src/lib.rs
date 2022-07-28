//! This library deals with source files and exposes an API used to facilitate
//! bookkeeping of file-related sources.

use std::path::Path;

use manifest::Manifest;
use paths::{Atlas, Dir, Src};

pub mod manifest;
pub mod paths;

#[derive(Debug)]
pub enum Config {
    /// Used whenever a manifest file cannot be found.
    Script,
    Project(Manifest),
}

impl Config {
    pub fn manifest(&self) -> Option<&Manifest> {
        match self {
            Config::Script => None,
            Config::Project(man) => Some(man),
        }
    }
}

#[derive(Debug)]
pub struct Project {
    atlas: Atlas,
    config: Config,
}

impl Project {
    /// Given a `Dir` instance, finds all Wysk source files contained
    /// (recursively) in either `src` or in the directories listed in the
    /// `workspaces` field of the manifest file `manifest.toml`.
    pub fn new_from_dir(dir: Dir) -> Option<Project> {
        let man = dir.read_manifest();
        let mut atlas = Atlas::walk_dir(dir);
        man.and_then(|man| {
            atlas.add_paths(man.workspaces());
            Some(Config::Project(man))
        })
        .map(|config| Project { atlas, config })
    }

    pub fn atlas(&self) -> &Atlas {
        &self.atlas
    }
    pub fn atlas_mut(&mut self) -> &mut Atlas {
        &mut self.atlas
    }
    pub fn config(&self) -> &Config {
        &self.config
    }
    pub fn manifest(&self) -> Option<&Manifest> {
        self.config.manifest()
    }
    pub fn sources(&self) -> std::slice::Iter<'_, Src> {
        self.atlas.sources_iter()
    }
}

/// Alias for the associated method `Project::new_from_dir`
pub fn new_project(path: impl AsRef<Path>) -> Option<Project> {
    Project::new_from_dir(Dir::new(0, path))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn inspect_prelude_project() {
        let dir = Dir::new(0, paths::PRELUDE_PATH);
        let project = new_project(dir);
        println!("{:#?}", &project)
    }
}
