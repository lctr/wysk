use std::fs;
use std::hash::Hash;
use std::path::Path;
use std::{collections::BTreeMap as Map, path::PathBuf};

use serde::{Deserialize, Serialize};
pub use toml::Value;

pub fn maybe_strings_to_pathbufs<S: AsRef<Path>>(
    it: Option<&Vec<S>>,
) -> impl Iterator<Item = PathBuf> + '_ {
    it.into_iter().flatten().map(|s| s.as_ref().to_path_buf())
}

type List<S = String> = Vec<S>;
type MaybeList<S = String> = Option<List<S>>;

/// The entire `manifest.toml` file. Parametrized over a `stringy`
/// type in order to allow for flexibility with interned symbols.
#[derive(Debug, Serialize, Deserialize)]
pub struct Manifest<S = String, P = S>
where
    S: Ord,
{
    pub package: Package<S>,
    pub workspace: Option<Workspace<S>>,
    pub dependencies: Dependencies<S>,
    pub dev_dependencies: Option<DevDependencies<S, S, P>>,
    #[serde(rename = "lib")]
    pub library: Option<Lib>,
    #[serde(rename = "exe")]
    pub binary: Option<Bin>,
}

impl Manifest {
    pub const FILENAME: &'static str = "manifest.toml";
    pub const INITIAL_VERSION: &'static str = "0.0.1";

    pub fn new(name: String) -> Manifest {
        Manifest {
            package: Package::new(name, Self::INITIAL_VERSION.into()),
            workspace: None,
            dependencies: Dependencies(Map::new()),
            dev_dependencies: None,
            library: None,
            binary: None,
        }
    }

    fn toml_text(&self) -> String {
        toml::to_string_pretty(self).unwrap()
    }

    pub fn save<P: AsRef<Path>>(&self, directory: P) -> std::io::Result<P> {
        let path = directory.as_ref().join(Self::FILENAME);
        fs::write(path, self.toml_text()).and(Ok(directory))
    }

    pub fn from_path<P: AsRef<Path>>(path: P) -> Option<Manifest> {
        match fs::read_to_string(path.as_ref()) {
            Ok(txt) => toml::from_str::<Manifest>(&*txt).ok(),
            Err(e) => {
                eprintln!(
                    "Error reading manifest from path `{}`: {}",
                    path.as_ref().display(),
                    e
                );
                None
            }
        }
    }

    pub fn workspaces(&self) -> impl Iterator<Item = PathBuf> + '_ {
        self.workspace.as_ref().into_iter().flat_map(|ws| {
            ws.members
                .as_ref()
                .into_iter()
                .flatten()
                .map(|s| PathBuf::from(&*s))
        })
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Package<S = String, P = S> {
    /// Name of the package
    pub name: S,
    /// Version of package
    pub version: S,
    pub license: Option<S>,
    pub license_file: Option<S>,
    pub assets: Option<P>,
    pub readme: Option<P>,
    pub description: Option<S>,
    pub homepage: Option<S>,
    pub repository: Option<S>,
    pub authors: MaybeList<S>,
    pub keywords: MaybeList<S>,
    pub categories: MaybeList<S>,
}

impl<S, P> Package<S, P> {
    pub fn new(name: S, version: S) -> Self {
        Package {
            name,
            version,
            license: None,
            license_file: None,
            assets: None,
            readme: None,
            description: None,
            homepage: None,
            repository: None,
            authors: None,
            keywords: None,
            categories: None,
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Documentation<S = String, P = S> {
    pub webpage: Option<S>,
    pub index: Option<P>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Lib<S = String> {
    pub name: S,
    pub test: Option<bool>,
    pub submodules: MaybeList<S>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Bin<S = String> {
    pub name: S,
    pub test: Option<bool>,
    pub submodules: MaybeList<S>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Workspace<S = String> {
    pub members: Option<Vec<S>>,
}

impl<S> Workspace<S> {
    pub fn pathbufs(&self) -> impl Iterator<Item = PathBuf> + '_
    where
        S: AsRef<Path>,
    {
        maybe_strings_to_pathbufs(self.members.as_ref())
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Dependencies<K = String, V = String, P = V>(pub Map<K, Dependency<V, P>>)
where
    K: Ord;

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
#[serde(untagged)]
pub enum Dependency<S = String, P = S> {
    /// When only a version number is provided
    Version(S),
    Local {
        path: P,
        version: Option<S>,
    },
    Remote {
        url: S,
        version: Option<S>,
    },
    Git {
        repo: S,
        version: Option<S>,
        branch: Option<S>,
    },
}

wy_common::variant_preds! { |S, P| Dependency[S, P]
    | version_only => Version(_)
    | local_only => Local {..}
    | remote_only => Remote {..}
    | git_only => Git {..}
}

impl<S, P> Dependency<S, P> {
    pub fn maybe_local_path(&self) -> Option<PathBuf>
    where
        P: AsRef<Path>,
    {
        if let Self::Local { path, .. } = self {
            Some(path.as_ref().to_path_buf())
        } else {
            None
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DevDependencies<K: Ord = String, S = String, P = S>(pub Map<K, Dependency<S, P>>);

#[derive(Debug, Serialize, Deserialize)]
pub struct Artifacts<S = String, P = S>(Map<S, P>)
where
    S: Ord;

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_default_manifest() {
        println!("{:?}", Manifest::new("Test".into()))
    }

    #[test]
    fn test_package_toml() {
        let content = r#"
        [package]
        name = "Tester"
        version = "0.0.1"
        license = "MIT"
        description = "A simple description"
        authors = ["Lictor Guzman"]
        keywords = ["wysk lang", "config"]
    
    
        [workspace]
        members = [ "subdir1", "womp"]
    
        [dependencies]
        a_thing = "1"
        c_thing = { url = "https://website.com" }
        b_thing = { path = "../thingy" }
        d_thing = { version = "1.2", repo = "https://github.com/a/b.git", branch = "main" }
    
        [dev-dependencies]

        [lib]
        name = "tester_lib"
        "#;
        let manifest: Manifest = toml::from_str(content).unwrap();
        match toml::to_string_pretty(&manifest) {
            Ok(s) => println!("prettified:\n{}", s),
            Err(e) => eprintln!(
                "error prettifying: {}\n\nManifest deserialized:\n{:#?}",
                e, manifest
            ),
        }
    }

    #[test]
    fn test_deserialize_example_manifest() {
        match std::fs::read_to_string("../../language/prelude/manifest.toml") {
            Ok(source) => match toml::from_str::<Manifest>(&*source) {
                Ok(cfg) => {
                    println!("Manifest successfully deseralized:\n\n{:#?}", &cfg);
                }
                Err(e) => {
                    eprintln!("Error reading manifest.toml! {}", e)
                }
            },
            Err(e) => {
                eprintln!("Unable to find `manifest.toml` file! {}", e)
            }
        }
    }
}
