use std::collections::BTreeMap as Map;
use std::fs;
use std::hash::Hash;
use std::path::Path;

use serde::{Deserialize, Serialize};
pub use toml::Value;

type List<S = String> = Vec<S>;
type MaybeList<S = String> = Option<List<S>>;

/// The entire `manifest.toml` file. Parametrized over a `stringy`
/// type in order to allow for flexibility with interned symbols.
#[derive(Debug, Serialize, Deserialize)]
pub struct Manifest<S = String>
where
    S: Ord,
{
    pub package: Package<S>,
    pub workspace: Option<Workspace<S>>,
    pub dependencies: Dependencies<S>,
    pub dev_dependencies: Option<DevDependencies<S>>,
    #[serde(rename = "lib")]
    pub library: Option<Lib>,
    #[serde(rename = "exe")]
    pub binary: Option<Bin>,
}

impl Manifest {
    pub const FILENAME: &'static str = "Manifest.toml";
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

    pub fn save<P: AsRef<Path>>(self, directory: P) -> Self {
        let path = directory.as_ref().join(Self::FILENAME);
        let _ = fs::write(path, self.toml_text());
        self
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
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Package<S = String> {
    /// Name of the package
    pub name: S,
    /// Version of package
    pub version: S,
    pub license: Option<S>,
    pub license_file: Option<S>,
    pub assets: Option<S>,
    pub readme: Option<S>,
    pub description: Option<S>,
    pub homepage: Option<S>,
    pub repository: Option<S>,
    pub authors: MaybeList<S>,
    pub keywords: MaybeList<S>,
    pub categories: MaybeList<S>,
}

impl<S> Package<S> {
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
pub struct Documentation<S = String> {
    pub webpage: Option<S>,
    pub index: Option<S>,
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

#[derive(Debug, Serialize, Deserialize)]
pub struct Dependencies<K = String, V = String>(pub Map<K, Dependency<V>>)
where
    K: Ord;

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
#[serde(untagged)]
pub enum Dependency<S = String> {
    /// When only a version number is provided
    Version(S),
    Local {
        path: S,
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

#[derive(Debug, Serialize, Deserialize)]
pub struct DevDependencies<K: Ord = String, S = String>(
    pub Map<K, Dependency<S>>,
);

#[derive(Debug, Serialize, Deserialize)]
pub struct Artifacts<S = String>(Map<S, S>)
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
        keywords = ["wysc lang", "config"]
    
    
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
        match std::fs::read_to_string(
            "/Users/lictor/Rust/lolvm/examples/manifest.toml",
        ) {
            Ok(source) => match toml::from_str::<Manifest>(&*source) {
                Ok(cfg) => {
                    println!(
                        "Manifest successfully deseralized:\n\n{:#?}",
                        &cfg
                    );
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
