use wy_common::mapstack::MapStack;
use wy_intern::{symbol, Symbol, Symbolic};
use wy_syntax::{
    ident::{Chain, Ident},
    Module,
};

wy_common::newtype! {
    usize in Uid | Show AsUsize (+= usize |rhs| rhs) (+ u32 |rhs| rhs as usize)
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Name {
    pub ident: Ident,
    pub uid: Uid,
}

impl Name {
    /// Creates a name for a given identifier with a `uid` starting at `Uid(0)`.
    pub fn new(ident: Ident) -> Self {
        Name { ident, uid: Uid(0) }
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}_'{}", self.ident, self.uid)
    }
}

impl PartialEq<Symbol> for Name {
    fn eq(&self, other: &Symbol) -> bool {
        self.ident.symbol() == *other
    }
}

impl PartialEq<Ident> for Name {
    fn eq(&self, other: &Ident) -> bool {
        &self.ident == other
    }
}

impl PartialEq<Name> for Ident {
    fn eq(&self, other: &Name) -> bool {
        self == &other.ident
    }
}

impl PartialEq<Chain> for Name {
    fn eq(&self, other: &Chain) -> bool {
        other == &self.ident
    }
}

impl PartialEq<Name> for Chain {
    fn eq(&self, other: &Name) -> bool {
        self == &other.ident
    }
}

#[derive(PartialEq, Debug)]
pub enum NameError {
    /// Emitted when multiple definitions have the same `Name`
    Clash(Ident),
    /// Emitted when a given `Name` is not in scope
    Unbound(Ident),
}

impl std::fmt::Display for NameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NameError::Clash(s) => write!(f, "ambiguous name: `{}` is defined multiple times", s),
            NameError::Unbound(s) => write!(f, "unbound name: `{}` is not defined", s),
        }
    }
}

/// A name supply holds the state necessary for producing unique `Name`s from
/// identifiers.
#[derive(Clone, Debug)]
pub struct Supply(Uid);

impl Supply {
    /// Note: names created with `Name::new` require an identifier and begin
    /// with a `Uid(0)`, while the initial state of the `Supply` created with
    /// `Supply::new` begins at `Uid(1)`.
    pub fn new() -> Self {
        Supply(Uid(1))
    }
    /// Increment the supply Supply
    pub fn tick(&mut self) -> Uid {
        self.0 += 1;
        self.0
    }

    /// Generates a fresh (unique + anonymous) name
    pub fn fresh(&mut self) -> Name {
        Name {
            ident: Ident::Fresh(symbol::intern_once("_a")),
            uid: self.tick(),
        }
    }

    pub fn ident(&mut self, ident: Ident) -> Name {
        Name {
            ident,
            uid: self.tick(),
        }
    }
}

/// The `Renamer` walks the AST and generates unique names from the identifiers
/// found within the AST. Some naming invariants:
/// * each module gets a `Uid` which is used in the names for its top level
///   declarations (function decls, type aliases, data decls, etc)
/// * methods share `Uid`s with the class they belong to
///     - this facilitates locating instance methods specific to a certain class
///       when constructing instance dictionaries in later phases!
/// * other named entities may share an `ident` field or a `uid` field, but
///   **must not introduce name collisions*
#[derive(Debug)]
struct Renamer {
    supply: Supply,
    errors: Vec<NameError>,
    uniques: MapStack<Ident, Name>,
}

impl Renamer {
    pub fn new() -> Self {
        Self {
            supply: Supply::new(),
            errors: Vec::new(),
            uniques: MapStack::new(),
        }
    }

    fn declare_global(&mut self, ident: Ident, uid: Uid) -> Name {
        self.make_unique(ident);
        // we can unwrap this since we know `uniques` has this ident, ensured by
        // the call to `make_unique`
        self.uniques
            .get_mut(&ident)
            .map(|n| {
                n.uid = uid;
                *n
            })
            .unwrap()
    }

    fn make_unique(&mut self, ident: Ident) -> Name {
        if self.uniques.in_scope(&ident) {
            self.errors.push(NameError::Clash(ident));
            self.uniques.get(&ident).copied().unwrap()
        } else {
            let unique = self.supply.ident(ident);
            self.uniques.insert(ident, unique);
            unique
        }
    }

    fn get_name(&self, ident: Ident) -> Name {
        match self.uniques.get(&ident) {
            Some(&Name { uid, ..}) => Name { ident, uid },
            // primitives have `Uid(0)`
            None => Name { ident, uid: Uid(0) },
        }
    }

    fn import_globals<Id, U, F>(&mut self, module: &Module<Id, U>, uid: Uid, mut to_ident: F)
    where
        Id: Eq + Copy,
        F: FnMut(Id) -> Ident,
    {
        let Module {
            uid: _,
            modname: _,
            imports: _,
            infixes: _,
            datatys,
            classes,
            implems,
            fundefs,
            aliases: _,
            newtyps,
        } = module;
        datatys
            .iter()
            .flat_map(|dt_decl| dt_decl.vnts.iter().map(|v| v.name))
            .chain(newtyps.iter().map(|nt_decl| nt_decl.ctor))
            .chain(classes.iter().flat_map(|cl_decl| 
                // Option implements `IntoIterator` and is cheaper than a `Vec`
                Some(cl_decl.name)
                    .into_iter()
                    .chain(cl_decl.defs.iter().map(|method| method.name()))))
            .chain(fundefs.iter().map(|fn_decl| fn_decl.name))
            .for_each(|ident| {
                self.declare_global(to_ident(ident), uid);
            });
        implems.iter().for_each(|inst| {
            let class_uid = self.get_name(to_ident(inst.name)).uid;
            inst.defs.iter().for_each(|binding| {
                self.declare_global(to_ident(binding.name), class_uid);
            })
        })
    }

    /// Loads the global names from a slice of `all_modules` (parametrized by
    /// `Name`s instead of `Ident`s, i.e., `&[Module<Name, Uid>]`) into the
    /// renamer's current scope. Note that the global names include imports from
    /// `all_modules` alongside globals in `module`.
    fn insert_globals(
        &mut self,
        uid: Uid,
        module: &Module<Ident>,
        all_modules: &[Module<Name, Uid>],
    ) {
        self.import_globals(module, uid, identity);
        for import in module.imports.iter() {
            let imported_m = match all_modules
                .iter()
                .find(|mdl| import.name == mdl.modname.map_ref(|nm| nm.ident)) {
                Some(m) => m,
                None => {
                    let ident = Ident::Upper(import.name.canonicalize());
                    self.errors.push(NameError::Unbound(ident));
                    continue;
                }
            };
            if import.imports.is_empty() {
                self.import_globals(imported_m, imported_m.uid, |n| n.ident);
            } else {
                for import in import.get_imports() {
                    for ident in import.idents() {
                        self.declare_global(ident, uid);
                    }
                }
            }
        }
    }
}

#[inline]
fn identity<X>(x: X) -> X {
    x
}

#[cfg(test)]
mod tests {
    use super::*;
    use wy_parser as parser;

    #[test]
    fn test_renamer() {
        let src = include_str!("../../../../language/prim.wy");
        match parser::parse_input(src) {
            Err(e) => {
                println!("{}", e)
            },
            Ok(program) => {
                let mut renamer = Renamer::new();
                let mdl = &program.module;
                let modid = Ident::from(&mdl.modname);
                let _modname = renamer.make_unique(modid);
                renamer.import_globals(&program.module, Uid(0), identity);
                println!("{:?}", &renamer)
                
            },
        }
    }
}
