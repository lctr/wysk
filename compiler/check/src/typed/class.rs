use wy_common::iter::Envr;
use wy_name::ident::Ident;

use super::constraint::Type;

#[derive(Debug)]
pub enum ClassError {
    ClassExists(Ident),
    MissingSuperclass {
        given_class: Ident,
        instances: Vec<Inst>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Qual<T> {
    preds: Vec<Pred>,
    head: T,
}

wy_common::struct_field_iters! {|T| Qual<T> | preds => predicates :: Pred }
wy_common::struct_getters! { |T| Qual<T> | head => head :: T }

impl<T> std::fmt::Display for Qual<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.preds.is_empty() {
            write!(f, "|{}| ", wy_common::pretty::Many(&self.preds[..], ", "))?;
        };
        write!(f, "{}", &self.head)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pred {
    class_name: Ident,
    member: Type,
}

impl Pred {
    pub fn new(class_name: Ident, member: Type) -> Self {
        Self { class_name, member }
    }
}

wy_common::struct_getters! {
    Pred
    | class_name => class_name :: Ident
    | member => member_ty :: Type
}

impl std::fmt::Display for Pred {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", &self.class_name, &self.member)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Class {
    parents: Vec<Ident>,
    instances: Vec<Inst>,
    methods: Vec<Ident>,
}

wy_common::struct_field_iters! { Class
    | #parents :: Ident
    | #instances :: Inst
    | #methods :: Ident
}

impl Class {
    pub fn new(parents: Vec<Ident>, instances: Vec<Inst>, methods: Vec<Ident>) -> Self {
        Self {
            parents,
            instances,
            methods,
        }
    }
    pub fn has_superclass(&self, class_name: &Ident) -> bool {
        self.parents.contains(class_name)
    }
    pub fn has_instance(&self, instance: &Inst) -> bool {
        self.instances.contains(instance)
    }
    pub fn has_method(&self, method: &Ident) -> bool {
        self.methods.contains(method)
    }
}

impl std::fmt::Display for Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Class {}\n    parents: {},\n    instances: {}\n,    members: {}\n{}",
            '{',
            wy_common::pretty::List(&self.parents[..]),
            wy_common::pretty::List(&self.instances[..]),
            wy_common::pretty::List(&self.methods[..]),
            '}'
        )
    }
}

pub type Inst = Qual<Pred>;

#[derive(Clone, Debug)]
pub struct ClassEnv {
    classes: Envr<Ident, Class>,
}

impl ClassEnv {
    pub fn new() -> Self {
        Self {
            classes: Envr::new(),
        }
    }
    pub fn has_class(&self, class_name: &Ident) -> bool {
        self.classes.contains_key(class_name)
    }
    pub fn get_class(&self, class_name: &Ident) -> Option<&Class> {
        self.classes.get(class_name)
    }
    pub fn add_class(&mut self, class_name: Ident, class: Class) -> Result<(), ClassError> {
        if self.has_class(&class_name) {
            return Err(ClassError::ClassExists(class_name));
        }
        let mut missing = vec![];
        for inst in class.instances() {
            for pred in inst.predicates() {
                if !self.has_class(pred.class_name()) {
                    missing.push(inst.clone());
                }
            }
        }
        if missing.is_empty() {
            self.classes.insert(class_name, class);
            Ok(())
        } else {
            Err(ClassError::MissingSuperclass {
                given_class: class_name,
                instances: missing,
            })
        }
    }
    pub fn superclasses_of(&self, class_name: &Ident) -> Option<&[Ident]> {
        self.classes.get(class_name).map(|cl| &cl.parents[..])
    }
    pub fn instances_of(&self, class_name: &Ident) -> Option<&[Inst]> {
        self.classes.get(class_name).map(|cl| &cl.instances[..])
    }
    pub fn methods_of(&self, class_name: &Ident) -> Option<&[Ident]> {
        self.classes.get(class_name).map(|cl| &cl.methods[..])
    }
    pub fn with_core_classes() -> Self {
        let mut env = Self::new();
        add_core_classes(&mut env).unwrap();
        env
    }
}

impl std::fmt::Display for ClassEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ClassEnv {}",
            wy_common::pretty::Dictionary(&self.classes)
        )
    }
}

pub fn add_core_classes(class_env: &mut ClassEnv) -> Result<(), ClassError> {
    // class names
    let [eq, ord, show, read, enum_, num, add, sub, mul, div, functor, applicative, monad] =
        wy_intern::intern_many_with(
            [
                "Eq",
                "Ord",
                "Show",
                "Read",
                "Enum",
                "Num",
                "Add",
                "Sub",
                "Mul",
                "Div",
                "Functor",
                "Applicative",
                "Monad",
            ],
            Ident::Upper,
        );
    // non-infix methods
    let [compare, show_, read_, succ, pred, into_enum, from_enum, enum_from, enum_from_then, enum_from_to, enum_from_then_to, abs, negate, signum, from_int, into_int, from_integer, integer_from, map, embed, lift_a2, unit] =
        wy_intern::intern_many_with(
            [
                // Ord
                "compare",
                // Show
                "show",
                // Read
                "read",
                // Enum
                "succ",
                "pred",
                "intoEnum",
                "fromEnum",
                "enumFrom",
                "enumFromThen",
                "enumFromTo",
                "enumFromThenTo",
                // Num
                "abs",
                "negate",
                "signum",
                "fromInt",
                "intoInt",
                "fromInteger",
                "integerFrom",
                // Functor
                "map",
                // Applicative
                "embed",
                "liftA2",
                // Monad
                "unit",
            ],
            Ident::Lower,
        );
    // infix methods
    let [equals, lt, gt, add_, sub_, mul_, div_, overwrite, aps, ap_r, ap_l, bind] =
        wy_intern::intern_many_with(
            [
                // Eq
                "==", // Ord
                "<", ">", // Add, Sub, Mul, Div
                "+", "-", "*", "/",  // Functor
                "/>", // Applicative
                "<*>", "*>", "<*", // Monad
                ">>=",
            ],
            Ident::Infix,
        );

    let base_classes = [
        (eq, vec![], vec![equals]),
        (ord, vec![eq], vec![compare, lt, gt]),
        (show, vec![], vec![show_]),
        (read, vec![], vec![read_]),
        (
            enum_,
            vec![],
            vec![
                succ,
                pred,
                into_enum,
                from_enum,
                enum_from,
                enum_from_then,
                enum_from_to,
                enum_from_then_to,
            ],
        ),
        (
            num,
            vec![],
            vec![
                abs,
                negate,
                signum,
                from_int,
                into_int,
                from_integer,
                integer_from,
            ],
        ),
        (add, vec![num], vec![add_]),
        (sub, vec![num], vec![sub_]),
        (mul, vec![num], vec![mul_]),
        (div, vec![num], vec![div_]),
        (functor, vec![], vec![map, overwrite]),
        (
            applicative,
            vec![functor],
            vec![embed, aps, ap_r, ap_l, lift_a2],
        ),
        (monad, vec![applicative], vec![unit, bind]),
    ];

    for (class_name, parents, methods) in base_classes {
        class_env.add_class(
            class_name,
            Class {
                parents,
                instances: vec![],
                methods,
            },
        )?;
    }

    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn load_core_classes() {
        let mut class_env = ClassEnv::new();
        add_core_classes(&mut class_env).unwrap();
        println!("{}", &class_env)
    }
}
