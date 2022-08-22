#[macro_export]
macro_rules! __force_expr_frag {
    ($e:expr) => {{
        $e
    }};
}

/// Same functionality as the std macro `matches!`, but with arguments reversed,
/// i.e., pattern then expression as opposed to expression and then pattern.
#[macro_export]
macro_rules! case {
    ($pat:pat, $expr:expr) => {{
        if let $pat = $expr {
            true
        } else {
            false
        }
    }};
}

/// Generates `.iter()` methods for the provided fields in a struct.
///
/// For example, a generic struct `Foo<X, Y>` with fields `bar` of type `Bar<X>`
/// and `baz` of type `Baz<Y>` would be implemented as following:
///
/// ```rust,ignore
/// use wy_common::struct_field_iters;
///
/// struct Bar<X>(X);
/// struct Baz<Y>(Y);
///
/// struct Foo<X, Y> {
///     bar: Vec<Bar<X>>,
///     baz: Baz<Y>,
/// }
///
/// struct_field_iters! {
///     |X, Y| Foo<X, Y>
///     | bar => get_bar :: Bar<X>
///     | baz => get_baz :: Baz<Y>
/// }
/// ```
#[macro_export]
macro_rules! struct_field_iters {
    (
        $(|$g0:ident $(, $gs:ident)*|)?
        $object:ty
        $(
           | $($($field:ident .)+)? # $rest:ident :: $ty:ty
        )+
    ) => {
        impl $(<$g0 $(, $gs)*>)? $object {
            $(
                #[inline]
                pub fn $rest(&self) -> std::slice::Iter<'_, $ty> {
                    self. $($($field .)+)? $rest.iter()
                }
            )+
        }
    };
    (
        $(|$g0:ident $(, $gs:ident)*|)?
        $object:ty
        $(
           | $field:ident $(. $rest:ident)* => $method_name:ident :: $ty:ty
        )+
    ) => {
        impl $(<$g0 $(, $gs)*>)? $object {
            $(
                #[inline]
                pub fn $method_name(&self) -> std::slice::Iter<'_, $ty> {
                    self.$field $(.$rest)* .iter()
                }
            )+
        }
    };
}

/// Generates an implementation of getters for the fields provided.
///
/// For example, a generic struct `Foo<X, Y>` with fields `bar` of type `Bar<X>`
/// and `baz` of type `Baz<Y>` would be implemented as following:
///
/// ```rust,ignore
/// struct Foo<X, Y> {
///     bar: Bar<X>,
///     baz: Baz<Y>,
/// }
///
/// struct_getters! {
///     |X, Y| Foo<X, Y>
///     | bar => get_bar :: Bar<X>
///     | baz => get_baz :: Baz<Y>
/// }
/// ```
#[macro_export]
macro_rules! struct_getters {
    (
        $(|$g0:ident $(, $gs:ident)*|)?
        $object:ty
        $(
           | $($($field:ident.)+)? # $rest:ident :: $ty:ty
        )+
    ) => {
        impl $(<$g0 $(, $gs)*>)? $object {
            $(
                #[inline]
                pub fn $rest(&self) -> &$ty {
                    &self. $($($field.)+)? $rest
                }
            )+
        }
    };
    (
        $(|$g0:ident $(, $gs:ident)*|)?
        $object:ty
        $(
           | $field:ident $(. $rest:ident)* => $method_name:ident :: $ty:ty
        )+
    ) => {
        impl $(<$g0 $(, $gs)*>)? $object {
            $(
                #[inline]
                pub fn $method_name(&self) -> &$ty {
                    &self.$field $(.$rest)*
                }
            )+
        }
    };
}

/// Generating predicates for a given enum to test for variants.
///
/// # Example
/// ```
/// use wy_common::variant_preds;
///
/// enum Foo<X, Y> {
///     Bar,
///     Baz { baz: X, count: usize },
///     Barbaz(X, Y)
/// }
///
/// variant_preds! {
///     |X, Y| Foo[X, Y]
///     | is_bar => Bar
///     | is_baz => Baz {..}
///     | is_barbaz => Barbaz (..)
///     | is_baz_with_count_zero => Baz { count: 0, .. }
///     | is_baz_with_even_count => Baz { count, .. } [if count % 2 == 0]
/// }
/// ```
#[macro_export]
macro_rules! variant_preds {
    (
        $(|$g0:ident $(, $gs:ident)*|)?
        $name:ident $([$($gss:tt)+])?
        $(
            $($(#[$com:meta])+)?
            | $method:ident => $variant:ident
                // really bad hack to get all shapes of enum variants
                $(($($args:tt)*))?
                $({ $($fields:tt)+ })?
                $([$($ts:tt)+])?
        )+
    ) => {
        impl $(<$g0 $(, $gs)*>)? $name $(<$($gss)+>)? {
            $(
                $($(#[$com])+)?
                #[inline]
                pub fn $method(&self) -> bool {
                    matches!(
                        self,
                        Self::$variant $(($($args)*))? $({ $($fields)+ })? $($($ts)+)?)
                }
            )+
        }
    };
}

#[macro_export]
macro_rules! poison_error {
    (
        #error = $error:expr;
        #msg = $custom_msg:expr
        $(; #query = $query:expr)? $(;)?
    ) => {{
        let error = $error;
        let custom_msg = $custom_msg;
        eprintln!("Poison error while {custom_msg}");
        $(let query = $query;
        eprint!(" `{query:?}`");)?
        panic!("{}", error)
    }};
    (
        $error:ident,
        $custom_msg:literal
        $(, $query:expr)?
    ) => {{
        $crate::poison_error! {
            #error = $error;
            #msg = $custom_msg;
            $(#query = $query)?
        }
    }};
}
