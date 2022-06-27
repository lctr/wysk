use std::{
    collections::HashMap,
    fmt::{self, Write},
};

///! Utilities predominantly used for *quick and dirty* pretty printing.

/// Takes a slice of printable items and a separator, printing out the
/// collection provided with the given separator in between each element.
///
/// # Example
/// ```rust
/// let list = vec![1, 2, 3, 4, 5];
/// println!("[{}]", Many(list.as_slice()), ',')
pub struct Many<'a, A, S>(pub &'a [A], pub S);

impl<'a, A, S> fmt::Display for Many<'a, A, S>
where
    A: fmt::Display,
    S: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0[..] {
            [] => Ok(()),
            [a] => A::fmt(a, f),
            [ref head, rest @ ..] => {
                let sep = &self.1;
                let init = A::fmt(head, f);
                rest.iter().fold(init, |_, c| {
                    S::fmt(sep, f)?;
                    A::fmt(c, f)?;
                    Ok(())
                })
            }
        }
    }
}

pub struct Slice<'a, A>(&'a [A], Option<usize>);
impl<'a, A> Slice<'a, A> {
    pub fn new(vec: &'a Vec<A>) -> Self {
        Self(vec.as_slice(), Some(vec.len()))
    }
}

pub enum Spacing<'a, A> {
    /// Around("x") -> ` x `
    Around(&'a A),
    /// Before("x") -> ` x`
    Before(&'a A),
    /// After("x") -> `x `
    After(&'a A),
    /// Block(["x", "y"]) -> `\n\tx\n\ty\n`
    /// Block([]) -> ``
    Block(usize, &'a [A]),
}

impl<'a, A: 'a> Spacing<'a, A> {
    pub fn spaces() -> std::iter::Repeat<char> {
        std::iter::repeat(' ')
    }
    pub fn indent(n: usize) -> std::iter::Take<std::iter::Repeat<char>> {
        Self::spaces().take(n)
    }
    pub fn write_spaces(n: usize, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Self::indent(n).try_fold((), |_, c| write!(f, "{}", c))
    }

    pub fn write_line_tab(n: usize, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\n")?;
        Self::write_spaces(n, f)
    }
}

impl<'a, A> fmt::Display for Spacing<'a, A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Spacing::Around(a) => write!(f, " {} ", a),
            Spacing::Before(a) => write!(f, " {}", a),
            Spacing::After(a) => write!(f, "{} ", a),
            Spacing::Block(n, aa) => {
                match aa {
                    [] => (),
                    [a] => {
                        Self::write_line_tab(*n, f)?;
                        write!(f, "{}", a)?;
                        Self::write_spaces(*n, f)?;
                    }
                    [a, bs @ ..] => {
                        Self::write_line_tab(*n, f)?;
                        write!(f, "{}", a)?;
                        for b in bs {
                            Self::write_line_tab(*n, f)?;
                            write!(f, "{}", b)?;
                        }
                        write!(f, "\n")?;
                    }
                }
                Ok(())
            }
        }
    }
}

/// Prints out a list of items, comma-separated and surrounded by square
/// brackets.
pub struct List<'a, A>(pub &'a [A]);

impl<'a, A> fmt::Display for List<'a, A>
where
    A: 'a + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        Many::fmt(&Many(&self.0, ", "), f)?;
        write!(f, "]")
    }
}

/// Prints out the internal item with optional parentheses if the second
/// component is greater than 0.
pub struct Parenthesized<'a, A>(pub &'a A, usize);

impl<'a, A> fmt::Display for Parenthesized<'a, A>
where
    A: 'a + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.1 == 0 {
            A::fmt(&self.0, f)
        } else {
            write!(f, "(")?;
            A::fmt(&self.0, f)?;
            write!(f, ")")
        }
    }
}

pub struct SepBy<'a, L, R, S>(pub &'a L, pub &'a R, pub S);

impl<'a, L, R, S> fmt::Debug for SepBy<'a, L, R, S>
where
    L: 'a + fmt::Debug,
    R: 'a + fmt::Debug,
    S: 'a + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        L::fmt(&self.0, f)?;
        <Spacing<'_, S> as fmt::Display>::fmt(&Spacing::After(&self.2), f)?;
        R::fmt(&self.1, f)
    }
}

impl<'a, L, R, S> fmt::Display for SepBy<'a, L, R, S>
where
    L: 'a + fmt::Display,
    R: 'a + fmt::Display,
    S: 'a + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        L::fmt(&self.0, f)?;
        S::fmt(&self.2, f)?;
        R::fmt(&self.1, f)
    }
}

macro_rules! debug_alt {
    ($f:ident, $($vars:ident)+, $reg:literal | #$alt:literal) => {{
        if $f.alternate() {
            write!($f, $alt, $($vars,)+)
        } else {
            write!($f, $reg, $($vars,)+)
        }
    }};
}

pub struct Record<'a, F: 'a, K: 'a, V: 'a>(pub &'a [(&'a F, &'a [(&'a K, &'a V)])]);

impl<'a, F, K, V> fmt::Display for Record<'a, F, K, V>
where
    F: 'a + fmt::Display,
    K: 'a + fmt::Display,
    V: 'a + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", '{')?;
        match &self.0 {
            [] => (),
            [(fld, kvs0), rest @ ..] => {
                write!(f, "\n    {}: {}", fld, Dict("=", kvs0))?;
                for (fld, kvs) in rest {
                    write!(f, ",\n    {}: {}", fld, Dict("=", kvs))?;
                }
                write!(f, "\n")?;
            }
        }
        write!(f, "{}", '}')
    }
}

impl<'a, F, K, V> fmt::Debug for Record<'a, F, K, V>
where
    F: 'a + fmt::Debug,
    K: 'a + fmt::Debug,
    V: 'a + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let dx = "    ";
        let Record(fields) = &self;
        write!(f, "{}", '{')?;
        match fields {
            [] => (),
            [(fld, kvs0), rest @ ..] => {
                let d0 = Dict(": ", kvs0);
                debug_alt!(f, dx fld d0, "\n{}{:?} {:?}" | #"{}{:?} {:#?}")?;
                // write!(f, "\n{}{:?} {:?}", dx, fld, Dict(": ", kvs0))?;
                for (fld, kvs) in rest {
                    let d0 = Dict(": ", kvs);
                    debug_alt!(f, dx fld d0, ",\n{}{:?} {:?}" | #",\n{}{:?} {:#?}")?;
                    // write!(f, ",\n{}{:?} {:?}", dx, fld, Dict(": ", kvs))?;
                }
                write!(f, "\n")?;
            }
        }
        write!(f, "{}", '}')
    }
}

pub struct Dict<'a, K: 'a, V: 'a>(pub &'a str, pub &'a [(K, V)]);

impl<'a, K: fmt::Debug, V: fmt::Debug> fmt::Debug for Dict<'a, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", '{')?;
        let sep = &self.0;
        match &self.1 {
            [] => (),
            [(k0, v0), rest @ ..] => {
                debug_alt!(f, k0 sep v0, "\n    {:?} {} {:?}" | #"\n    {:?} {} {:#?}")?;
                for (k, v) in rest {
                    debug_alt!(f, k sep v, ",\n    {:?} {} {:?}" | #",\n    {:?} {} {:#?}")?;
                }
                write!(f, "\n")?;
            }
        }
        write!(f, "{}", '}')
    }
}

pub struct Dictionary<'a, K, V>(pub &'a HashMap<K, V>);

impl<'a, K, V> fmt::Display for Dictionary<'a, K, V>
where
    K: fmt::Display,
    V: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let map = &self.0;
        f.write_char('{')?;
        match map.len() {
            0 => (),
            1 => {
                let (k, v) = map.into_iter().next().unwrap();
                write!(f, " {} = {} ", k, v)?;
            }
            _ => {
                let mut iter = map.into_iter();
                let (k0, v0) = iter.next().unwrap();
                write!(f, "\n    {} = {}", k0, v0)?;
                for (k, v) in iter {
                    write!(f, ",\n    {} = {}", k, v)?;
                }
                write!(f, "\n")?;
            }
        }
        f.write_char('}')
    }
}

impl<'a, K, V> fmt::Debug for Dictionary<'a, K, V>
where
    K: fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let map = &self.0;
        f.write_char('{')?;
        match map.len() {
            0 => (),
            1 => {
                let (k, v) = map.into_iter().next().unwrap();
                debug_alt!(f, k v, "\n    {:?} = {:?}" | #"{:?} = {:#?}")?;
            }
            _ => {
                let mut iter = map.into_iter();
                let (k0, v0) = iter.next().unwrap();
                debug_alt!(f, k0 v0, "\n    {:?} = {:?}" | #"{:?} = {:#?}")?;
                for (k, v) in iter {
                    debug_alt!(f, k v, ", {:?} = {:?}" | #"{:?} = {:#?}")?;
                }
                write!(f, "\n")?;
            }
        }
        f.write_char('}')
    }
}

impl<'a, K, V> fmt::Display for Dict<'a, K, V>
where
    K: 'a + fmt::Display,
    V: 'a + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_char('{')?;
        match self.1 {
            [] => (),
            [(k, v)] => {
                write!(f, " {} {} {} ", k, &self.0, v)?;
            }
            [(k0, v0), bs @ ..] => {
                let sp = "    ";
                write!(f, "\n")?;
                write!(f, "{}{} {} {}", sp, k0, &self.0, v0)?;
                for (k, v) in bs {
                    write!(f, ",\n{}{} {} {}", sp, k, &self.0, v)?;
                }
                write!(f, "\n")?;
            }
        }
        for (k, v) in self.1 {
            K::fmt(k, f)?;
            write!(f, " {} ", &self.0)?;
            V::fmt(v, f)?;
        }
        f.write_char('}')
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn print_many() {
        assert_eq!("1, 2, 3, 4", Many(&[1, 2, 3, 4], ", ").to_string());
        println!("[{}]", Many(&[1, 2, 3, 4], ", "));
        println!("{{{}}}", Spacing::Block(4, &[1, 2, 3, 4]))
    }
}
