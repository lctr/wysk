///! Utilities predominantly used for *quick and dirty* pretty printing.

/// Takes a slice of printable items and a separator, printing out the
/// collection provided with the given separator in between each element.
///
/// # Example
/// ```rust
/// let list = vec![1, 2, 3, 4, 5];
/// println!("[{}]", Many(list.as_slice()), ',')
pub struct Many<'a, A, S>(pub &'a [A], pub S);

impl<'a, A, S> std::fmt::Display for Many<'a, A, S>
where
    A: std::fmt::Display,
    S: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

/// Prints out a list of items, comma-separated and surrounded by square
/// brackets.
pub struct List<'a, A>(pub &'a [A]);

impl<'a, A> std::fmt::Display for List<'a, A>
where
    A: 'a + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        Many::fmt(&Many(&self.0, ", "), f)?;
        write!(f, "]")
    }
}

/// Prints out the internal item with optional parentheses if the second
/// component is greater than 0.
pub struct Parenthesized<'a, A>(pub &'a A, usize);

impl<'a, A> std::fmt::Display for Parenthesized<'a, A>
where
    A: 'a + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.1 == 0 {
            A::fmt(&self.0, f)
        } else {
            write!(f, "(")?;
            A::fmt(&self.0, f)?;
            write!(f, ")")
        }
    }
}

pub struct SepBy<'a, A, B, S>(pub &'a A, pub &'a B, pub S);

impl<'a, A, B, S> std::fmt::Display for SepBy<'a, A, B, S>
where
    A: 'a + std::fmt::Display,
    B: 'a + std::fmt::Display,
    S: 'a + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        A::fmt(&self.0, f)?;
        S::fmt(&self.2, f)?;
        B::fmt(&self.1, f)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn print_many() {
        println!("[{}]", Many(&[1, 2, 3, 4], ", "))
    }
}
