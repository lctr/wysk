#![allow(unused)]
use super::*;
use serde::{Deserialize, Serialize};
use visit::{Visit, VisitError, VisitMut};
use wy_intern::symbol;

use wy_lexer::{self, LexError};

/// Precedence are internally represented with values greater than declared in
/// source code, differing by 1. This not only implies that the minimum
/// precedence accepted -- written as 0 -- is *actually* 1, and the maximum --
/// written 9 -- is actually *10*. This is to give us the freedom to define
/// a precedence lower than defineable externally without having to rely on
/// negative numbers.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Prec(pub u8);

impl Prec {
    pub const ARROW: Self = Prec(0);
    pub const CONS: Self = Prec(6);
    pub const MIN: Self = Prec(1);
    pub const MAX: Self = Prec(10);
}

impl Default for Prec {
    fn default() -> Self {
        Self::MAX
    }
}

impl std::str::FromStr for Prec {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.parse::<u8>() {
            Ok(n) => {
                if n < 10 { Ok(Prec(n + 1)) } else { Err(format!("the number `{}` is not within the range of supported precedence values 0 <= prec <= 9", n))}
            }
            Err(e) => Err(format!(
                "the string `{}` is not a valid precedence value due to failure to parse as unsigned integer.\n >> {}", s, e)),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Assoc {
    Left,
    Right,
    None,
}

impl std::fmt::Display for Assoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Assoc::Left => "left-associative",
                Assoc::Right => "right-associative",
                Assoc::None => "not associative",
            }
        )
    }
}

impl Assoc {
    pub fn is_left(&self) -> bool {
        matches!(self, Self::Left)
    }
    pub fn is_right(&self) -> bool {
        matches!(self, Self::Right)
    }
    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
}

impl std::str::FromStr for Assoc {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let text = s.to_lowercase();
        match text.as_str() {
            "l" | "left" | "infixl" => Ok(Self::Left),
            "r" | "right" | "infixr" => Ok(Self::Right),
            "_" | "n" | "none" | "infix" => Ok(Self::None),
            s => Err(format!(
                "The string `{}` does not correspond to a supported infix associativity",
                s
            )),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Fixity {
    pub prec: Prec,
    pub assoc: Assoc,
}

impl Fixity {
    pub const MIN_PREC: Prec = Prec::MIN;
    pub const CONS: Self = Self {
        prec: Prec(5),
        assoc: Assoc::Right,
    };
}

impl Default for Fixity {
    fn default() -> Self {
        Self {
            prec: Prec(9),
            assoc: Assoc::Left,
        }
    }
}

impl From<(Prec, Assoc)> for Fixity {
    fn from((prec, assoc): (Prec, Assoc)) -> Self {
        Fixity { prec, assoc }
    }
}

impl From<(Assoc, Prec)> for Fixity {
    fn from((assoc, prec): (Assoc, Prec)) -> Self {
        Fixity { prec, assoc }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum FixityFail<Id = Ident> {
    AssocFail([(Id, Assoc); 2]),
    NoFixity(Id),
    NoLeftExpr,
    NoRightExpr,
    InfixesEmpty,
    Visit(VisitError),
}

impl<Id: std::fmt::Display> std::fmt::Display for FixityFail<Id> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Fixity error: ")?;
        match self {
            FixityFail::AssocFail([(i1, a1), (i2, a2)]) => write!(f, "mismatched infix associativities! The infix `{}` is `{}`, but the infix `{}` is `{}`", i1, a1, i2, a2),
            FixityFail::NoFixity(_) => todo!(),
            FixityFail::NoLeftExpr => write!(f, "Expression stack empty, but needed expression for left-hand side of (reconstituted) infix expression"),
            FixityFail::NoRightExpr => write!(f, "Expression stack empty, but needed expression for right-hand side of (reconstituted) infix expression"),
            FixityFail::InfixesEmpty => write!(f, "Infix stack empty, but needed infix to complete (reconstituted) infix expression"),
            FixityFail::Visit(err) => write!(f, "{}", err)
        }
    }
}

impl std::error::Error for FixityFail {}

/// Non-hashmap container for declared fixities.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Fixities<Id>(Vec<(Id, Fixity)>);
impl Default for Fixities<Ident> {
    fn default() -> Self {
        Self(vec![(Ident::COLON, Fixity::CONS)])
    }
}

impl<Id> Fixities<Id> {
    #[inline]
    pub fn contains_infix(&self, id: &Id) -> bool
    where
        Id: PartialEq,
    {
        self.iter().any(|(i, _)| i == id)
    }

    #[inline]
    pub fn contains_fixity(&self, id: &Id, fixity: &Fixity) -> bool
    where
        Id: PartialEq,
    {
        self.iter().any(|(i, fx)| i == id && fx == fixity)
    }

    #[inline]
    pub fn map<U>(self, mut f: impl FnMut(Id) -> U) -> Fixities<U> {
        self.0
            .into_iter()
            .map(|(id, fixity)| (f(id), fixity))
            .collect()
    }

    #[inline]
    pub fn into_table(self) -> FixityTable<Id>
    where
        Id: Eq + std::hash::Hash,
    {
        self.0.into_iter().collect()
    }

    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, (Id, Fixity)> {
        self.0.iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, (Id, Fixity)> {
        self.0.iter_mut()
    }
}

impl<Id> IntoIterator for Fixities<Id> {
    type Item = (Id, Fixity);

    type IntoIter = std::vec::IntoIter<(Id, Fixity)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<Id> FromIterator<(Id, Fixity)> for Fixities<Id> {
    fn from_iter<T: IntoIterator<Item = (Id, Fixity)>>(iter: T) -> Self {
        Fixities(iter.into_iter().collect::<Vec<_>>())
    }
}

impl<Id> From<FixityTable<Id>> for Fixities<Id> {
    fn from(table: FixityTable<Id>) -> Self {
        Self(table.into_iter().collect::<Vec<_>>())
    }
}

impl<Id> std::ops::Deref for Fixities<Id> {
    type Target = Vec<(Id, Fixity)>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug)]
pub struct FixityTable<Id = Ident>(pub HashMap<Id, Fixity>);

impl<Id> IntoIterator for FixityTable<Id> {
    type Item = (Id, Fixity);

    type IntoIter = std::collections::hash_map::IntoIter<Id, Fixity>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

pub type Infix = Ident;

impl<Id: Eq + std::hash::Hash> std::ops::Index<Id> for FixityTable<Id> {
    type Output = Fixity;

    fn index(&self, index: Id) -> &Self::Output {
        self.0.get(&index).unwrap_or_else(|| &Fixity {
            assoc: Assoc::Left,
            prec: Prec(9),
        })
    }
}

impl<Id> FixityTable<Id>
where
    Id: Eq + std::hash::Hash,
{
    pub fn new(mut infixify: impl FnMut(Symbol) -> Id) -> Self {
        let mut map = HashMap::new();
        map.insert(infixify(wy_intern::sym::COLON), Fixity::CONS);
        Self(map)
    }

    /// Converts the `FixityTable` into an instance of `Fixities`, containing
    /// the same data but backed by a vector instead of a hashmap.
    pub fn as_fixities(self) -> Fixities<Id> {
        self.0.into_iter().collect()
    }

    /// Returns default fixity (left, 9) if not found.
    pub fn get_fixity(&self, id: &Id) -> Fixity {
        self.0.get(id).copied().unwrap_or_default()
    }

    pub fn map<X: Eq + std::hash::Hash>(self, mut f: impl FnMut(Id) -> X) -> FixityTable<X> {
        FixityTable(
            self.0
                .into_iter()
                .map(|(id, fixity)| (f(id), fixity))
                .collect::<HashMap<_, _>>(),
        )
    }

    #[inline]
    pub fn iter(&self) -> std::collections::hash_map::Iter<'_, Id, Fixity> {
        self.0.iter()
    }

    /// Apply this fixity table's fixities to an expression, rearranging an
    /// `Infix` expression to adhere to the fixities defined.
    pub fn apply<T>(
        &mut self,
        mut expr: Box<Expression<Id, T>>,
    ) -> Result<Expression<Id, T>, FixityFail<Id>>
    where
        Id: Clone,
    {
        fn reduce<Op, B>(
            exprs: &mut Vec<Box<Expression<Op, B>>>,
            infixes: &mut Vec<Op>,
        ) -> Result<(), FixityFail<Op>> {
            assert!(exprs.len() >= 2);
            let infix = infixes.pop().ok_or(FixityFail::InfixesEmpty)?;
            let right = exprs.pop().ok_or(FixityFail::NoRightExpr)?;
            let left = exprs.pop().ok_or(FixityFail::NoLeftExpr)?;
            exprs.push(Box::new(Expression::Infix { infix, left, right }));
            Ok(())
        }

        let mut exprs = vec![];
        let mut ops = vec![];
        loop {
            match *expr {
                Expression::Infix { infix, left, right } => {
                    exprs.push(left);
                    expr = right;
                    loop {
                        match ops.last().cloned() {
                            Some(prev_op) => {
                                let Fixity {
                                    assoc: this_assoc,
                                    prec: this_prec,
                                } = self.get_fixity(&infix);
                                let Fixity {
                                    assoc: prev_assoc,
                                    prec: prev_prec,
                                } = self.get_fixity(&prev_op);
                                if this_prec > prev_prec {
                                    ops.push(infix);
                                    break;
                                } else if this_prec == prev_prec {
                                    match (this_assoc, prev_assoc) {
                                        (Assoc::Left, Assoc::Left) => {
                                            reduce(&mut exprs, &mut ops)?;
                                        }

                                        (Assoc::Right, Assoc::Right) => {
                                            // shift infix
                                            ops.push(infix);
                                            break;
                                        }
                                        (t_a, p_a) => {
                                            // TODO: what about mismatched associativities?
                                            // TODO: Error reporting!
                                            return Err(FixityFail::AssocFail([
                                                (infix, this_assoc),
                                                (prev_op, prev_assoc),
                                            ]));
                                        }
                                    }
                                } else {
                                    reduce(&mut exprs, &mut ops)?;
                                }
                            }
                            None => {
                                ops.push(infix);
                                break;
                            }
                        }
                    }
                }
                rhs => {
                    let mut result = rhs;
                    while ops.len() != 0 {
                        assert!(exprs.len() >= 1);
                        let lhs = exprs.pop().ok_or(FixityFail::NoLeftExpr)?;
                        let op = ops.pop().ok_or(FixityFail::InfixesEmpty)?;
                        result = Expression::Infix {
                            infix: op,
                            left: lhs,
                            right: Box::new(result),
                        };
                    }
                    return Ok(result);
                }
            }
        }
    }

    fn visit_expression<T>(&mut self, expr: &mut Expression<Id, T>) -> Result<(), FixityFail<Id>>
    where
        Id: Clone,
    {
        // walk_expr_mut(self, expr)
        // use visit::*;
        // Visitor(())
        //     .visit_expr_mut(expr)
        //     .map_err(FixityFail::Visit)?;

        if let Expression::Infix { .. } = expr {
            let mut temp = Expression::Tuple(vec![]);
            std::mem::swap(&mut temp, expr);
            temp = self.apply(Box::new(temp))?;
            std::mem::swap(&mut temp, expr);
        };

        Ok(())
    }
    fn visit_module(&mut self, module: &mut Module) {}
}

impl<Id> FromIterator<(Id, Fixity)> for FixityTable<Id>
where
    Id: Eq + std::hash::Hash,
{
    fn from_iter<T: IntoIterator<Item = (Id, Fixity)>>(iter: T) -> Self {
        Self(iter.into_iter().collect::<HashMap<Id, Fixity>>())
    }
}

// UTILS, PROBABLY TO BECOME STANDARDLY IMPLEMENTED
impl std::ops::Deref for FixityTable {
    type Target = HashMap<Ident, Fixity>;

    fn deref(&self) -> &Self::Target {
        &(self.0)
    }
}

impl std::ops::DerefMut for FixityTable {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut (self.0)
    }
}

impl<T> From<Ident> for Expression<Ident, T> {
    fn from(name: Ident) -> Self {
        Expression::Ident(name)
    }
}

#[cfg(test)]
mod tests {
    use wy_span::Dummy;

    use super::*;
    /// let's take a stab at reordering expressions based on fixities we will be
    /// using simple arithmetic operators, whose fixities are (to be) defined (and
    /// implicitly imported) in the Prelude.
    ///
    /// Recall that an algebraic field *F* is equipped with the following four
    /// arithmetic operations
    /// - `(+) => (Assoc::Left, Prec(5))`
    /// - `(-) => (Assoc::Left, Prec(5))`
    /// - `(*) => (Assoc::Left, Prec(6))`
    /// - `(/) => (Assoc::Left, Prec(6))`
    ///
    /// We will be testing the expression `a + b * (c - d)`
    ///
    ///
    /// | LABEL           | PARSED AS              |
    /// |-----------------|------------------------|
    /// | INITIAL         | `a + (b * (c - d))`    |
    /// | INITIAL AS SEXP | `(+ a (* b (- c d)))`  |
    /// | CORRECT         | `(a + b) * (c - d)`    |
    /// | CORRECT SEXP    | `(* (+ a b) (- c d))`  |
    ///
    #[test]
    fn test_fixity_correction() {
        let [a, b, c, d] = { map_array(symbol::intern_many(["a", "b", "c", "d"]), Ident::Lower) };
        let [plus, minus, times, div] =
            { map_array(symbol::intern_many(["+", "-", "*", "/"]), Ident::Infix) };
        let var = Expression::<Ident, Ident>::Ident;
        // a + b * c - d
        // (a + (b * (c - d)))
        let og_expr = ifx(var(a), plus, ifx(var(b), times, ifx(var(c), minus, var(d))));
        // (a + (b * c)) - d
        let want_expr = ifx(ifx(var(a), plus, ifx(var(b), times, var(c))), minus, var(d));

        // fixity decls for (+) and (-)
        let decls = [
            FixityDecl {
                span: Span::DUMMY,
                infixes: vec![plus, minus],
                fixity: Fixity {
                    assoc: Assoc::Left,
                    prec: Prec(6),
                },
                from_pragma: false,
            },
            FixityDecl {
                span: Span::DUMMY,
                infixes: vec![times, div],
                fixity: Fixity {
                    assoc: Assoc::Left,
                    prec: Prec(7),
                },
                from_pragma: false,
            },
        ];
        let mut fixities = FixityTable::from(&decls[..]);
        println!(
            "\
        raw:     `a + b * c - d`\n\
        parsed:  `(a + (b * (c - d)))`\n\
        correct: `((a + (b * c)) - d)`"
        );
        println!("original: {:#?}", &og_expr);
        println!("expected: {:#?}", &want_expr);
        assert_eq!(fixities.apply(Box::new(og_expr)), Ok(want_expr));
    }

    fn ifx(
        left: Expression<Ident, Ident>,
        infix: Ident,
        right: Expression<Ident, Ident>,
    ) -> Expression<Ident, Ident> {
        Expression::Infix {
            infix,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    fn map_array<F, X, Y, const K: usize>(array: [X; K], mut f: F) -> [Y; K]
    where
        F: FnMut(X) -> Y,
    {
        // this is safe since `out` is the same size as `array`, and we will be
        // replacing every element of `out` with `f` applied to each element of
        // `array`.
        let mut out: [Y; K] = unsafe { std::mem::zeroed() };
        let mut i = 0;
        for x in array {
            out[i] = f(x);
            i += 1;
        }
        out
    }
}
