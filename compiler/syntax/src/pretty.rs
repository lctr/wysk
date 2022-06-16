use wy_common::{deque, Deque};
use wy_intern::{Symbol, Symbolic};
use wy_lexer::Literal;
use wy_name::ident::{Chain, Ident};

use crate::{
    expr::Expression,
    pattern::Pattern,
    stmt::{Alternative, Binding, Match, Statement},
    tipo::{Signature, Type},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Text<'t> {
    Empty,
    Line,
    Tab,
    Space,
    Var(u32),
    Sym(Symbol),
    Lit(&'t Literal),
    Raw(&'t str),
    Concat(Deque<Self>),
    List(Vec<Self>),
    Pair(Vec<Self>),
    Dict(Vec<Self>),
    Block(Vec<Self>),
    Group(Box<Self>),
    Prefix {
        affix: Symbol,
        body: Box<Text<'t>>,
    },
    Suffix {
        affix: Symbol,
        body: Box<Text<'t>>,
    },
    Infix {
        left: Box<Text<'t>>,
        infix: Symbol,
        right: Box<Text<'t>>,
    },
    Join {
        sep: &'t str,
        space: bool,
        head: Box<Self>,
        tail: Vec<Self>,
    },
    Indent {
        offset: Offset,
        lines: Vec<Self>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Offset(usize);

impl std::ops::Add for Offset {
    type Output = Offset;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl std::ops::Add<usize> for Offset {
    type Output = Offset;

    fn add(self, rhs: usize) -> Self::Output {
        Self(self.0 + rhs)
    }
}

impl std::ops::AddAssign for Offset {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl std::ops::AddAssign<usize> for Offset {
    fn add_assign(&mut self, rhs: usize) {
        self.0 += rhs;
    }
}

impl std::ops::AddAssign<Offset> for usize {
    fn add_assign(&mut self, rhs: Offset) {
        *self += rhs.0;
    }
}

impl Default for Offset {
    fn default() -> Self {
        Self(0)
    }
}

impl Offset {
    pub fn new(indent: usize) -> Self {
        Self(indent)
    }

    pub fn spread<'t>(
        &'t self,
        items: impl Iterator<Item = Text<'t>>,
    ) -> impl Iterator<Item = Text<'t>> {
        items.map(|text| Text::Indent {
            offset: *self,
            lines: vec![text],
        })
    }

    pub fn write_str(&self, buf: &mut String) {
        for _ in 0..self.0 {
            buf.push(' ');
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Delims {
    Nada,
    Pair,
    List,
    Dict,
    Space,
}

impl std::ops::Index<usize> for Delims {
    type Output = str;

    fn index(&self, index: usize) -> &Self::Output {
        let even = index % 2 == 0;
        let f = |x, y| if even { x } else { y };
        match self {
            Delims::Nada => "",
            Delims::Pair => f("(", ")"),
            Delims::List => f("[", "]"),
            Delims::Dict => f("{", "}"),
            Delims::Space => " ",
        }
    }
}

impl<'t> std::ops::Index<(&[Text<'t>], &mut String)> for Delims {
    type Output = ();

    fn index(&self, (texts, buf): (&[Text<'t>], &mut String)) -> &Self::Output {
        let [a, b] = match self {
            Delims::Nada => ["", ""],
            Delims::Pair => ["(", ")"],
            Delims::List => ["[", "]"],
            Delims::Dict if !texts.into_iter().next().is_some() => ["{ ", " }"],
            Delims::Dict => ["{", "}"],
            Delims::Space => [" ", " "],
        };
        buf.push_str(a);
        match texts {
            [] => (),
            [x] => {
                buf.push(' ');
                x.push_to(buf);
                buf.push(' ');
            }
            [x, xs @ ..] => {
                x.push_to(buf);
                for x in xs {
                    buf.push_str(", ");
                    x.push_to(buf);
                }
            }
        }
        buf.push_str(b);
        &()
    }
}

impl Delims {
    pub fn surround(self, texts: &[Text], buf: &mut String) {
        self[(texts, buf)]
    }
}

impl<'t> Text<'t> {
    fn boundary(&self) -> Delims {
        fn around_space(sep: &str) -> bool {
            sep.starts_with(|c: char| c.is_whitespace())
                || sep.ends_with(|c: char| c.is_whitespace())
        }
        match self {
            Self::Pair(..) => Delims::Pair,
            Self::List(..) => Delims::List,
            Self::Dict(..) => Delims::Dict,
            Self::Block(..) => Delims::Dict,
            Self::Concat(..) => Delims::Nada,
            Self::Join {
                space: true, sep, ..
            } if !around_space(*sep) => Delims::Space,
            _ => Delims::Nada,
        }
    }
    pub fn push_to(&self, buf: &mut String) {
        match self {
            Text::Empty => (),
            Text::Line => buf.push('\n'),
            Text::Tab => buf.push_str("    "),
            Text::Space => buf.push(' '),
            Text::Var(n) => wy_common::text::write_display_var(*n, buf),
            Text::Sym(s) => s.write_str(buf),
            Text::Lit(l) => buf.push_str(&*format!("{}", l)),
            Text::Raw(s) => buf.push_str(*s),
            Text::Concat(ss) => ss.into_iter().for_each(|text| text.push_to(buf)),
            Text::Pair(ts) | Text::List(ts) | Text::Dict(ts) => {
                self.boundary().surround(ts.as_slice(), buf)
            }
            Text::Group(t) => {
                buf.push('(');
                t.push_to(buf);
                buf.push(')');
            }
            Text::Block(ts) => {
                buf.push('{');
                match ts.as_slice() {
                    [] => (),
                    [a] => {
                        buf.push(' ');
                        a.push_to(buf);
                        buf.push(' ');
                    }
                    [a, bs @ ..] => {
                        a.push_to(buf);
                        for b in bs {
                            b.push_to(buf);
                            buf.push_str("; ");
                        }
                    }
                }
                buf.push('}');
            }
            Text::Prefix { affix, body } => {
                buf.push_str(affix.display().as_str());
                body.push_to(buf);
            }
            Text::Suffix { affix, body } => {
                body.push_to(buf);
                buf.push_str(affix.display().as_str());
            }
            Text::Infix { left, infix, right } => {
                left.push_to(buf);
                buf.push(' ');
                buf.push_str(infix.display().as_str());
                buf.push(' ');
                right.push_to(buf);
            }
            Text::Join {
                sep,
                space,
                head,
                tail,
            } => {
                head.push_to(buf);
                for t in tail {
                    if *space {
                        buf.push(' ');
                        buf.push_str(*sep);
                        buf.push(' ');
                    } else {
                        buf.push_str(*sep);
                    }
                    t.push_to(buf);
                }
            }
            Text::Indent { offset, lines } => {
                let offset = *offset
                    + buf
                        .as_str()
                        .lines()
                        .last()
                        .map(|s| s.len())
                        .unwrap_or_else(|| 0);
                match &lines[..] {
                    [] => (),
                    [x, xs @ ..] => {
                        x.push_to(buf);
                        for line in xs {
                            buf.push('\n');
                            offset.write_str(buf);
                            line.push_to(buf);
                        }
                    }
                }
            }
        }
    }

    pub fn display(&self) -> String {
        let mut s = String::new();
        self.push_to(&mut s);
        s
    }

    pub fn fmt_with(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buf = String::new();
        self.push_to(&mut buf);
        write!(f, "{}", buf)
    }
}

impl std::fmt::Display for Text<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_with(f)
    }
}

pub trait AsText {
    fn text(&self) -> Text;
    fn write_text(&self, buf: &mut String) {
        self.text().push_to(buf)
    }
}

impl AsText for Ident {
    fn text(&self) -> Text {
        Text::Sym(self.get_symbol())
    }
}

impl<Id> AsText for Chain<Id>
where
    Id: AsText,
{
    fn text(&self) -> Text {
        Text::Join {
            sep: ".",
            space: false,
            head: Box::new(self.root().text()),
            tail: self.tail().map(AsText::text).collect(),
        }
    }
}

impl<Id, T> AsText for Expression<Id, T>
where
    Id: Symbolic,
    T: std::fmt::Display,
{
    fn text(&self) -> Text {
        use crate::expr::Section;
        match self {
            Expression::Ident(id) => Text::Var(id.get_symbol().as_u32()),
            Expression::Path(id, ids) => Text::Join {
                sep: ".",
                space: false,
                head: Box::new(Text::Sym(id.get_symbol())),
                tail: ids
                    .into_iter()
                    .map(|i| Text::Var(i.get_symbol().as_u32()))
                    .collect(),
            },
            Expression::Lit(lit) => Text::Lit(lit),
            Expression::Neg(x) => Text::Concat(deque![Text::Raw("-"), x.text()]),
            Expression::Infix { infix, left, right } => Text::Infix {
                left: Box::new(left.text()),
                infix: infix.get_symbol(),
                right: Box::new(right.text()),
            },
            Expression::Section(sec) => match sec {
                Section::Prefix { prefix, right } => Text::Prefix {
                    affix: prefix.get_symbol(),
                    body: Box::new(right.text()),
                },
                Section::Suffix { left, suffix } => Text::Suffix {
                    body: Box::new(left.text()),
                    affix: suffix.get_symbol(),
                },
            },
            Expression::Tuple(ts) => Text::Pair(ts.into_iter().map(|x| x.text()).collect()),
            Expression::Array(ts) => Text::List(ts.into_iter().map(|x| x.text()).collect()),
            Expression::List(head, stmts) => Text::List(vec![Text::Join {
                sep: "|",
                space: true,
                head: Box::new(head.text()),
                tail: stmts.into_iter().map(|s| s.text()).collect(),
            }]),
            Expression::Dict(_) => todo!(),
            Expression::Lambda(p, x) => {
                let mut texts = deque![];
                texts.push_front(Text::Raw("\\"));
                texts.push_back(p.text());
                texts.push_back(Text::Space);
                let mut tmp = x.as_ref();
                while let Expression::Lambda(p, xt) = tmp {
                    texts.push_back(p.text());
                    tmp = xt.as_ref();
                }
                texts.push_back(Text::Raw(" -> "));
                texts.push_back(tmp.text());
                Text::Group(Box::new(Text::Concat(texts)))
            }
            Expression::Let(bs, x) => Text::Concat(
                std::iter::once(Text::Raw("let "))
                    .chain(bs.into_iter().map(|b| b.text()))
                    .chain([Text::Raw(" in "), x.text()])
                    .collect(),
            ),
            Expression::App(app, arg) => Text::Join {
                sep: " ",
                space: false,
                head: Box::new(app.text()),
                tail: vec![arg.text()],
            },
            Expression::Cond(xyz) => {
                let [x, y, z] = xyz.as_ref();
                Text::Concat(deque![
                    Text::Raw("if "),
                    x.text(),
                    Text::Raw(" then "),
                    y.text(),
                    Text::Raw(" else "),
                    z.text()
                ])
            }
            Expression::Case(_, _) => todo!(),
            Expression::Cast(x, t) => Text::Group(Box::new(Text::Join {
                sep: "::",
                space: true,
                head: Box::new(x.text()),
                tail: vec![t.text()],
            })),
            Expression::Do(stmts, ex) => Text::Block(
                stmts
                    .into_iter()
                    .map(|st| st.text())
                    .chain([ex.text()])
                    .collect(),
            ),
            Expression::Range(a, b) => Text::List(vec![Text::Join {
                sep: "..",
                space: true,
                head: Box::new(a.text()),
                tail: vec![b.as_ref().map(|x| x.text()).unwrap_or_else(|| Text::Empty)],
            }]),
            Expression::Group(x) => Text::Group(Box::new(x.text())),
        }
    }
}

impl<Id: Symbolic, T: std::fmt::Display> AsText for Type<Id, T> {
    fn text(&self) -> Text {
        todo!()
    }
}

impl<Id: Symbolic, T: std::fmt::Display> AsText for Pattern<Id, T> {
    fn text(&self) -> Text {
        todo!()
    }
}

impl<Id: Symbolic, T: std::fmt::Display> AsText for Statement<Id, T> {
    fn text(&self) -> Text {
        match self {
            Statement::Generator(pat, exp) => Text::Join {
                sep: "<-",
                space: true,
                head: Box::new(pat.text()),
                tail: vec![exp.text()],
            },
            Statement::Predicate(x) => x.text(),
            Statement::JustLet(binds) => Text::Concat(
                std::iter::once(Text::Raw("let "))
                    .chain(binds.into_iter().map(|b| b.text()))
                    .collect(),
            ),
        }
    }
}

impl<Id: Symbolic, T: std::fmt::Display> AsText for Binding<Id, T> {
    fn text(&self) -> Text {
        let name = || Text::Var(self.name.get_symbol().as_u32());
        let arms = self.arms_iter().map(|m| m.text());
        let fst = self
            .tipo
            .as_ref()
            .map(|s| Text::Join {
                sep: "::",
                space: true,
                head: Box::new(name()),
                tail: vec![s.text()],
            })
            .unwrap_or_else(|| name());
        Text::Join {
            sep: "|",
            space: true,
            head: Box::new(fst),
            tail: arms.collect(),
        }
    }
}

impl<Id: Symbolic, T: std::fmt::Display> AsText for Match<Id, T> {
    fn text(&self) -> Text {
        todo!()
    }
}

impl<Id: Symbolic, T: std::fmt::Display> AsText for Alternative<Id, T> {
    fn text(&self) -> Text {
        todo!()
    }
}

impl<Id: Symbolic, T: std::fmt::Display> AsText for Signature<Id, T> {
    fn text(&self) -> Text {
        todo!()
    }
}

impl AsText for str {
    fn text(&self) -> Text {
        Text::Raw(self)
    }
}

impl AsText for String {
    fn text(&self) -> Text {
        Text::Raw(self.as_str())
    }
}

#[cfg(test)]
mod test {
    use wy_common::{deque, Mappable};

    use super::*;

    #[test]
    fn test_text() {
        let [a, b, c] = wy_intern::intern_many(["a", "b", "c"]);
        let x = Text::List(vec![Text::Indent {
            offset: Offset(0),
            lines: vec![
                Text::Lit(&Literal::Int(0)),
                Text::Lit(&Literal::Char('x')),
                Text::Raw("() -> ()"),
                Text::Dict(vec![
                    Text::Sym(a),
                    Text::Pair(vec![Text::Sym(b), Text::Sym(c)]),
                ]),
            ],
        }]);
        println!("{}", x);
        let [a, b, c] = wy_intern::intern_many(["A", "B", "C"]).fmap(Ident::Upper);
        println!("{}", Chain::new(a, deque![b, c]).text())
    }
}
