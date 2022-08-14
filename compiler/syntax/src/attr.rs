use serde::{Deserialize, Serialize};

// use wy_intern::Symbol;

pub use wy_lexer::{
    comment::{CommentId, LineKind},
    meta::Placement,
    Token,
};

use wy_span::Span;

use crate::{fixity::Fixity, tipo::Type};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Pragma<Id, V> {
    pub span: Span,
    pub plmt: Placement,
    pub attr: Attribute<Id, V>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DocLine {
    pub id: CommentId,
    pub span: Span,
    pub line_kind: LineKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Attribute<Id, V> {
    Test,
    Todo,
    Inline,
    NoInline,
    Doc(DocLine),
    Fixity(Fixity),
    Derive(Vec<Id>),
    Specialize(Id, Vec<Type<Id, V>>),
    Custom(Id, Vec<Token>),
}
