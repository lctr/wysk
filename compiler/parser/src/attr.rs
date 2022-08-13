#![allow(unused)]
use wy_lexer::{
    meta::{Attr, Placement, Pragma},
    stream::Mode,
    Lexeme,
};
use wy_name::Ident;
use wy_syntax::attr::Attribute;

// use crate::error::Parsed;

use super::stream::*;

impl<'t> Parser<'t> {
    pub fn attribute_node(&mut self) {
        match self.lexer.get_mode() {
            Mode::Default => todo!(),
            Mode::Meta {
                place: _,
                attr_seen: _,
            } => {
                todo!()
                // self.pragma(*place)
            }
            Mode::Macro => todo!(),
        }
        // self.eat(Lexeme::BrackL)?;
    }
}
