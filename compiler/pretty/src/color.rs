use serde::{Deserialize, Serialize};
use wy_span::Span;

#[allow(unused)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum AsciiColor {
    Black = 30,
    Red = 31,
    Green = 32,
    Yellow = 33,
    Blue = 34,
    Magenta = 35,
    Cyan = 36,
    White = 37,
    LightBlack = 90,
    LightRed = 91,
    LightGreen = 92,
    LightYellow = 93,
    LightBlue = 94,
    LightMagenta = 95,
    LightCyan = 96,
    LightWhite = 97,
    Default = 0,
}

impl Default for AsciiColor {
    fn default() -> Self {
        Self::Default
    }
}

macro_rules! impl_get_str {
    (
        $name:ident fg bg
        $(| $variant:ident $lit1:literal $lit2:literal)+
    ) => {
        impl $name {
            pub fn fg_val_str(&self) -> &str {
                match self {
                    $(Self::$variant => { stringify!($lit1) })+
                    // should variants provided be exhaustive? or should there
                    // be a default value?
                    // #[allow(unreachable_patterns)]
                    // _ => "0"
                }
            }
            pub fn bg_val_str(&self) -> &str {
                match self {
                    $(Self::$variant => { stringify!($lit2)} )+
                    // if keeping default value, setting it to same as `Default`
                    // variant
                    // #[allow(unreachable_patterns)]
                    // _ => "10"
                }
            }
        }
    };
}

impl_get_str! {
    AsciiColor fg bg
    | Black 30 40
    | Red 31 41
    | Green 32 42
    | Yellow 33 43
    | Blue 34 44
    | Magenta 35 45
    | Cyan 36 46
    | White 37 47
    | LightBlack 90 100
    | LightRed 91 101
    | LightGreen 92 102
    | LightYellow 93 103
    | LightBlue 94 104
    | LightMagenta 95 105
    | LightCyan 96 106
    | LightWhite 97 107
    | Default 0 10
}

impl AsciiColor {
    pub fn as_fg(&self) -> u8 {
        *self as u8
    }

    pub fn as_bg(&self) -> u8 {
        *self as u8 + 10
    }
}

#[derive(
    Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct RGB(u8, u8, u8);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(unused)]
pub enum Style {
    None,
    Fg(AsciiColor),
    Bg(AsciiColor),
    FgBg { fg: AsciiColor, bg: AsciiColor },
}

impl std::fmt::Display for Style {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Style::None => write!(f, "{:?}", self),
            Style::Fg(c) => write!(f, "Fg({:?})", c),
            Style::Bg(c) => write!(f, "Bg({:?})", c),
            Style::FgBg { fg, bg } => write!(f, "FgBg({:?}, {:?})", fg, bg),
        }
    }
}

impl Default for Style {
    fn default() -> Self {
        Self::None
    }
}

impl Style {
    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
    /// Modifies a provided string buffer in place, applying the given style to
    /// the `snip` string slice provided.
    pub fn write_str(&self, buf: &mut String, snip: &str) {
        match self {
            Style::None => {
                buf.push_str(snip);
            }
            Style::Fg(color) => {
                buf.push_str(COLOR_ESC[0]);
                buf.push_str(color.fg_val_str());
                buf.push_str(COLOR_ESC[1]);
                buf.push_str(snip);
                buf.push_str(COLOR_ESC[2]);
            }
            Style::Bg(color) => {
                buf.push_str(COLOR_ESC[0]);
                buf.push_str(color.bg_val_str());
                buf.push_str(COLOR_ESC[1]);
                buf.push_str(snip);
                buf.push_str(COLOR_ESC[2]);
            }
            Style::FgBg { fg, bg } => {
                buf.push_str(COLOR_ESC[0]);
                buf.push_str(bg.bg_val_str());
                buf.push_str(";");
                buf.push_str(fg.fg_val_str());
                buf.push_str(COLOR_ESC[1]);
                buf.push_str(snip);
                buf.push_str(COLOR_ESC[2]);
            }
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TextError {
    StyleBound {
        style: Style,
        bounds: Span,
        strlen: usize,
    },
}

impl std::fmt::Display for TextError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TextError::StyleBound { style, bounds: Span(start, end), strlen } => write!(f, "TextError: Style is out of bounds! The buffer string has a length of {} bytes, but the style `{}` has spans over the byte range {} .. {}.", strlen, style, start, end),
        }
    }
}

impl std::error::Error for TextError {}

/// Bases used in constructing colored text.
pub const COLOR_ESC: [&'static str; 3] = ["\u{1b}[0m\u{1b}[", ";15m", "\u{1b}[0m"];

type IoTxt = &'static str;

pub const RED_PARENS: [IoTxt; 2] = [
    concat!("\u{1b}[0m\u{1b}[", 31, ";15m", "(", "\u{1b}[0m"),
    concat!("\u{1b}[0m\u{1b}[", 31, ";15m", ")", "\u{1b}[0m"),
];

pub const RED_WHITE_NAME: IoTxt = concat!(
    "\u{1b}[0m\u{1b}[",
    31,
    ";15m",
    "(",
    "\u{1b}[0m",
    "Wysk",
    "\u{1b}[0m\u{1b}[",
    31,
    ";15m",
    ")",
    "\u{1b}[0m"
);

pub const BLUE_PROMPT_INPUT: IoTxt =
    concat!("\u{1b}[0m\u{1b}[", 34, ";15m", "<)", "\u{1b}[0m", ' ');

pub const RED_PROMPT_ERROR: IoTxt =
    concat!("\u{1b}[0m\u{1b}[", 91, ";15m", "Error!", "\u{1b}[0m", ' ');

pub const GREEN_PROMPT_OUT: IoTxt = concat!("\u{1b}[0m\u{1b}[", 32, ";15m", "(>", "\u{1b}[0m", ' ');

/// Strips a string of its ASCII color formatting. This is necessary when
/// looking to use dispay a string that may have been styled via `Debug`    .
pub fn strip_color(s: String) -> String {
    let mut stripped = String::new();
    let mut tmp = 0;
    while let Some(a) = (&s[tmp..]).find(COLOR_ESC[0]) {
        stripped.push_str(&s[tmp..a]);
        let a_after = a + COLOR_ESC[0].len();
        match (&s[a_after..]).find(COLOR_ESC[1]) {
            Some(b) => {
                let b_after = b + COLOR_ESC[1].len();
                match (&s[b_after..]).find(COLOR_ESC[2]) {
                    Some(c) => {
                        let c_after = c + COLOR_ESC[2].len();
                        stripped.push_str(&s[c..c_after]);
                        tmp = c_after;
                    }
                    None => {
                        stripped.push_str(&s[b_after..]);
                        break;
                    }
                }
            }
            None => {
                stripped.push_str(&s[a_after..]);
                break;
            }
        }
    }
    stripped
}

#[macro_export]
macro_rules! color {
    (fg $color:ident $string:expr) => {
        format!(
            "\u{1b}[0m\u{1b}[{};15m{}\u{1b}[0m",
            ($crate::color::AsciiColor::$color as u8),
            $string
        )
    };
    (bg $color:ident $string:expr) => {
        format!(
            "\u{1b}[0m\u{1b}[{};15m{}\u{1b}[0m",
            ($crate::color::AsciiColor::$color as u8) + 10,
            $string
        )
    };
    (wrap $color:ident [$start:expr, $end:expr] $body:expr) => {{
        use crate::color::AsciiColor::*;
        [color!(fg $color $start), $body,
        color!(fg $color $end)].concat()
    }};
    (each fg $($fg:ident $string:expr)+) => {{
        use $crate::color::AsciiColor::*;
        let mut s = vec![];

        s.push($(format!(
            "\u{1b}[0m\u{1b}[{};{};15m{}\u{1b}[0m",
            ($bg as u8) + 10,
            $fg as u8,
            $string
        ))+);
        s
    }};
    (each $((fg $fg:ident, bg $bg:ident) $string:expr)+) => {{
        use $crate::color::AsciiColor::*;
        let mut s = vec![];

        s.push($(format!(
            "\u{1b}[0m\u{1b}[{};{};15m{}\u{1b}[0m",
            ($bg as u8) + 10,
            $fg as u8,
            $string
        ))+);
        s
    }};
    (fg for $s:ident match $base:ident $($($ps:pat)+ => $fg:ident),+) => {{
        match $base {
            $($($ps)+ => {color!(fg $fg $s)}),+
            _ => color!(fg Yellow format!("{}", $s))
        }
    }};
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_strip_color() {
        let base = "Hello!";
        let green = color!(fg Green base);
        println!("(green) display: {}", &green);
        println!("(green) debug: {:?}", &green);
        let stripped = strip_color(green);
        println!("(stripped) display: {}", &stripped);
        println!("(stripped) debug: {:?}", &stripped);
    }
}
