use serde::{Deserialize, Serialize};

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

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum AnsiFormat {
    Reset = 0,
    Bold = 1,
    Dim = 2,
    Italic = 3,
    Underlined = 4,
    Blinking = 5,
    Inverted = 7,
    Hidden = 8,
    Strikethrough = 9,
}

impl AnsiFormat {
    pub fn reset_val(&self) -> &str {
        match self {
            AnsiFormat::Reset => "",
            AnsiFormat::Bold => "22",
            AnsiFormat::Dim => "22",
            AnsiFormat::Italic => "23",
            AnsiFormat::Underlined => "24",
            AnsiFormat::Blinking => "25",
            AnsiFormat::Inverted => "27",
            AnsiFormat::Hidden => "28",
            AnsiFormat::Strikethrough => "29",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Style {
    reset_prev: bool,
    is_bold: bool,
    is_dim: bool,
    is_italic: bool,
    is_underlined: bool,
    is_blinking: bool,
    is_inverted: bool,
    is_hidden: bool,
    is_strikethrough: bool,
    fg_color: Option<AsciiColor>,
    bg_color: Option<AsciiColor>,
}

impl Default for Style {
    fn default() -> Self {
        Self {
            reset_prev: true,
            is_bold: false,
            is_dim: false,
            is_italic: false,
            is_underlined: false,
            is_blinking: false,
            is_inverted: false,
            is_hidden: false,
            is_strikethrough: false,
            fg_color: None,
            bg_color: None,
        }
    }
}

impl Style {
    pub fn codes(&self) -> Vec<u8> {
        let mut parts = vec![];
        if self.is_bold {
            parts.push(AnsiFormat::Bold as u8)
        }
        if self.is_dim {
            parts.push(AnsiFormat::Dim as u8)
        }
        if self.is_italic {
            parts.push(AnsiFormat::Italic as u8)
        }
        if self.is_underlined {
            parts.push(AnsiFormat::Underlined as u8)
        }
        if self.is_blinking {
            parts.push(AnsiFormat::Blinking as u8)
        }
        if self.is_inverted {
            parts.push(AnsiFormat::Inverted as u8)
        }
        if self.is_hidden {
            parts.push(AnsiFormat::Hidden as u8)
        }
        if self.is_strikethrough {
            parts.push(AnsiFormat::Strikethrough as u8)
        }
        if let Some(fg) = self.fg_color {
            parts.push(fg.as_fg())
        }
        if let Some(bg) = self.bg_color {
            parts.push(bg.as_bg())
        }
        parts
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct StyleBuilder(Style);

impl Default for StyleBuilder {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl StyleBuilder {
    pub fn new() -> Self {
        Self(Style::default())
    }
    pub fn set_bold(mut self, is_bold: bool) -> Self {
        self.0.is_bold = is_bold;
        self
    }
    pub fn set_dim(mut self, is_dim: bool) -> Self {
        self.0.is_dim = is_dim;
        self
    }
    pub fn set_italic(mut self, is_italic: bool) -> Self {
        self.0.is_italic = is_italic;
        self
    }
    pub fn set_blinking(mut self, is_blinking: bool) -> Self {
        self.0.is_blinking = is_blinking;
        self
    }
    pub fn set_inverted(mut self, is_inverted: bool) -> Self {
        self.0.is_inverted = is_inverted;
        self
    }
    pub fn set_hidden(mut self, is_hidden: bool) -> Self {
        self.0.is_hidden = is_hidden;
        self
    }
    pub fn set_strikethrough(mut self, is_strikethrough: bool) -> Self {
        self.0.is_strikethrough = is_strikethrough;
        self
    }
    pub fn set_fg_color(mut self, color: AsciiColor) -> Self {
        self.0.fg_color = Some(color);
        self
    }
    pub fn set_bg_color(mut self, color: AsciiColor) -> Self {
        self.0.bg_color = Some(color);
        self
    }
    pub fn build<S>(self, s: S) -> Styled<S> {
        Styled(self.0, s)
    }
}

pub struct Styled<S>(Style, S);

impl<S> Styled<Vec<S>> {
    pub fn apply_to_all(self) -> Vec<Styled<S>> {
        let style = self.0;
        self.1.into_iter().map(|s| Styled(style, s)).collect()
    }
}

impl<S> Styled<S> {
    pub fn modify_style(self, f: impl FnOnce(StyleBuilder) -> StyleBuilder) -> Self {
        let style = self.0;
        let mut styler = StyleBuilder::new();
        styler.0 = style;
        f(styler).build(self.1)
    }

    pub fn fmt_display(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
    where
        S: std::fmt::Display,
    {
        std::fmt::Display::fmt(self, f)
    }

    pub fn fmt_debug(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
    where
        S: std::fmt::Debug,
    {
        std::fmt::Debug::fmt(self, f)
    }
}

impl<S> std::fmt::Debug for Styled<S>
where
    S: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let parts = self.0.codes();
        let item = &self.1;
        match &parts[..] {
            [] => write!(f, "\u{1b}[0m{item:?}"),
            [a, bs @ ..] => {
                write!(f, "\u{1b}[{a}")?;
                for b in bs {
                    write!(f, ";{b}")?;
                }
                write!(f, "m{item:?}\u{1b}[0m")
            }
        }
    }
}

impl<S> std::fmt::Display for Styled<S>
where
    S: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let parts = self.0.codes();
        let item = &self.1;
        match &parts[..] {
            [] => write!(f, "\u{1b}[0m{item}"),
            [a, bs @ ..] => {
                write!(f, "\u{1b}[{a}")?;
                for b in bs {
                    write!(f, ";{b}")?;
                }
                write!(f, "m{item}\u{1b}[0m")
            }
        }
    }
}

#[macro_export]
macro_rules! color {
    (fg $color:ident $string:expr) => {
        $crate::color::StyleBuilder::new()
            .set_fg_color($crate::color::AsciiColor::$color)
            .build($string)
    };
    (bg $color:ident $string:expr) => {
        $crate::color::StyleBuilder::new()
            .set_bg_color($crate::color::AsciiColor::$color)
            .build($string)
    };
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn expect_bold_red_text() {
        let styled = StyleBuilder::new()
            .set_bold(true)
            .set_fg_color(AsciiColor::Red)
            .build("hello");
        println!("{styled}")
    }
}
