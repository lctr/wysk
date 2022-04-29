use wy_intern::symbol::{self, Symbol};
use wy_span::Span;

//----COMMENTS-----------------------------------------------------

/// Comment kinds. Note that *all* line comments are preceded by `~~` unless
/// immediately followed by a special glyph indicating the flavor of doc
/// comment they correspond to. Block comments are wrapped between `~{` and `}
/// ~`, are *never* doc comments, and are generally less preferred than
/// multiple line comments.
///
/// The comment markers listed above are NOT included in the spans capturing
/// the content of the commented lines. Therefore, commented lines such as
/// ```wysk
/// ~~ this here is a thing
/// ~~ that I want to talk about
/// ```
/// would capture spans beginning with `this` for the first line and ending at
/// the `thing`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Comment {
    /// Line comments
    Line(Span),
    Block(Span),
    Doc {
        span: Span,
        linekind: LineKind,
    },
}

impl Comment {
    pub fn span(&self) -> Span {
        match self {
            Comment::Line(span)
            | Comment::Block(span)
            | Comment::Doc { span, .. } => *span,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum SyntaxId {
    /// Indicated either by no language identifier, or the identifiers `wysk`,
    /// or `doctest`,
    Wysk,
    /// Indicates embedded code is markdown;
    Markdown,
    /// Indicates embedded code is HTML; supported identifiers is `html`
    Html,
    /// Indicates embedded code is pure CSS; supported identifier is only `css`
    Css,
    /// Indicates embedded code is *vanilla* javascript, equivalent to wrapping
    /// the embedded code in HTML `<script>` `</script>` tags. The supported
    /// identifier
    Js,
    /// Indicates embedded code is JSON.
    Json,
    /// Indicates embedded code is TOML.
    Toml,
    Yaml,
    /// Indicates embedded code is LaTeX.
    LaTeX,
    Other(Symbol),
}

impl SyntaxId {
    pub fn from_str(s: impl AsRef<str>) -> Self {
        match s.as_ref().trim().to_ascii_lowercase().as_str() {
            "" | "wysk" | "doctest" => Self::Wysk,
            "md" | "markdown" => Self::Markdown,
            "html" | "htm" => Self::Html,
            "css" => Self::Css,
            "js" | "javascript" | "ecmascript" => Self::Js,
            "json" => Self::Json,
            "toml" => Self::Toml,
            "yaml" => Self::Yaml,
            "latex" | "tex" => Self::LaTeX,
            other => Self::Other(symbol::intern_once(other)),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum LineKind {
    /// Non-processed line, i.e., for regular line and block comments
    /// typically wedged between otherwise continuous doc comments.
    Ignore,
    /// The first line of documentation for the code below it.
    /// These lines are marked by `~~>`. Comments are subject by default to
    /// markdown syntax.
    DocHead,
    /// These lines are marked by `~~|`. Comments are subject by default to
    /// markdown syntax.
    DocBody,
    /// Documents the code above it. These lines are marked by `~~:`. Comments
    /// are subject by default to markdown syntax.
    DocFoot,
    /// Comments meant to be parsed according to the language id listed, with
    /// `wysk` as the default in the absence of a language id.
    ///
    /// Note that unlike markdown, the line should begin with `~~<X>` for some
    /// language id `X`, followed by the code to be embedded and then closed
    /// with `~~;` *on a new line*, e.g.,
    /// ```wysk
    /// ~~> This a constant function with no arguments
    /// ~~| and is analogous to the following code in `Haskell``
    /// ~~<haskell>
    /// ~~| main :: IO ()
    /// ~~| main = ()
    /// ~~;
    /// ```
    /// ```wysk
    /// fn main :: IO () = ()
    /// ```
    Embeded(SyntaxId),
}

impl LineKind {
    #[inline]
    pub fn on_end_embed(c: char) -> bool {
        c == ';'
    }
    pub fn from_str(s: impl AsRef<str>) -> Self {
        let flag = s.as_ref();
        if flag.starts_with('>') {
            Self::DocHead
        } else if flag.starts_with('|') {
            Self::DocBody
        } else if flag.starts_with(':') {
            Self::DocFoot
        } else if flag.starts_with('<') && flag.ends_with('>') && flag.len() > 2
        {
            Self::Embeded(SyntaxId::from_str(&flag[1..flag.len() - 1]))
        } else {
            Self::Ignore
        }
    }
}
