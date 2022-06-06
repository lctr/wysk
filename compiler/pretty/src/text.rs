pub enum Text<'t> {
    Line,
    Str(&'t str),
}
