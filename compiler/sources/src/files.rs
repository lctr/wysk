use std::sync::Arc;

use wy_span::{BytePos, Col, Coord, Location, Row, Span};

use crate::paths::{FileName, FilePath};

#[derive(Default, Debug)]
pub struct SourceMap {
    files: Vec<Arc<File>>,
}

impl SourceMap {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn end_pos(&self) -> BytePos {
        self.files
            .last()
            .map(|file| file.span.end())
            .unwrap_or(BytePos::ZERO)
    }

    pub fn add_file(&mut self, name: FileName, text: String, path: FilePath) -> Arc<File> {
        let start = self.end_pos() + 1;
        let end = start + BytePos::strlen(text.as_str());
        let mut rows = vec![start];
        rows.extend(
            text.match_indices('\n')
                .map(|(p, _)| start + (p as u32 + 1)),
        );
        let file = Arc::new(File {
            span: Span(start, end),
            name,
            text,
            rows,
            path,
        });
        self.files.push(file.clone());
        file
    }

    pub(crate) fn iter_files(&self) -> std::slice::Iter<'_, Arc<File>> {
        self.files.iter()
    }

    pub(crate) fn file_count(&self) -> usize {
        self.files.len()
    }
}

pub struct File {
    pub span: Span,
    name: FileName,
    text: String,
    path: FilePath,
    rows: Vec<BytePos>,
}

impl std::fmt::Debug for File {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "File({})", &self.name)
    }
}

impl PartialEq for File {
    /// Compares identity via raw pointer
    fn eq(&self, other: &Self) -> bool {
        self as *const _ == other as *const _
    }
}

impl Eq for File {}

impl std::hash::Hash for File {
    /// Files are only created by the `SourceMap`, so we only need to
    /// hash their spans. Maybe we could include their paths to be safe?
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.span.hash(state);
        // self.name.hash(state);
        // self.text.hash(state);
        // self.path.hash(state);
        // self.rows.hash(state);
    }
}

impl File {
    pub fn name(&self) -> &FileName {
        &self.name
    }

    pub fn source(&self) -> &str {
        &self.text
    }

    pub fn src_path(&self) -> &FilePath {
        &self.path
    }

    pub fn row_at(&self, pos: BytePos) -> Row {
        assert!(pos >= self.span.start() && pos <= self.span.end());
        match self.rows.binary_search(&pos) {
            Ok(n) => Row::new(n as u32),
            Err(n) => Row::new(n as u32 - 1),
        }
    }

    pub fn coord_at(&self, pos: BytePos) -> Coord {
        let row = self.row_at(pos);
        let row_span = self.row_span(row);
        let byte_col = pos - row_span.start();
        let col = Col::of_chars(&self.span_text(row_span)[byte_col.range_to()]);
        Coord { row, col }
    }

    pub fn span_text(&self, span: Span) -> &str {
        assert!(self.span.contains(span));
        &self.text[(span - self.span).range()]
    }

    pub fn row_span(&self, row: Row) -> Span {
        assert!(row > 0 && row.as_usize() < self.rows.len());
        Span(
            self.rows[if !row.is_zero() { row - 1u32 } else { row }.as_usize()],
            *self.rows.get(row.as_usize()).unwrap_or(&self.span.end()),
        )
    }

    pub fn row_text(&self, row: Row) -> &str {
        self.span_text(self.row_span(row))
            .trim_end_matches(&['\n', '\r'][..])
    }

    /// Returns the total number of lines in the file.
    pub fn height(&self) -> usize {
        self.rows.len()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FilePos {
    pub file: Arc<File>,
    pub coord: Coord,
}

impl std::fmt::Display for FilePos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.file.src_path(), &self.coord)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileRegion {
    pub file: Arc<File>,
    pub region: Location,
}

impl std::fmt::Display for FileRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (start, end) = (&self.region.start, &self.region.end);
        write!(f, "{}", self.file.src_path())?;
        if self.region.is_empty() {
            write!(f, "{start}")
        } else {
            write!(f, "[{start}, {end}]")
        }
    }
}
