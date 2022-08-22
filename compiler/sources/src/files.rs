use std::{fmt, path::Path, sync::Arc};

use serde::{Deserialize, Serialize};
use wy_intern::Symbol;
use wy_span::{BytePos, Col, Coord, Region, Row, Span};

use crate::paths::{FileId, FilePath, IoResult};

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

    pub fn has_file<P: AsRef<Path>>(&self, p: P) -> bool {
        let path = p.as_ref();
        self.iter_files().any(|file| file.path.path() == path)
    }

    pub fn file_init_pos<P: AsRef<Path>>(&self, p: P) -> Option<BytePos> {
        let path = p.as_ref();
        self.iter_files().find_map(|file| {
            if file.path.path() == path && !file.rows.is_empty() {
                Some(file.start_pos())
            } else {
                None
            }
        })
    }

    pub fn add_from_filepath(&mut self, filepath: FilePath) -> IoResult<Arc<File>> {
        if let Some(file) = self.find_file_with_path(&filepath) {
            return Ok(file.clone());
        }

        filepath
            .read_to_string()
            .map(|text| self.add_file(FileName::from_filepath(&filepath), text, filepath))
    }

    pub fn has_file_with_path<P: AsRef<Path>>(&self, path: P) -> bool {
        self.iter_files()
            .any(|file| file.src_path().path() == path.as_ref())
    }

    pub fn find_file_with_path<P: AsRef<Path>>(&self, path: P) -> Option<&Arc<File>> {
        self.iter_files()
            .find(|file| file.src_path().path() == path.as_ref())
    }

    pub fn add_file(&mut self, name: FileName, text: String, path: FilePath) -> Arc<File> {
        if let Some(stored_file) = self.iter_files().find(|file| file.src_path() == &path) {
            return stored_file.clone();
        }

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

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct FileName(Symbol);

impl FileName {
    pub fn from_filepath(fp: &FilePath) -> Self {
        FileName(Symbol::intern(fp.file_name()))
    }
}

impl fmt::Debug for FileName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FileName({})", &self.0)
    }
}

impl fmt::Display for FileName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.0)
    }
}

#[derive(Serialize, Deserialize)]
pub struct File {
    pub span: Span,
    name: FileName,
    text: String,
    path: FilePath,
    rows: Vec<BytePos>,
}

impl std::fmt::Debug for File {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("File")
            .field("name", &self.name())
            .field("path", &self.src_path())
            .field("rows", &self.rows)
            .finish_non_exhaustive()
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

impl AsRef<str> for File {
    fn as_ref(&self) -> &str {
        self.text.as_str()
    }
}

impl File {
    pub fn name(&self) -> &FileName {
        &self.name
    }

    pub fn source(&self) -> &str {
        &self.text
    }

    pub fn id(&self) -> FileId {
        self.src_path().id()
    }

    pub fn src_path(&self) -> &FilePath {
        &self.path
    }

    pub fn start_pos(&self) -> BytePos {
        assert!(!self.rows.is_empty());
        self.rows[0]
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
        assert!(row > 0u32 && row.as_usize() < self.rows.len());
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
pub struct FileCoord {
    pub file: Arc<File>,
    pub coord: Coord,
}

impl std::fmt::Display for FileCoord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.file.src_path(), &self.coord)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileRegion {
    pub file: Arc<File>,
    pub region: Region,
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
