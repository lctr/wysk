pub mod show;

pub mod diff;

pub use show::{Dialogue, SrcLoc, SrcPath};

pub type Outcome<X, E> = Result<X, Failure<E>>;

#[derive(Debug)]
pub enum Failure<E> {
    Io(std::io::Error),
    Err(E),
}

pub fn normalize_io_err<E>(error: Failure<std::io::Error>) -> Failure<E> {
    match error {
        Failure::Io(e) | Failure::Err(e) => Failure::Io(e),
    }
}

impl<E> std::fmt::Display for Failure<E>
where
    E: std::error::Error,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Failure::Io(err) => write!(f, "IO error: {}", err),
            Failure::Err(e) => write!(f, "{}", e),
        }
    }
}

impl<E> From<std::io::Error> for Failure<E> {
    fn from(ioerr: std::io::Error) -> Self {
        Failure::Io(ioerr)
    }
}

impl<E> From<Failure<Failure<E>>> for Failure<E> {
    fn from(e: Failure<Failure<E>>) -> Self {
        match e {
            Failure::Io(e) => Failure::Io(e),
            Failure::Err(e) => e,
        }
    }
}

impl<E> std::error::Error for Failure<E> where E: std::error::Error {}
