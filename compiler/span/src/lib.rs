pub mod col;
pub mod coord;
pub mod pos;
pub mod ranges;
pub mod row;
pub mod wrappers;

pub use col::Col;
pub use coord::Coord;
pub use pos::BytePos;
use ranges::CoordSpan;
pub use ranges::{Position, Region, Span};
pub use row::Row;
pub use wrappers::{Located, Positioned, Spanned};

pub trait Unspan {
    type Item;
    fn unspan(self) -> Self::Item;
}

impl<I> Unspan for Spanned<I> {
    type Item = I;

    fn unspan(self) -> Self::Item {
        self.take_item()
    }
}

impl<I> Unspan for (I, Span) {
    type Item = I;

    fn unspan(self) -> Self::Item {
        self.0
    }
}

/// Public interface for identifying invalid (tracking-related) values.
pub trait Dummy
where
    Self: Sized + PartialEq,
{
    const DUMMY: Self;
    fn dummy() -> Self {
        Self::DUMMY
    }
    fn is_dummy(&self) -> bool {
        self == &Self::DUMMY
    }
    fn partial_dummy(&self) -> bool;
}

/// Public interface for dealing with `Span`s.
pub trait WithSpan {
    fn get_pos(&self) -> BytePos;

    fn as_index(&self) -> usize {
        self.get_pos().as_usize()
    }

    fn spanned<F, X>(&mut self, mut f: F) -> Spanned<X>
    where
        F: FnMut(&mut Self) -> X,
    {
        let start = self.get_pos();
        let ret = f(self);
        let end = self.get_pos();
        Spanned(ret, Span(start, end))
    }

    fn while_pos<X>(
        &mut self,
        mut pred: impl FnMut(BytePos) -> bool,
        mut f: impl FnMut(&mut Self) -> X,
    ) -> Vec<Spanned<X>> {
        std::iter::from_fn(|| {
            if pred(self.get_pos()) {
                Some(self.spanned(|this| f(this)))
            } else {
                None
            }
        })
        .collect()
    }
}

pub trait WithLoc {
    fn get_coord(&self) -> Coord;
    fn get_row(&self) -> Row {
        WithLoc::get_coord(self).row
    }
    fn get_col(&self) -> Col {
        WithLoc::get_coord(self).col
    }
    fn located<X>(&mut self, mut f: impl FnMut(&mut Self) -> X) -> Located<X> {
        let start = WithLoc::get_coord(self);
        let x = f(self);
        let end = WithLoc::get_coord(self);
        Located(x, Region { start, end })
    }
    fn while_loc<X>(
        &mut self,
        mut pred: impl FnMut(Coord) -> bool,
        mut f: impl FnMut(&mut Self) -> X,
    ) -> Vec<Located<X>> {
        std::iter::from_fn(|| {
            if pred(self.get_coord()) {
                Some(self.located(|this| f(this)))
            } else {
                None
            }
        })
        .collect()
    }
    fn while_row<X>(
        &mut self,
        mut pred: impl FnMut(Row) -> bool,
        mut f: impl FnMut(&mut Self) -> X,
    ) -> Vec<Located<X>> {
        std::iter::from_fn(|| {
            if pred(self.get_row()) {
                Some(self.located(|this| f(this)))
            } else {
                None
            }
        })
        .collect()
    }
    fn while_col<X>(
        &mut self,
        mut pred: impl FnMut(Col) -> bool,
        mut f: impl FnMut(&mut Self) -> X,
    ) -> Vec<Located<X>> {
        std::iter::from_fn(|| {
            if pred(self.get_col()) {
                Some(self.located(|this| f(this)))
            } else {
                None
            }
        })
        .collect()
    }
}

pub trait WithCoordSpan {
    fn get_coord_span(&self) -> CoordSpan;

    fn get_coord(&self) -> Coord {
        self.get_coord_span().coord()
    }
    fn get_span(&self) -> Span {
        self.get_coord_span().span()
    }
    fn get_row(&self) -> Row {
        self.get_coord().row
    }
    fn get_col(&self) -> Col {
        self.get_coord().col
    }
    fn start(&self) -> BytePos {
        self.get_span().start()
    }
    fn end(&self) -> BytePos {
        self.get_span().end()
    }
}

pub trait WithPosition: WithSpan + WithLoc {
    fn get_position(&self) -> Position;
    fn get_span(&self) -> Span {
        self.get_position().span()
    }
    fn get_location(&self) -> Region {
        self.get_position().location()
    }
    fn positioned<X>(&mut self, mut f: impl FnMut(&mut Self) -> X) -> Positioned<X> {
        let pos_a = WithSpan::get_pos(self);
        let start = WithLoc::get_coord(self);
        let x = f(self);
        let pos_b = WithSpan::get_pos(self);
        let end = WithLoc::get_coord(self);
        Positioned(
            x,
            Position {
                span: Span(pos_a, pos_b),
                region: Region { start, end },
            },
        )
    }
}

impl Dummy for Span {
    const DUMMY: Self = Self(BytePos::ZERO, BytePos::ZERO);

    fn is_dummy(&self) -> bool {
        self.0.is_dummy() && self.1.is_dummy() || self.is_empty()
    }

    fn partial_dummy(&self) -> bool {
        self.0.is_dummy() || self.1.is_dummy()
    }
}

impl Dummy for Row {
    const DUMMY: Self = Self::ZERO;

    fn partial_dummy(&self) -> bool {
        self.is_zero()
    }
}

impl Dummy for Col {
    const DUMMY: Self = Self::MAX;

    fn partial_dummy(&self) -> bool {
        self.is_max()
    }
}

impl Dummy for Coord {
    /// Dummy `Position` for situations in which the only requirement
    /// is the existence of a `Position`. Useful as an intermediate value.
    ///
    /// Note: dummy values can be identified by having a `row` value
    /// of `Row::ZERO` or a `col` value of `u32::MAX`, while `Position`
    /// has a default (and starting) `row` value of `Row::ONE`.
    const DUMMY: Self = Self {
        row: Row::ZERO,
        col: Col::MAX,
    };

    fn partial_dummy(&self) -> bool {
        self.row.is_zero() || self.col.is_max()
    }
}

impl Dummy for Region {
    const DUMMY: Self = Self {
        start: Coord::DUMMY,
        end: Coord::DUMMY,
    };

    fn is_dummy(&self) -> bool {
        self.start.is_dummy() || self.end.is_dummy() || self.is_empty()
    }

    fn partial_dummy(&self) -> bool {
        self.start.is_dummy()
            || self.end.is_dummy()
            || self.start.row > self.end.row
            || self.start.col > self.end.col
    }
}

impl Dummy for Position {
    const DUMMY: Self = Self {
        span: Span::DUMMY,
        region: Region::DUMMY,
    };

    fn is_dummy(&self) -> bool {
        self.span.is_dummy() || self.region.is_dummy() || self.is_empty()
    }

    fn partial_dummy(&self) -> bool {
        self.span.partial_dummy()
            || self.region.partial_dummy()
            || self.span.is_empty()
            || self.region.is_empty()
    }
}

impl WithSpan for BytePos {
    fn get_pos(&self) -> BytePos {
        *self
    }
}

impl WithLoc for Coord {
    fn get_coord(&self) -> Coord {
        *self
    }
}

impl WithCoordSpan for CoordSpan {
    fn get_coord_span(&self) -> CoordSpan {
        *self
    }
}
