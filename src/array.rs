//! Defines a trait for fixed-length compressed arrays.

mod bit;
mod plain;
mod radix;

use num_traits::{PrimInt, Unsigned};

pub use self::{
    bit::NanoArrayBit,
    radix::NanoArrayRadix,
};

/// A fixed-length array of unsigned integers in the range `0..(Self::max_elem())`.
/// May be stored in a compressed format, and therefore does not provide references; this means no
/// [`core::ops::Index`] or [`core::ops::IndexMut`] required, and no slicing.
///
/// **The following operations are required to be implemented**:
///
/// - read element at index --- [`Self::get_unchecked`]
/// - write element at index --- [`Self::set_unchecked`] and/or [`Self::with_unchecked`]
/// - shift and rotate
///   - [`Self::shift_low`] and [`Self::shift_high`]
///   - [`Self::rotate_low`] and/or [`Self::rotate_high`]
///
pub trait NanoArray:
Copy + Clone + Sized + PartialEq + Eq {
    /// The underlying representation of this array.
    type Packed;
    
    /// The element type of this array; must be an unsigned primitive integer.
    /// Note that it's _not guaranteed_ that all values that can fit the type is allowed;
    /// see [`Self::max_elem()`].
    type Element: PrimInt + Unsigned;

    /// The fixed length of this array.
    const LENGTH: usize;

    /// Creates an all-zero array.
    fn new() -> Self;

    /// Creates an array from its underlying representation.
    fn from_packed(packed: Self::Packed) -> Self;

    /// Converts the array to its underlying representation.
    fn packed(self) -> Self::Packed;

    /// Returns the maximum element allowed in this array.
    fn max_elem() -> Self::Element;

    /// Returns the `i`-th element of this array.
    /// Panics if the index is out of bounds.
    fn get(self, i: usize) -> Self::Element {
        assert!(i < Self::LENGTH);
        self.get_unchecked(i)
    }

    /// Returns a new array = this array with the `i`-th element set to `elem`
    /// (a.k.a. immutable set index).
    /// Panics if the index is out of bounds or the element is out of range.
    fn with(self, i: usize, elem: Self::Element) -> Self {
        assert!(i < Self::LENGTH);
        assert!(elem <= Self::max_elem());
        self.with_unchecked(i, elem)
    }

    /// Sets the `i`-th element of this array to `elem`.
    /// Panics if the index is out of bounds or the element is out of range.
    fn set(&mut self, i: usize, elem: Self::Element) {
        assert!(i < Self::LENGTH);
        assert!(elem <= Self::max_elem());
        self.set_unchecked(i, elem)
    }

    /// Returns the `i`-th element of this array.
    /// Behavior when the index is out of bounds is _unspecified_ (okay to panic).
    fn get_unchecked(self, i: usize) -> Self::Element;

    /// Returns a new array = this array with the `i`-th element set to `elem`
    /// (a.k.a. immutable set index).
    /// Behavior when the index is out of bounds is _unspecified_ (okay to panic).
    ///
    /// Implementer must provide at least one of [`Self::with_unchecked`], [`Self::set_unchecked`].
    fn with_unchecked(self, i: usize, elem: Self::Element) -> Self {
        let mut copy = self.clone();
        copy.set_unchecked(i, elem);
        copy
    }

    /// Sets the `i`-th element of this array to `elem`.
    /// Behavior when the index is out of bounds is _unspecified_ (okay to panic).
    ///
    /// Implementer must provide at least one of [`Self::with_unchecked`], [`Self::set_unchecked`].
    fn set_unchecked(&mut self, i: usize, elem: Self::Element) {
        replace_with::replace_with(
            self, || Self::new(), |x| x.with_unchecked(i, elem));
    }

    /// Shifts this array `n` elements towards the higher index.
    /// The lower indices will be left as `0`.
    /// Behavior when `n > Self::LENGTH` is _unspecified_ (okay to panic).
    ///
    /// Example: `shift_high([A, B, C, D], 1) == [0, A, B, C]`
    fn shift_high(self, n: usize) -> Self;

    /// Shifts this array `n` elements towards the lower index
    /// The higher indices will be left as `0`.
    /// Behavior when `n > Self::LENGTH` is _unspecified_ (okay to panic).
    ///
    /// Example: `shift_low([A, B, C, D], 1) == [B, C, D, 0]`
    fn shift_low(self, n: usize) -> Self;

    /// Rotates this array `n` elements towards the higher index.
    /// This is equivalent to `rotate_low(Self::LENGTH - n)`.
    /// Panics when `n > Self::LENGTH`.
    ///
    /// Example: `rotate_high([A, B, C, D], 1) == [D, A, B, C]`
    ///
    /// Implementer must provide at least one of [`Self::rotate_high`], [`Self::rotate_low`].
    fn rotate_high(self, n: usize) -> Self {
        assert!(n <= Self::LENGTH);
        self.rotate_low(Self::LENGTH - n)
    }

    /// Rotates this array `n` elements towards the lower index.
    /// This is equivalent to `rotate_high(Self::LENGTH - n)`.
    /// Panics when `n > Self::LENGTH`.
    ///
    /// Example: `rotate_low([A, B, C, D], 1) == [B, C, D, A]`
    ///
    /// Implementer must provide at least one of [`Self::rotate_high`], [`Self::rotate_low`].
    fn rotate_low(self, n: usize) -> Self {
        assert!(n <= Self::LENGTH);
        self.rotate_high(Self::LENGTH - n)
    }
}
