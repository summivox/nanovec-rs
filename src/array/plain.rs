//! Implements [`crate::NanoArray`] for plain arrays.
//!
//! This is intended primarily for testing. While it is fully functional, the shift/rotate and
//! "immutable set" (`with_unchecked`) methods might not be as efficient as their bit-/radix-packed
//! counterparts.
//!
//! Example:
//! ```
//! use nanovec::NanoArray;
//! fn test<Array: NanoArray<Element=u8>>(a: Array) -> Array {
//!     a.with(0, 10).with(1, 20).with(2, 30).with(3, 255).rotate_high(2)
//! }
//! assert_eq!(test([0; 5]), [255, 0, 10, 20, 30]);
//! ```

use num_traits::{PrimInt, Unsigned};

use crate::array::NanoArray;

impl<T: PrimInt + Unsigned, const LENGTH: usize> NanoArray for [T; LENGTH] {
    type Packed = Self;
    type Element = T;
    const LENGTH: usize = LENGTH;

    fn new() -> Self { [T::zero(); LENGTH] }

    fn from_packed(packed: Self::Packed) -> Self { packed }

    fn packed(self) -> Self::Packed { self }

    fn unpacked(self) -> [T; LENGTH] { self }

    fn max_elem() -> Self::Element { T::max_value() }

    fn get_unchecked(self, i: usize) -> Self::Element { self[i] }

    fn with_unchecked(mut self, i: usize, elem: Self::Element) -> Self {
        self[i] = elem;
        self
    }

    fn set_unchecked(&mut self, i: usize, elem: Self::Element) { self[i] = elem; }

    fn shift_high(mut self, n: usize) -> Self {
        self.rotate_right(n);
        for i in 0..n {
            self[i] = T::zero();
        }
        self
    }

    fn shift_low(mut self, n: usize) -> Self {
        self.rotate_left(n);
        for i in (LENGTH - n)..LENGTH {
            self[i] = T::zero();
        }
        self
    }

    fn rotate_high(mut self, n: usize) -> Self {
        self.rotate_right(n);
        self
    }

    fn rotate_low(mut self, n: usize) -> Self {
        self.rotate_left(n);
        self
    }
}
