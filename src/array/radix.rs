use core::fmt::{Debug, Formatter};

use num_traits::{PrimInt, Unsigned, WrappingAdd, WrappingMul, WrappingSub};

use crate::array::NanoArray;
use crate::radix_utils::*;

/// An arbitrary upper limit on the length of [`NanoArrayRadix`] to get around language limitations.
/// See [`NanoArrayRadix::POW`].
pub const MAX_LENGTH: usize = 64;

/// A [`NanoArray`] with element range `0..RADIX`, encoded as a base-`RADIX` unsigned integer
/// with 1 "digit" per element.
///
/// - `T`: a backing unsigned integer used to store the encoded number; (`n` bits).
/// - `RADIX`: determines the range of each element.
///
/// The length of the array `m` is defined by `argmax(m) RADIX.pow(m) <= 2.pow(n)`,
/// i.e. the largest `m`-digit base-`RADIX` number must fit in `T`.
/// Solving the inequality: `m = floor(n / log2(RADIX))`.
///
/// See [`NanoArray`] for the supported operations.
///
/// ## Iterator support
///
/// - This array is [`Copy`] and offers [`Self::into_iter()`] which consumes the array into an
///   iterator of its elements. A non-consuming iterator can be emulated using `.clone()`.
///
/// - This array implements [`FromIterator`] and can therefore be [`Iterator::collect`]ed into.
///   It consumes at most [`Self::LENGTH`] elements; if the iterator is short, `0` is filled.
///
/// Example:
/// ```
/// use nanovec::array::*;
/// type A = NanoArrayRadix<u32, 84>;
/// let a = [0x4A, 0x3B, 0x2C, 0x1D, 0x0E].iter().collect::<A>();
/// assert_eq!(a.get(0), 0x4A);
/// assert_eq!(a.get(1), 0x3B);
/// let v = a.clone().into_iter().collect::<Vec<_>>();
/// assert_eq!(v, vec![0x4A, 0x3B, 0x2C, 0x1D, 0x0E]);
/// assert_eq!(a.get(2), 0x2C);
/// assert_eq!(a.get(3), 0x1D);
/// assert_eq!(a.get(4), 0x0E);
/// ```
///
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct NanoArrayRadix<T, const RADIX: usize>(T)
    where T: PrimInt + Unsigned + Unsigned + WrappingAdd + WrappingSub + WrappingMul;

macro_rules! t {
    ($x:expr) => { T::from($x).unwrap() };
}

impl<T: PrimInt + Unsigned + Unsigned + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
NanoArrayRadix<T, RADIX> {
    /// Width of `T`, in Bytes.
    pub const NUM_BYTES: usize = core::mem::size_of::<T>();
    /// Width of `T`, in bits.
    pub const NUM_BITS: usize = Self::NUM_BYTES * 8;

    /// The fixed length of this array.
    pub const LENGTH: usize = get_capacity_clamped(Self::NUM_BITS, RADIX, MAX_LENGTH);

    /// Powers of `RADIX`; `POW[i] == RADIX.pow(i)`.
    ///
    /// Note that we want `[u128; Self::LENGTH]` but this is not possible in Rust Edition 2021.
    pub const POW: [u128; MAX_LENGTH] =
        get_powers_fixed::<MAX_LENGTH>(Self::LENGTH, RADIX);

    /// Converts this array into an iterator of its elements.
    pub fn into_iter(mut self) -> impl Iterator<Item=T> {
        core::iter::repeat_with(move || {
            let x = self.0 % t!(RADIX);
            self.0 = self.0 / t!(RADIX);
            x
        }).take(Self::LENGTH)
    }
}

impl<T: PrimInt + Unsigned + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
NanoArray for NanoArrayRadix<T, RADIX> {
    type Packed = T;
    type Element = T;
    const LENGTH: usize = Self::LENGTH;

    fn new() -> Self { Self(T::zero()) }

    fn from_packed(packed: T) -> Self { Self(packed) }

    fn packed(self) -> T { self.0 }

    fn max_elem() -> T { t!(RADIX - 1) }

    fn with(self, i: usize, elem: T) -> Self {
        assert!(elem < t!(RADIX));
        assert!(i < Self::LENGTH);
        self.with_unchecked(i, elem)
    }

    fn set(&mut self, i: usize, elem: T) {
        assert!(elem < t!(RADIX));
        assert!(i < Self::LENGTH);
        self.set_unchecked(i, elem);
    }

    fn get_unchecked(self, i: usize) -> T {
        (self.0 / t!(Self::POW[i])) % t!(RADIX)
    }

    fn with_unchecked(self, i: usize, elem: T) -> Self {
        // x + (elem - old_elem) * RADIX.pow(i) --- it all adds up in unsigned modular arithmetics.
        Self(
            self.0.wrapping_add(
                &elem.wrapping_sub(&self.get(i)).wrapping_mul(&t!(Self::POW[i])))
        )
    }

    fn set_unchecked(&mut self, i: usize, elem: T) {
        self.0 = self.with_unchecked(i, elem).0;
    }

    fn shift_high(self, n: usize) -> Self {
        assert!(n <= Self::LENGTH);
        if n == 0 { return self; }
        if n == Self::LENGTH { return Self::new() }
        Self(
            (self.0 % t!(Self::POW[Self::LENGTH - n])) * t!(Self::POW[n])
        )
    }

    fn shift_low(self, n: usize) -> Self {
        assert!(n <= Self::LENGTH);
        if n == 0 { return self; }
        if n == Self::LENGTH { return Self::new() }
        Self(
            self.0 / t!(Self::POW[n])
        )
    }

    fn rotate_high(self, n: usize) -> Self {
        assert!(n <= Self::LENGTH);
        if n == 0 || n == Self::LENGTH { return self; }
        let pow_split = t!(Self::POW[Self::LENGTH - n]);
        let pow_move = t!(Self::POW[n]);
        let left = self.0 / pow_split;
        let right = self.0 % pow_split;
        Self(
            right * pow_move + left
        )
    }
}

impl<T: PrimInt + Unsigned + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
Default for NanoArrayRadix<T, RADIX>  {
    fn default() -> Self { Self::new() }
}

impl<T: PrimInt + Unsigned + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
From<T> for NanoArrayRadix<T, RADIX>  {
    fn from(packed: T) -> Self {
        Self::from_packed(packed)
    }
}

impl<T: PrimInt + Unsigned + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
FromIterator<T> for NanoArrayRadix<T, RADIX>  {
    fn from_iter<It: IntoIterator<Item=T>>(iter: It) -> Self {
        let mut a = Self::new();
        for (i, elem)
        in iter.into_iter().enumerate().take(Self::LENGTH) {
            a.0 = a.0 + elem * t!(Self::POW[i]);
        }
        a
    }
}

impl<'a, T: PrimInt + Unsigned + WrappingAdd + WrappingSub + WrappingMul + 'a, const RADIX: usize>
FromIterator<&'a T> for NanoArrayRadix<T, RADIX>  {
    fn from_iter<It: IntoIterator<Item=&'a T>>(iter: It) -> Self {
        let mut a = Self::new();
        for (i, elem)
        in iter.into_iter().enumerate().take(Self::LENGTH) {
            a.0 = a.0 + (*elem) * t!(Self::POW[i]);
        }
        a
    }
}

impl<T: PrimInt + Unsigned + WrappingAdd + WrappingSub + WrappingMul + Debug, const RADIX: usize>
Debug for NanoArrayRadix<T, RADIX>  {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "[")?;
        for (i, x) in self.into_iter().enumerate() {
            if i == 0 {
                write!(f, "{:?}", x)?;
            } else {
                write!(f, ", {:?}", x)?;
            }
        }
        write!(f, "]")
    }
}

// TODO(summivox): rust (associated impl trait) for IntoIterator

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get_100() {
        type A = NanoArrayRadix<u32, 100>;
        let a = A::from_packed(12345678);
        assert_eq!(a.get(0), 78);
        assert_eq!(a.get(1), 56);
        assert_eq!(a.get(2), 34);
        assert_eq!(a.get(3), 12);
    }

    #[test]
    fn with_set_100() {
        type A = NanoArrayRadix<u32, 100>;
        let a = A::from_packed(12345678);
        assert_eq!(a.with(2, 99).packed(), 12995678);

        let mut a = A::from_packed(12345678);
        a.set(0, 0);
        assert_eq!(a.packed(), 12345600);
        a.set(3, 99);
        assert_eq!(a.packed(), 99345600);
    }

    #[test]
    fn shift_rotate_100() {
        type A = NanoArrayRadix<u32, 100>;
        let a = A::from_iter([12, 34, 56, 78]);

        assert_eq!(a.shift_high(0), a);
        assert_eq!(a.shift_high(1), A::from_iter([00, 12, 34, 56]));
        assert_eq!(a.shift_high(2), A::from_iter([00, 00, 12, 34]));
        assert_eq!(a.shift_high(3), A::from_iter([00, 00, 00, 12]));
        assert_eq!(a.shift_high(4), A::from_iter([00, 00, 00, 00]));

        assert_eq!(a.shift_low(0), a);
        assert_eq!(a.shift_low(1), A::from_iter([34, 56, 78, 00]));
        assert_eq!(a.shift_low(2), A::from_iter([56, 78, 00, 00]));
        assert_eq!(a.shift_low(3), A::from_iter([78, 00, 00, 00]));
        assert_eq!(a.shift_low(4), A::from_iter([00, 00, 00, 00]));

        assert_eq!(a.rotate_high(0), a);
        assert_eq!(a.rotate_high(1), A::from_iter([78, 12, 34, 56]));
        assert_eq!(a.rotate_high(2), A::from_iter([56, 78, 12, 34]));
        assert_eq!(a.rotate_high(3), A::from_iter([34, 56, 78, 12]));
        assert_eq!(a.rotate_high(4), a);

        assert_eq!(a.rotate_low(0), a);
        assert_eq!(a.rotate_low(1), A::from_iter([34, 56, 78, 12]));
        assert_eq!(a.rotate_low(2), A::from_iter([56, 78, 12, 34]));
        assert_eq!(a.rotate_low(3), A::from_iter([78, 12, 34, 56]));
        assert_eq!(a.rotate_low(4), a);
    }
}
