use core::fmt::{Debug, Formatter};

use num_traits::{PrimInt, WrappingAdd, WrappingMul, WrappingSub};

use super::radix_utils::*;

/// An arbitrary upper limit on the length of our array to get around language limitations.
pub const MAX_LENGTH: usize = 64;

/// Represents a fixed-length array of unsigned integers in the range `0..RADIX`,
/// stored as a base-`RADIX` unsigned integer with 1 "digit" per element.
///
/// - `T`: a backing unsigned integer used to store the encoded number; (`n` bits).
/// - `RADIX`: determines the range of each element.
///
/// The length of the array `m` is defined as `argmax(m) RADIX.pow(m) <= 2.pow(n)`,
/// i.e. the largest `m`-digit base-`RADIX` number must fit in `T`.
///
/// ## Summary of supported operations
///
/// - {Get, immutable set, mutable set} element at index.
///
/// - {Shift, Rotate} to the {"left", "right"}
///   - left = towards the LSdigit of the base-`RADIX` integer = towards the larger index
///   - right = towards the MSdigit of the base-`RADIX` integer = towards the smaller index
///
/// ## Iterator support
///
/// - This array is [`Copy`] and offers [`Self::into_iter()`] which consumes the array into an
///   iterator of its elements. A non-consuming iterator can be emulated using `.clone()`.
/// - This array implements [`FromIterator`] and can therefore be [`Iterator::collect`]ed into.
///   It can take at most [`Self::LENGTH`] elements.
///
/// Example:
/// ```
/// use nanovec::NanoArrayRadix;
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
pub struct NanoArrayRadix<T, const RADIX: usize>(pub T)
    where T: PrimInt + WrappingAdd + WrappingSub + WrappingMul;

macro_rules! t {
    ($x:expr) => { T::from($x).unwrap() };
}

impl<T: PrimInt + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
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

    /// Creates an empty array.
    pub fn new() -> Self { Self(T::zero()) }

    /// Creates a stack from its base-`RADIX` integer representation.
    pub fn from_packed(packed: T) -> Self { Self(packed) }

    /// Converts the stack to its base-`RADIX` integer representation.
    pub fn packed(self) -> T { self.0 }

    /// Returns the (fixed) length of this array.
    pub const fn len(self) -> usize { Self::LENGTH }

    /// Returns the `i`-th element of this array.
    /// Panics if the index is out of bounds.
    ///
    /// Example:
    /// ```
    /// use nanovec::NanoArrayRadix;
    /// type A = NanoArrayRadix<u32, 100>;
    /// let a = A::from_packed(12345678);
    /// assert_eq!(a.get(0), 78);
    /// assert_eq!(a.get(1), 56);
    /// assert_eq!(a.get(2), 34);
    /// assert_eq!(a.get(3), 12);
    /// ```
    pub fn get(self, i: usize) -> T {
        assert!(i < Self::LENGTH);
        (self.0 / t!(Self::POW[i])) % t!(RADIX)
    }

    /// Returns a new array = this array with the `i`-th element set to `elem`
    /// (a.k.a. immutable set index).
    /// Panics if the element is out of range or the index is out of bounds.
    ///
    /// Example:
    /// ```
    /// use nanovec::NanoArrayRadix;
    /// type A = NanoArrayRadix<u32, 100>;
    /// let a = A::from_packed(12345678);
    /// assert_eq!(a.with(2, 99).packed(), 12995678);
    /// ```
    pub fn with(self, i: usize, elem: T) -> Self {
        assert!(elem < t!(RADIX));
        assert!(i < Self::LENGTH);
        self.with_unchecked(i, elem)
    }

    /// Sets the `i`-th element of this array to `elem`.
    /// Panics if the element is out of range or the index is out of bounds.
    ///
    /// Example:
    /// ```
    /// use nanovec::NanoArrayRadix;
    /// type A = NanoArrayRadix<u32, 100>;
    /// let mut a = A::from_packed(12345678);
    /// a.set(0, 0);
    /// assert_eq!(a.packed(), 12345600);
    /// a.set(3, 99);
    /// assert_eq!(a.packed(), 99345600);
    /// ```
    pub fn set(&mut self, i: usize, elem: T) {
        assert!(elem < t!(RADIX));
        assert!(i < Self::LENGTH);
        self.set_unchecked(i, elem);
    }

    /// Returns a new array = this array with the `i`-th element set to `elem`
    /// (a.k.a. immutable set index).
    /// Result is a mess if the element is out of range.
    /// Panics if the index is out of bounds (due to indexing of [`Self::POW`]).
    pub fn with_unchecked(self, i: usize, elem: T) -> Self {
        // x + (elem - old_elem) * RADIX.pow(i) --- it all adds up in unsigned modular arithmetics.
        Self(
            self.0.wrapping_add(
                &elem.wrapping_sub(&self.get(i)).wrapping_mul(&t!(Self::POW[i])))
        )
    }

    /// Sets the `i`-th element of this array to `elem`.
    /// No-op if the index is out of bounds.
    pub fn set_unchecked(&mut self, i: usize, elem: T) {
        self.0 = self.with_unchecked(i, elem).0;
    }

    /// Shifts this array `n` elements towards the most significant digit.
    ///
    /// NOTE: The direction is consistent with the integer notation (left = towards MSdigit).
    ///
    /// Example: `[A, B, C, D, E] shl 1 == [0, A, B, C, D]`
    /// ```
    /// use nanovec::NanoArrayRadix;
    /// type A = NanoArrayRadix<u32, 84>;
    /// let a = A::new().with(0, 0x4A).with(1, 0x3B).with(2, 0x2C).with(3, 0x1D).with(4, 0x0E);
    /// let b = A::new().with(0, 0x00).with(1, 0x4A).with(2, 0x3B).with(3, 0x2C).with(4, 0x1D);
    /// assert_eq!(a.shl(1), b);
    /// ```
    pub fn shl(self, n: usize) -> Self {
        Self(
            (self.0 % t!(Self::POW[Self::LENGTH - n])) * t!(Self::POW[n])
        )
    }

    /// Shifts this array `n` elements towards the least significant digit.
    ///
    /// NOTE: The direction is consistent with the integer notation (right = towards LSdigit).
    ///
    /// Example: `[A, B, C, D, E] shr 1 == [B, C, D, E, 0]`
    /// ```
    /// use nanovec::NanoArrayRadix;
    /// type A = NanoArrayRadix<u32, 84>;
    /// let a = A::new().with(0, 0x4A).with(1, 0x3B).with(2, 0x2C).with(3, 0x1D).with(4, 0x0E);
    /// let b = A::new().with(0, 0x3B).with(1, 0x2C).with(2, 0x1D).with(3, 0x0E).with(4, 0x00);
    /// assert_eq!(a.shr(1), b);
    /// ```
    pub fn shr(self, n: usize) -> Self {
        Self(
            self.0 / t!(Self::POW[n])
        )
    }

    /// Rotates this array `n` elements towards the most significant digit.
    /// This is equivalent to `ror(LENGTH - n)`.
    ///
    /// NOTE: The direction is consistent with the integer notation (left = towards MSdigit).
    ///
    /// Example: `[A, B, C, D, E] rol 1 == [E, A, B, C, D]`
    /// ```
    /// use nanovec::NanoArrayRadix;
    /// type A = NanoArrayRadix<u32, 84>;
    /// let a = A::new().with(0, 0x4A).with(1, 0x3B).with(2, 0x2C).with(3, 0x1D).with(4, 0x0E);
    /// let b = A::new().with(0, 0x0E).with(1, 0x4A).with(2, 0x3B).with(3, 0x2C).with(4, 0x1D);
    /// assert_eq!(a.rol(1), b);
    /// ```
    pub fn rol(self, n: usize) -> Self {
        assert!(n <= Self::LENGTH);
        let pow_split = t!(Self::POW[Self::LENGTH - n]);
        let pow_move = t!(Self::POW[n]);
        let left = self.0 / pow_split;
        let right = self.0 % pow_split;
        Self(
            right * pow_move + left
        )
    }

    /// Rotates this array `n` elements towards the least significant digit.
    /// This is equivalent to `rol(LENGTH - n)`.
    ///
    /// NOTE: The direction is consistent with the integer notation (right = towards LSdigit).
    ///
    /// Example: `[A, B, C, D, E] ror 1 => [B, C, D, E, A]`
    /// ```
    /// use nanovec::NanoArrayRadix;
    /// type A = NanoArrayRadix<u32, 84>;
    /// let a = A::new().with(0, 0x4A).with(1, 0x3B).with(2, 0x2C).with(3, 0x1D).with(4, 0x0E);
    /// let b = A::new().with(0, 0x3B).with(1, 0x2C).with(2, 0x1D).with(3, 0x0E).with(4, 0x4A);
    /// assert_eq!(a.ror(1), b);
    /// ```
    pub fn ror(self, n: usize) -> Self {
        assert!(n <= Self::LENGTH);
        self.rol(Self::LENGTH - n)
    }

    /// Converts this array into an iterator of its elements.
    pub fn into_iter(mut self) -> impl Iterator<Item=T> {
        core::iter::repeat_with(move || {
            let x = self.0 % t!(RADIX);
            self.0 = self.0 / t!(RADIX);
            x
        }).take(Self::LENGTH)
    }
}

impl<T: PrimInt + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
Default for NanoArrayRadix<T, RADIX>  {
    fn default() -> Self { Self::new() }
}

impl<T: PrimInt + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
From<T> for NanoArrayRadix<T, RADIX>  {
    fn from(packed: T) -> Self {
        Self::from_packed(packed)
    }
}

impl<T: PrimInt + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
FromIterator<T> for NanoArrayRadix<T, RADIX>  {
    fn from_iter<It: IntoIterator<Item=T>>(iter: It) -> Self {
        let mut a = Self::new();
        let powers = core::iter::successors(
            Some(T::one()),
            |&x| Some(x * t!(RADIX)));
        for (pow, elem)
        in powers.zip(iter.into_iter()).take(Self::LENGTH) {
            a.0 = a.0 + elem * pow;
        }
        a
    }
}

impl<'a, T: PrimInt + WrappingAdd + WrappingSub + WrappingMul + 'a, const RADIX: usize>
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

impl<T: PrimInt + WrappingAdd + WrappingSub + WrappingMul + Debug, const RADIX: usize>
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

// TODO(summivox): IntoIterator (need associated impl trait)
