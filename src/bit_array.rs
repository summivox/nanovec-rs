use core::{
    marker::PhantomData as P
};
use core::fmt::{Debug, Formatter};
use num_traits::PrimInt;

/// Represents a fixed-length array of unsigned integers in the range `0..(1 << NUM_ELEM_BITS)`,
/// stored as a wider unsigned integer with each element taking exactly `NUM_ELEM_BITS`.
///
/// - `TContainer`: an unsigned integer storing all elements in the array (`n` bits).
/// - `TElem`: an unsigned integer that can fit each element (`m` bits).
/// - `NUM_ELEM_BITS == k`: determines the range of each element (`k` bits).
///
/// The following must hold: `n >= m >= k`, i.e. `TContainer` must be at least as wide as `TElem`,
/// and `TElem` must be at least `NUM_ELEM_BITS` wide.
///
/// The length of the array is determined as `floor(n / k)`.
///
/// ## Summary of supported operations
///
/// - {Get, immutable set, mutable set} element at index.
///
/// - {Shift, Rotate} to the {"left", "right"}
///   - left = towards the LSbit of the bit-packed integer = towards the larger index
///   - right = towards the MSbit of the bit-packed integer = towards the smaller index
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
/// use nanovec::NanoArrayBit;
/// type A = NanoArrayBit<u32, u8, 8>;
/// let a = [0xA, 0xB, 0xC, 0xD].iter().collect::<A>();
/// assert_eq!(a.get(0), 0xA);
/// assert_eq!(a.get(1), 0xB);
/// let v = a.clone().into_iter().collect::<Vec<_>>();
/// assert_eq!(v, vec![0xA, 0xB, 0xC, 0xD]);
/// assert_eq!(a.get(2), 0xC);
/// assert_eq!(a.get(3), 0xD);
/// ```
///
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct NanoArrayBit<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>(
    TContainer, P<TElem>
);

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS> {
    /// Width of `TContainer`, in Bytes.
    pub const NUM_CONTAINER_BYTES: usize = core::mem::size_of::<TContainer>();
    /// Width of `TContainer`, in bits.
    pub const NUM_CONTAINER_BITS: usize = Self::NUM_CONTAINER_BYTES * 8;
    /// Width of `TElem`, in Bytes.
    pub const NUM_ELEM_TYPE_BYTES: usize = core::mem::size_of::<TElem>();
    /// Width of `TElem`, in bits.
    pub const NUM_ELEM_TYPE_BITS: usize = Self::NUM_ELEM_TYPE_BYTES * 8;

    /// Number of elements in this array.
    pub const LENGTH: usize = Self::NUM_CONTAINER_BITS / NUM_ELEM_BITS;
    /// The maximum number of bits occupied in `TContainer`.
    pub const LENGTH_BITS: usize = Self::LENGTH * NUM_ELEM_BITS;

    // Note: due to "constexpr" limitations, we're limited to this kind of hacky static assertions.

    /// `TContainer` must be at least as wide as `TElem`.
    const _CHECK1: u8 =
        if Self::NUM_CONTAINER_BITS >= Self::NUM_ELEM_TYPE_BITS { 0 } else { panic!() };
    /// `TElem` must be able to fit the full range of elements.
    const _CHECK2: u8 =
        if Self::NUM_ELEM_TYPE_BITS >= NUM_ELEM_BITS { 0 } else { panic!() };
    const fn static_asserts() {
        let _ = Self::_CHECK1;
        let _ = Self::_CHECK2;
    }

    /// Bit mask covering all bits that could be occupied in `TContainer`.
    pub(crate) fn container_mask() -> TContainer {
        if Self::LENGTH_BITS == Self::NUM_CONTAINER_BITS {
            !TContainer::zero()
        } else {
            (TContainer::one() << Self::LENGTH_BITS) - TContainer::one()
        }
    }

    /// Bit mask covering one element at index 0.
    pub(crate) fn elem_mask() -> TContainer {
        (TContainer::one() << NUM_ELEM_BITS) - TContainer::one()
    }

    /// Bit mask covering elements at indices `0..i` (excluding `i`)
    pub(crate) fn prefix_mask(i: usize) -> TContainer {
        if i == Self::LENGTH {
            Self::container_mask()
        } else {
            (TContainer::one() << (i * NUM_ELEM_BITS)) - TContainer::one()
        }
    }

    /// Bit mask covering one element at index `i`.
    pub(crate) fn index_mask(i: usize) -> TContainer {
        Self::elem_mask() << (i * NUM_ELEM_BITS)
    }

    /// Creates an all-zero array.
    pub fn new() -> Self {
        Self::static_asserts();
        Self(TContainer::zero(), P)
    }

    /// Creates an array with given bit-packed integer representation.
    pub fn from_packed(packed: TContainer) -> Self {
        Self::static_asserts();
        Self(packed & Self::container_mask(), P)
    }

    /// Returns the bit-packed integer representation of this array.
    pub const fn packed(self) -> TContainer { self.0 }

    /// Returns the (fixed) length of this array.
    pub const fn len(self) -> usize { Self::LENGTH }

    /// Returns the `i`-th element of this array.
    /// Panics if the index is out of bounds.
    pub fn get(self, i: usize) -> TElem {
        assert!(i < Self::LENGTH);
        self.get_unchecked(i)
    }

    /// Returns a new array = this array with the `i`-th element set to `elem`
    /// (a.k.a. immutable set index).
    /// Panics if the index is out of bounds.
    pub fn with(self, i: usize, elem: TElem) -> Self {
        assert!(i < Self::LENGTH);
        self.with_unchecked(i, elem)
    }

    /// Sets the `i`-th element of this array to `elem`.
    /// Panics if the index is out of bounds.
    pub fn set(&mut self, i: usize, elem: TElem) {
        assert!(i < Self::LENGTH);
        self.set_unchecked(i, elem);
    }

    /// Returns the `i`-th element of this array.
    pub fn get_unchecked(self, i: usize) -> TElem {
        TElem::from((self.0 >> (i * NUM_ELEM_BITS)) & Self::elem_mask()).unwrap()
    }

    /// Returns a new array = this array with the `i`-th element set to `elem`
    /// (a.k.a. immutable set index).
    /// No-op if the index is out of bounds.
    pub fn with_unchecked(self, i: usize, elem: TElem) -> Self {
        Self(
            ((self.0 & !Self::index_mask(i)) |
                ((TContainer::from(elem).unwrap() & Self::elem_mask()) << (i * NUM_ELEM_BITS))) &
                Self::container_mask(),
            P
        )
    }

    /// Sets the `i`-th element of this array to `elem`.
    /// No-op if the index is out of bounds.
    pub fn set_unchecked(&mut self, i: usize, elem: TElem) {
        self.0 = self.with_unchecked(i, elem).0;
    }

    /// Shifts this array `n` elements to the MSbit.
    ///
    /// NOTE: The direction is consistent with the backing integer (left = towards MSbit).
    ///
    /// Example: `[A, B, C, D] shl 1 == [0, A, B, C]`
    /// ```
    /// use nanovec::NanoArrayBit;
    /// type A = NanoArrayBit<u32, u8, 8>;
    /// let a = A::new().with(0, 0xA).with(1, 0xB).with(2, 0xC).with(3, 0xD);
    /// let b = A::new().with(0, 0x0).with(1, 0xA).with(2, 0xB).with(3, 0xC);
    /// assert_eq!(a.shl(1), b);
    /// ```
    pub fn shl(self, n: usize) -> Self {
        Self(
            (self.0 << (n * NUM_ELEM_BITS)) & Self::container_mask(),
            P
        )
    }

    /// Shifts this array `n` elements to the LSbit.
    ///
    /// NOTE: The direction is consistent with the backing integer (right = towards LSbit).
    ///
    /// Example: `[A, B, C, D] shr 1 == [B, C, D, 0]`
    /// ```
    /// use nanovec::NanoArrayBit;
    /// type A = NanoArrayBit<u32, u8, 8>;
    /// let a = A::new().with(0, 0xA).with(1, 0xB).with(2, 0xC).with(3, 0xD);
    /// let b = A::new().with(0, 0xB).with(1, 0xC).with(2, 0xD).with(3, 0x0);
    /// assert_eq!(a.shr(1), b);
    /// ```
    pub fn shr(self, n: usize) -> Self {
        Self(
            self.0 >> (n * NUM_ELEM_BITS),
            P
        )
    }

    /// Rotates this array `n` elements to the MSbit.
    /// This is equivalent to `ror(LENGTH - n)`.
    ///
    /// NOTE: The direction is consistent with the backing integer (left = towards MSbit).
    ///
    /// Example: `[A, B, C, D] rol 1 == [D, A, B, C]`
    /// ```
    /// use nanovec::NanoArrayBit;
    /// type A = NanoArrayBit<u32, u8, 8>;
    /// let a = A::new().with(0, 0xA).with(1, 0xB).with(2, 0xC).with(3, 0xD);
    /// let b = A::new().with(0, 0xD).with(1, 0xA).with(2, 0xB).with(3, 0xC);
    /// assert_eq!(a.rol(1), b);
    /// ```
    pub fn rol(self, n: usize) -> Self {
        assert!(n <= Self::LENGTH);
        Self(
            ((self.0 & Self::prefix_mask(Self::LENGTH - n)) << (NUM_ELEM_BITS * n)) |
                (self.0 >> (NUM_ELEM_BITS * (Self::LENGTH - n))),
            P
        )
    }

    /// Rotates this array `n` elements to the LSbit.
    /// This is equivalent to `rol(LENGTH - n)`.
    ///
    /// NOTE: The direction is consistent with the backing integer (right = towards LSbit).
    ///
    /// Example: `[A, B, C, D] ror 1 => [B, C, D, A]`
    /// ```
    /// use nanovec::NanoArrayBit;
    /// type A = NanoArrayBit<u32, u8, 8>;
    /// let a = A::new().with(0, 0xA).with(1, 0xB).with(2, 0xC).with(3, 0xD);
    /// let b = A::new().with(0, 0xB).with(1, 0xC).with(2, 0xD).with(3, 0xA);
    /// assert_eq!(a.ror(1), b);
    /// ```
    pub fn ror(self, n: usize) -> Self {
        assert!(n <= Self::LENGTH);
        self.rol(Self::LENGTH - n)
    }

    /// Converts this array into an iterator of its elements.
    ///
    /// See [struct-level docs](NanoArrayBit) for example.
    pub fn into_iter(self) -> impl Iterator<Item=TElem> {
        (0..Self::LENGTH).map(move |i| self.get_unchecked(i))
    }
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
Default for NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS> {
    fn default() -> Self { Self::new() }
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
From<TContainer> for NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS> {
    fn from(packed: TContainer) -> Self {
        Self::from_packed(packed)
    }
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
FromIterator<TElem> for NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS> {
    fn from_iter<T: IntoIterator<Item=TElem>>(iter: T) -> Self {
        let mut a = Self::new();
        for (i, elem) in iter.into_iter()
            .enumerate()
            .take(Self::LENGTH) {
            a.set(i, elem);
        }
        a
    }
}

impl<'a, TContainer: PrimInt, TElem: PrimInt + 'a, const NUM_ELEM_BITS: usize>
FromIterator<&'a TElem> for NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS> {
    fn from_iter<T: IntoIterator<Item=&'a TElem>>(iter: T) -> Self {
        let mut a = Self::new();
        for (i, elem) in iter.into_iter()
            .enumerate()
            .take(Self::LENGTH) {
            a.set(i, *elem);
        }
        a
    }
}

impl<TContainer: PrimInt, TElem: PrimInt + Debug, const NUM_ELEM_BITS: usize>
Debug for NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "[")?;
        for i in 0..Self::LENGTH {
            if i == 0 {
                write!(f, "{:?}", self.get(i))?;
            } else {
                write!(f, ", {:?}", self.get(i))?;
            }
        }
        write!(f, "]")
    }
}

// TODO(summivox): rust (associated impl trait)
/*
impl<TContainer: PrimInt, TElem: PrimInt, TFn: Fn(usize) -> TElem, const NUM_ELEM_BITS: usize>
IntoIterator for NanoArray<TContainer, TElem, NUM_ELEM_BITS> {
    type Item = TElem;
    type IntoIter = impl Iterator<Item=TElem>;

    fn into_iter(self) -> Self::IntoIter { self.into_iter() }
}
*/
