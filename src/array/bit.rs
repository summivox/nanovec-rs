use core::{
    marker::PhantomData as P
};

use core::fmt::{Debug, Formatter};

use num_traits::{CheckedShl, CheckedShr, PrimInt, Unsigned};

use crate::array::NanoArray;

/// A [`NanoArray`] with element range `0..(1 << NUM_ELEM_BITS)`, i.e. a `k`-bit unsigned
/// integer, bit-packed into a `n`-bit unsigned integer where `n >= k`.
///
/// - `TContainer`: a `n`-bit unsigned integer that stores the content of the array.
/// - `TElem`: an `m`-bit unsigned integer that can fit each element.
/// - `NUM_ELEM_BITS == k`
///
/// The following must hold: `n >= m >= k`, i.e. `TContainer` must be at least as wide as `TElem`,
/// and `TElem` must be at least `NUM_ELEM_BITS` wide.
///
/// The length of the array is determined as `floor(n / k)`.
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
/// use nanovec::array::{NanoArray, NanoArrayBit};  // must also import the trait
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
pub struct NanoArrayBit<TContainer, TElem, const NUM_ELEM_BITS: usize>(
    TContainer, P<TElem>,
) where
    TContainer: PrimInt + Unsigned + CheckedShl + CheckedShr,
    TElem: PrimInt + Unsigned,
;

impl<TContainer, TElem, const NUM_ELEM_BITS: usize>
NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS>
    where
        TContainer: PrimInt + Unsigned + CheckedShl + CheckedShr,
        TElem: PrimInt + Unsigned,
{
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

    /// Converts this array into an iterator of its elements.
    ///
    /// See [struct-level docs](NanoArrayBit) for example.
    pub fn into_iter(self) -> impl Iterator<Item=TElem> {
        (0..Self::LENGTH).map(move |i| self.get_unchecked(i))
    }
}

impl<TContainer, TElem, const NUM_ELEM_BITS: usize>
NanoArray for NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS>
    where
        TContainer: PrimInt + Unsigned + CheckedShl + CheckedShr,
        TElem: PrimInt + Unsigned,
{
    type Packed = TContainer;
    type Element = TElem;
    const LENGTH: usize = Self::LENGTH;

    fn new() -> Self {
        Self::static_asserts();
        Self(TContainer::zero(), P)
    }

    fn from_packed(packed: TContainer) -> Self {
        Self::static_asserts();
        Self(packed & Self::container_mask(), P)
    }

    fn packed(self) -> TContainer { self.0 }

    fn max_elem() -> TElem { TElem::from(Self::elem_mask()).unwrap() }

    fn get_unchecked(self, i: usize) -> TElem {
        TElem::from((self.0 >> (i * NUM_ELEM_BITS)) & Self::elem_mask()).unwrap()
    }

    fn with_unchecked(self, i: usize, elem: TElem) -> Self {
        Self(
            ((self.0 & !Self::index_mask(i)) |
                ((TContainer::from(elem).unwrap() & Self::elem_mask()) << (i * NUM_ELEM_BITS))) &
                Self::container_mask(),
            P
        )
    }

    fn shift_high(self, n: usize) -> Self {
        Self(
            self.0.checked_shl((n * NUM_ELEM_BITS) as u32).unwrap_or(TContainer::zero()) &
                Self::container_mask(),
            P
        )
    }

    fn shift_low(self, n: usize) -> Self {
        Self(
            self.0.checked_shr((n * NUM_ELEM_BITS) as u32).unwrap_or(TContainer::zero()),
            P
        )
    }

    fn rotate_high(self, n: usize) -> Self {
        assert!(n <= Self::LENGTH);
        let mask = Self::prefix_mask(Self::LENGTH - n);
        let right_to_left = (self.0 & mask)
            .checked_shl((NUM_ELEM_BITS * n) as u32)
            .unwrap_or(TContainer::zero());
        let left_to_right = self.0
            .checked_shr((NUM_ELEM_BITS * (Self::LENGTH - n)) as u32)
            .unwrap_or(TContainer::zero());
        Self(
            right_to_left | left_to_right,
            P
        )
    }
}

impl<TContainer, TElem, const NUM_ELEM_BITS: usize>
Default for NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS>
    where
        TContainer: PrimInt + Unsigned + CheckedShl + CheckedShr,
        TElem: PrimInt + Unsigned,
{
    fn default() -> Self { Self::new() }
}

impl<TContainer, TElem, const NUM_ELEM_BITS: usize>
From<TContainer> for NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS>
    where
        TContainer: PrimInt + Unsigned + CheckedShl + CheckedShr,
        TElem: PrimInt + Unsigned,
{
    fn from(packed: TContainer) -> Self {
        Self::from_packed(packed)
    }
}

impl<TContainer, TElem, const NUM_ELEM_BITS: usize>
FromIterator<TElem> for NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS>
    where
        TContainer: PrimInt + Unsigned + CheckedShl + CheckedShr,
        TElem: PrimInt + Unsigned,
{
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

impl<'a, TContainer, TElem, const NUM_ELEM_BITS: usize>
FromIterator<&'a TElem> for NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS>
    where
        TContainer: PrimInt + Unsigned + CheckedShl + CheckedShr,
        TElem: PrimInt + Unsigned + 'a,
{
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

impl<TContainer, TElem, const NUM_ELEM_BITS: usize>
Debug for NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS>
    where
        TContainer: PrimInt + Unsigned + CheckedShl + CheckedShr,
        TElem: PrimInt + Unsigned + Debug,
{
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

// TODO(summivox): rust (associated impl trait) for IntoIterator
/*
impl<TContainer: PrimInt + Unsigned, TElem: PrimInt + Unsigned, TFn: Fn(usize) -> TElem, const NUM_ELEM_BITS: usize>
IntoIterator for NanoArray<TContainer, TElem, NUM_ELEM_BITS> {
    type Item = TElem;
    type IntoIter = impl Iterator<Item=TElem>;

    fn into_iter(self) -> Self::IntoIter { self.into_iter() }
}
*/

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get_64_12() {
        type A = NanoArrayBit<u64, u16, 12>;
        let a = A::from_packed(0x123456789ABCDEF);
        assert_eq!(a.get(0), 0xDEF);
        assert_eq!(a.get(1), 0xABC);
        assert_eq!(a.get(2), 0x789);
        assert_eq!(a.get(3), 0x456);
        assert_eq!(a.get(4), 0x123);
    }

    #[test]
    fn with_set_64_12() {
        type A = NanoArrayBit<u64, u16, 12>;
        let a = A::from_packed(0x123456789ABCDEF);
        assert_eq!(a.with(1, 0x321).packed(), 0x123456789321DEF);
        let mut aa = a;
        aa.set(4, 0xFFF);
        assert_eq!(aa.packed(), 0xFFF456789ABCDEF);
        assert_eq!(aa.unpacked(), [0xDEF, 0xABC, 0x789, 0x456, 0xFFF]);
    }

    #[test]
    fn shift_rotate_32_8() {
        type A = NanoArrayBit<u32, u8, 8>;
        let a = A::from_iter([0xA, 0xB, 0xC, 0xD]);

        assert_eq!(a.shift_high(0), a);
        assert_eq!(a.shift_high(1), A::from_iter([0x0, 0xA, 0xB, 0xC]));
        assert_eq!(a.shift_high(2), A::from_iter([0x0, 0x0, 0xA, 0xB]));
        assert_eq!(a.shift_high(3), A::from_iter([0x0, 0x0, 0x0, 0xA]));
        assert_eq!(a.shift_high(4), A::from_iter([0x0, 0x0, 0x0, 0x0]));

        assert_eq!(a.shift_low(0), a);
        assert_eq!(a.shift_low(1), A::from_iter([0xB, 0xC, 0xD, 0x0]));
        assert_eq!(a.shift_low(2), A::from_iter([0xC, 0xD, 0x0, 0x0]));
        assert_eq!(a.shift_low(3), A::from_iter([0xD, 0x0, 0x0, 0x0]));
        assert_eq!(a.shift_low(4), A::from_iter([0x0, 0x0, 0x0, 0x0]));

        assert_eq!(a.rotate_high(0), a);
        assert_eq!(a.rotate_high(1), A::from_iter([0xD, 0xA, 0xB, 0xC]));
        assert_eq!(a.rotate_high(2), A::from_iter([0xC, 0xD, 0xA, 0xB]));
        assert_eq!(a.rotate_high(3), A::from_iter([0xB, 0xC, 0xD, 0xA]));
        assert_eq!(a.rotate_high(4), a);

        assert_eq!(a.rotate_low(0), a);
        assert_eq!(a.rotate_low(1), A::from_iter([0xB, 0xC, 0xD, 0xA]));
        assert_eq!(a.rotate_low(2), A::from_iter([0xC, 0xD, 0xA, 0xB]));
        assert_eq!(a.rotate_low(3), A::from_iter([0xD, 0xA, 0xB, 0xC]));
        assert_eq!(a.rotate_low(4), a);
    }
}
