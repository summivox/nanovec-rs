use core::{
    fmt::{Debug, Formatter},
};

use num_traits::PrimInt;

use super::NanoArrayBit;

/// Represents a bounded double-ended queue (deque) of unsigned integers in the range
/// `0..(1 << NUM_ELEM_BITS)`, stored as the number of elements (`u8`) + a wider unsigned integer
/// with each element taking up exactly `NUM_ELEM_BITS`.
///
/// - `TContainer`: an unsigned integer storing all elements in the deque (`n` bits).
/// - `TElem`: an unsigned integer that can fit each element (`m` bits).
/// - `NUM_ELEM_BITS == k`: determines the range of each element (`k` bits).
///
/// The following must hold: `n >= m >= k`, i.e. `TContainer` must be at least as wide as `TElem`,
/// and `TElem` must be at least `NUM_ELEM_BITS` wide.
///
/// This deque can fit at most `floor(n / k)` elements, which is available as [`Self::CAPACITY`]
/// and [`Self::capacity()`].
///
/// ## Summary of supported operations
///
/// - {Immutable,Mutable} {push,pop} {front,back} of the deque (hence the name).
/// - Get and {Immutable,Mutable} set element at index.
///
/// ## Iterator support
///
/// - This deque is [`Copy`] and self-iterates (directly implementing [`Iterator`]).
///   A non-consuming iterator can be emulated using `.clone()`.
/// - This deque implements [`FromIterator`] and can therefore be [`Iterator::collect`]ed into.
///
/// Example:
/// ```
/// use nanovec::NanoVecBitN;
/// type V = NanoVecBitN<u64, u16, 12>;
/// let v = [0x123, 0x456, 0x789, 0xABC, 0xDEF].iter().collect::<V>();
/// assert_eq!(v.front(), Some(0x123));
/// assert_eq!(v.clone().collect::<Vec<_>>(), vec![0x123, 0x456, 0x789, 0xABC, 0xDEF]);
/// assert_eq!(v.back(), Some(0xDEF));
/// ```
///
#[derive(Copy, Clone)]
pub struct NanoVecBitN<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize> {
    a: NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS>,
    n: u8,
}

// Avoid typing this out throughout the implementation.
// Usage: `<arr!()>::LENGTH`
macro_rules! arr {
    () => { NanoArrayBit::<TContainer, TElem, NUM_ELEM_BITS> };
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
NanoVecBitN<TContainer, TElem, NUM_ELEM_BITS> {
    /// The maximum number of elements this stack can store.
    pub const CAPACITY: usize = <arr!()>::LENGTH;
    /// The maximum number of bits occupied in `TContainer`.
    pub const CAPACITY_BITS: usize = <arr!()>::LENGTH_BITS;

    /// Creates an empty deque.
    pub fn new() -> Self {
        Self {
            a: <arr!()>::new(),
            n: 0,
        }
    }

    /// Creates a deque from its bit-packed integer representation + length.
    /// Panics if `len > capacity`.
    pub fn from_packed_len(packed: TContainer, len: u8) -> Self {
        assert!(len <= Self::CAPACITY as u8);
        Self {
            a: <arr!()>::from_packed(packed),
            n: len,
        }
    }
    /// Converts the deque to its bit-packed integer representation + length.
    pub fn to_packed_len(self) -> (TContainer, u8) { (self.a.packed(), self.n) }
    /// Converts the deque to its bit-packed integer representation (no length).
    pub fn packed(self) -> TContainer { self.a.packed() }
    /// Returns how many elements are currently in the deque.
    pub fn len(self) -> usize { self.n as usize }

    /// Returns if this deque is empty.
    pub fn is_empty(self) -> bool { self.n == 0 }
    /// Returns if this deque can fit no more elements.
    pub fn is_full(self) -> bool { self.n == Self::CAPACITY as u8 }
    /// Returns the maximum number of elements this deque can store.
    pub fn capacity(self) -> usize { Self::CAPACITY }

    ////////////////////////////////////////////////////////////////////
    // push

    /// Returns a new deque = this deque with an additional element added to the front
    /// (a.k.a. immutable push front).
    /// Panics if this deque is full.
    pub fn with_front(self, elem: TElem) -> Self {
        assert!(!self.is_full());
        self.with_front_circular(elem)
    }

    /// Returns a new deque = this deque with an additional element added to the back
    /// (a.k.a. immutable push back).
    /// Panics if this deque is full.
    pub fn with_back(self, elem: TElem) -> Self {
        assert!(!self.is_full());
        self.with_back_circular(elem)
    }

    /// Pushes an element to the front of this deque.
    /// Panics if this deque is full.
    pub fn push_front(&mut self, elem: TElem) {
        assert!(!self.is_full());
        self.a = self.a.shl(1).with(0, elem);
        self.n += 1;
    }

    /// Pushes an element to the back of this deque.
    /// Panics if this deque is full.
    pub fn push_back(&mut self, elem: TElem) {
        assert!(!self.is_full());
        self.a = self.a.with(self.n as usize, elem);
        self.n += 1;
    }

    /// Pushes an element to the front of this deque.
    /// If the deque is full, removes and returns the element at the back; otherwise `None`.
    pub fn push_front_circular(&mut self, elem: TElem) -> Option<TElem> {
        let cap_back = if self.is_full() {
            Some(self.cap_back_unchecked())
        } else {
            None
        };
        *self = self.with_front_circular(elem);
        cap_back
    }

    /// Pushes an element to the back of this deque.
    /// If the deque is full, removes and returns the element at the front; otherwise `None`.
    pub fn push_back_circular(&mut self, elem: TElem) -> Option<TElem> {
        let front = if self.is_full() { self.front() } else { None };
        *self = self.with_back_circular(elem);
        front
    }

    /// Returns a new deque = this deque with an additional element added to the front,
    /// and the element at the back removed if the original deque is full.
    pub fn with_front_circular(self, elem: TElem) -> Self {
        Self {
            a: self.a.shl(1).with(0, elem),
            n: if self.is_full() { self.n } else { self.n + 1 },
        }
    }

    /// Returns a new deque = this deque with an additional element added to the back,
    /// and the element at the front removed if the original deque is full.
    pub fn with_back_circular(self, elem: TElem) -> Self {
        if self.is_full() {
            Self {
                a: self.a.shr(1).with(Self::CAPACITY - 1, elem),
                n: self.n,
            }
        } else {
            Self {
                a: self.a.with(self.n as usize, elem),
                n: self.n + 1,
            }
        }
    }

    ////////////////////////////////////////////////////////////////////
    // get

    /// Returns the element at the front of the deque, or `None` if the deque is empty.
    pub fn front(self) -> Option<TElem> {
        (self.n > 0).then(|| self.front_unchecked())
    }

    /// Returns the element at the back of the deque, or `None` if the deque is empty.
    pub fn back(self) -> Option<TElem> {
        (self.n > 0).then(|| self.back_unchecked())
    }

    /// Returns the element at the back of the deque when the deque is full; `None` otherwise.
    pub fn cap_back(self) -> Option<TElem> {
        self.is_full().then(|| self.cap_back_unchecked())
    }

    /// Returns the element at the front of the deque.
    /// The result can be anything if the deque is empty.
    pub fn front_unchecked(self) -> TElem {
        self.a.get_unchecked(0)
    }

    /// Returns the element at the back of the deque.
    /// The result can be anything if the deque is empty.
    pub fn back_unchecked(self) -> TElem {
        self.a.get_unchecked(self.n as usize - 1)
    }

    /// Returns the element at the back of the deque when the deque is full.
    /// The result can be anything otherwise.
    pub fn cap_back_unchecked(self) -> TElem {
        self.a.get_unchecked(Self::CAPACITY - 1)
    }

    ////////////////////////////////////////////////////////////////////
    // index

    /// Returns the `i`-th element from the front; `None` if the index is out of bounds.
    pub fn get(self, i: usize) -> Option<TElem> {
        (i < self.n as usize).then(|| self.get_unchecked(i))
    }

    /// Returns a new deque = this deque with the `i`-th element from the front set to `elem`
    /// (a.k.a. immutable set index).
    /// Panics if the index is out of bounds.
    pub fn with(self, i: usize, elem: TElem) -> Self {
        assert!(i < self.n as usize);
        self.with_unchecked(i, elem)
    }

    /// Sets the `i`-th element from the front to `elem`.
    /// Panics if the index is out of bounds.
    pub fn set(&mut self, i: usize, elem: TElem) {
        assert!(i < self.n as usize);
        self.set_unchecked(i, elem);
    }

    /// Returns the `i`-th element from the front.
    /// The result can be anything if the index is out of bounds.
    pub fn get_unchecked(self, i: usize) -> TElem {
        self.a.get_unchecked(i)
    }

    /// Returns a new deque = this deque with the `i`-th element from the front set to `elem`
    /// (a.k.a. immutable set index).
    /// No-op if the index is out of bounds.
    pub fn with_unchecked(self, i: usize, elem: TElem) -> Self {
        Self {
            a: self.a.with_unchecked(i, elem),
            n: self.n,
        }
    }

    /// Set the `i`-th element from the front to `elem`.
    /// No-op if the index is out of bounds.
    pub fn set_unchecked(&mut self, i: usize, elem: TElem) {
        self.a.set_unchecked(i, elem);
    }

    ////////////////////////////////////////////////////////////////////
    // pop

    /// Returns a new deque = this deque without its front element (if any).
    /// Equivalent to an immutable [`Self::pop_front()`].
    pub fn without_front(self) -> Self {
        Self {
            a: self.a.shr(1),
            n: if self.n == 0 { 0 } else { self.n - 1 },
        }
    }

    /// Returns a new deque = this deque without its back element (if any).
    /// Equivalent to an immutable [`Self::pop_back()`].
    pub fn without_back(self) -> Self {
        Self {
            a: self.a,  // fake delete
            n: if self.n == 0 { 0 } else { self.n - 1 },
        }
    }

    /// Removes the front element from this deque and returns it;
    /// `None` if the deque is empty.
    pub fn pop_front(&mut self) -> Option<TElem> {
        if self.n == 0 { return None; }
        let front = self.front_unchecked();
        self.a = self.a.shr(1);
        self.n -= 1;
        Some(front)
    }

    /// Removes the back element from this deque and returns it;
    /// `None` if the deque is empty.
    pub fn pop_back(&mut self) -> Option<TElem> {
        if self.n == 0 { return None; }
        let back = self.back_unchecked();
        // fake delete
        self.n -= 1;
        Some(back)
    }
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
Default for NanoVecBitN<TContainer, TElem, NUM_ELEM_BITS> {
    fn default() -> Self { Self::new() }
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
Iterator for NanoVecBitN<TContainer, TElem, NUM_ELEM_BITS> {
    type Item = TElem;
    fn next(&mut self) -> Option<Self::Item> { self.pop_front() }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.n as usize, Some(self.n as usize))
    }
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
FromIterator<TElem> for NanoVecBitN<TContainer, TElem, NUM_ELEM_BITS> {
    fn from_iter<T: IntoIterator<Item=TElem>>(iter: T) -> Self {
        let mut v = Self::new();
        for elem in iter {
            v.push_back(elem);
        }
        v
    }
}

impl<'a, TContainer: PrimInt, TElem: PrimInt + 'a, const NUM_ELEM_BITS: usize>
FromIterator<&'a TElem> for NanoVecBitN<TContainer, TElem, NUM_ELEM_BITS> {
    fn from_iter<T: IntoIterator<Item=&'a TElem>>(iter: T) -> Self {
        let mut v = Self::new();
        for elem in iter {
            v.push_back(*elem);
        }
        v
    }
}

// Custom eq is needed --- unused parts of the packed value should be masked off.
impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
PartialEq for NanoVecBitN<TContainer, TElem, NUM_ELEM_BITS> {
    fn eq(&self, other: &Self) -> bool {
        if self.n != other.n { return false; }
        let mask = <arr!()>::prefix_mask(self.n as usize);
        self.a.packed() & mask == other.a.packed() & mask
    }
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
Eq for NanoVecBitN<TContainer, TElem, NUM_ELEM_BITS> {}

impl<TContainer: PrimInt, TElem: PrimInt + Debug, const NUM_ELEM_BITS: usize>
Debug for NanoVecBitN<TContainer, TElem, NUM_ELEM_BITS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "[")?;
        let mut first = true;
        for elem in *self {
            if first {
                first = false;
                write!(f, "{:?}", elem)?;
            } else {
                write!(f, ", {:?}", elem)?;
            }
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;

    #[test]
    fn test_32_8_4_push_pop() {
        type V = NanoVecBitN::<u32, u8, 4>;
        assert_eq!(V::CAPACITY, 8);

        let v00 = V::new();
        assert_eq!(v00, V { a: 0x00000000.into(), n: 0 });

        // with_{front,back}
        let v01 = v00.with_back(0x0);
        assert_eq!(v01, V { a: 0x00000000.into(), n: 1 });
        let v02 = v01.with_back(0x1);
        assert_eq!(v02, V { a: 0x00000010.into(), n: 2 });
        let v03 = v02.with_back(0x2);
        assert_eq!(v03, V { a: 0x00000210.into(), n: 3 });
        let v13 = v03.with_front(0xF);
        assert_eq!(v13, V { a: 0x0000210F.into(), n: 4 });
        let v23 = v13.with_front(0xE);
        assert_eq!(v23, V { a: 0x000210FE.into(), n: 5 });
        let v24 = v23.with_back(0x3);
        assert_eq!(v24, V { a: 0x003210FE.into(), n: 6 });
        let v34 = v24.with_front(0x9);
        assert_eq!(v34, V { a: 0x03210FE9.into(), n: 7 });
        let v35 = v34.with_back(0xA);
        assert_eq!(v35, V { a: 0xA3210FE9.into(), n: 8 });

        // from/to
        assert_eq!(v35.to_packed_len(), (0xA3210FE9, 8));
        assert_eq!(v35, V::from_packed_len(0xA3210FE9, 8));

        // without_{front,back}
        let vv34 = v35.without_back();
        assert_eq!(vv34, v34);
        let vv24 = v34.without_front();
        assert_eq!(vv24, v24);
        let vv23 = v24.without_back();
        assert_eq!(vv23, v23);
        let vv13 = v23.without_front();
        assert_eq!(vv13, v13);
        let vv03 = v13.without_front();
        assert_eq!(vv03, v03);
        let vv02 = v03.without_back();
        assert_eq!(vv02, v02);
        let vv01 = v02.without_back();
        assert_eq!(vv01, v01);
        let vv00 = v01.without_back();
        assert_eq!(vv00, v00);

        // push_{front,back}
        let mut vv = V::new();
        vv.push_back(0x0);
        assert_eq!(vv, v01);
        vv.push_back(0x1);
        assert_eq!(vv, v02);
        vv.push_back(0x2);
        assert_eq!(vv, v03);
        vv.push_front(0xF);
        assert_eq!(vv, v13);
        vv.push_front(0xE);
        assert_eq!(vv, v23);
        vv.push_back(0x3);
        assert_eq!(vv, v24);
        vv.push_front(0x9);
        assert_eq!(vv, v34);
        vv.push_back(0xA);
        assert_eq!(vv, v35);

        // pop_{front,back}
        assert_eq!(vv.pop_back(), Some(0xA));
        assert_eq!(vv, v34);
        assert_eq!(vv.pop_front(), Some(0x9));
        assert_eq!(vv, v24);
        assert_eq!(vv.pop_back(), Some(0x3));
        assert_eq!(vv, v23);
        assert_eq!(vv.pop_front(), Some(0xE));
        assert_eq!(vv, v13);
        assert_eq!(vv.pop_front(), Some(0xF));
        assert_eq!(vv, v03);
        assert_eq!(vv.pop_back(), Some(0x2));
        assert_eq!(vv, v02);
        assert_eq!(vv.pop_back(), Some(0x1));
        assert_eq!(vv, v01);
        assert_eq!(vv.pop_back(), Some(0x0));
        assert_eq!(vv, v00);
        assert_eq!(vv.pop_back(), None);
        assert_eq!(vv, v00);
    }

    #[test]
    fn test_32_8_4_pop_then_push() {
        type V = NanoVecBitN::<u32, u8, 4>;
        let v34 = V { a: 0x03210FE9.into(), n: 7 };

        let mut vv = v34;
        assert_eq!(vv.pop_back(), Some(0x3));
        assert_eq!(vv.pop_back(), Some(0x2));
        vv.push_back(0xD);
        assert_eq!(vv.back(), Some(0xD));
        assert_eq!(vv, V { a: 0x00D10FE9.into(), n: 6 });
        vv.push_back(0xC);
        assert_eq!(vv.back(), Some(0xC));
        assert_eq!(vv, V { a: 0x0CD10FE9.into(), n: 7 });

        let mut vv = v34;
        assert_eq!(vv.pop_front(), Some(0x9));
        vv.push_front(0x6);
        assert_eq!(vv.front(), Some(0x6));
        assert_eq!(vv, V { a: 0x03210FE6.into(), n: 7 });
    }

    #[test]
    fn test_32_8_4_push_circular() {
        type V = NanoVecBitN::<u32, u8, 4>;
        let v34 = V { a: 0x03210FE9.into(), n: 7 };

        // push_{front,back}_circular (indirectly tests {front,back})

        let mut vv = v34;
        assert_eq!(vv.push_back_circular(0xA), None);
        assert_eq!(vv, V { a: 0xA3210FE9.into(), n: 8 });
        assert_eq!(vv.push_back_circular(0xB), Some(0x9));
        assert_eq!(vv, V { a: 0xBA3210FE.into(), n: 8 });
        assert_eq!(vv.push_back_circular(0xC), Some(0xE));
        assert_eq!(vv, V { a: 0xCBA3210F.into(), n: 8 });
        assert_eq!(vv.push_back_circular(0xD), Some(0xF));
        assert_eq!(vv, V { a: 0xDCBA3210.into(), n: 8 });
        assert_eq!(vv.push_back_circular(0xE), Some(0x0));
        assert_eq!(vv, V { a: 0xEDCBA321.into(), n: 8 });

        let mut vv = v34;
        assert_eq!(vv.push_front_circular(0xA), None);
        assert_eq!(vv, V { a: 0x3210FE9A.into(), n: 8 });
        assert_eq!(vv.push_front_circular(0xB), Some(0x3));
        assert_eq!(vv, V { a: 0x210FE9AB.into(), n: 8 });
        assert_eq!(vv.push_front_circular(0xC), Some(0x2));
        assert_eq!(vv, V { a: 0x10FE9ABC.into(), n: 8 });
        assert_eq!(vv.push_front_circular(0xD), Some(0x1));
        assert_eq!(vv, V { a: 0x0FE9ABCD.into(), n: 8 });
        assert_eq!(vv.push_front_circular(0xE), Some(0x0));
        assert_eq!(vv, V { a: 0xFE9ABCDE.into(), n: 8 });
    }

    #[test]
    fn test_32_8_4_index() {
        type V = NanoVecBitN::<u32, u8, 4>;
        let v34 = V { a: 0x03210FE9.into(), n: 7 };

        // get index
        for (i, elem) in [0x9, 0xE, 0xF, 0x0, 0x1, 0x2, 0x3].iter().enumerate() {
            assert_eq!(v34.get(i), Some(*elem));
        }

        // with index
        let v34_0 = v34.with(0, 0xC);
        assert_eq!(v34_0, V { a: 0x03210FEC.into(), n: 7 });
        assert_ne!(v34_0, v34);
        let v34_1 = v34.with(1, 0xC);
        assert_eq!(v34_1, V { a: 0x03210FC9.into(), n: 7 });
        assert_ne!(v34_1, v34);
        let v34_2 = v34.with(2, 0xC);
        assert_eq!(v34_2, V { a: 0x03210CE9.into(), n: 7 });
        assert_ne!(v34_2, v34);
        let v34_3 = v34.with(3, 0xC);
        assert_eq!(v34_3, V { a: 0x0321CFE9.into(), n: 7 });
        assert_ne!(v34_3, v34);
        let v34_4 = v34.with(4, 0xC);
        assert_eq!(v34_4, V { a: 0x032C0FE9.into(), n: 7 });
        assert_ne!(v34_4, v34);
        let v34_5 = v34.with(5, 0xC);
        assert_eq!(v34_5, V { a: 0x03C10FE9.into(), n: 7 });
        assert_ne!(v34_5, v34);
        let v34_6 = v34.with(6, 0xC);
        assert_eq!(v34_6, V { a: 0x0C210FE9.into(), n: 7 });
        assert_ne!(v34_6, v34);

        // set index
        let mut vv = v34;
        vv.set(6, 0xC);
        assert_eq!(vv, V { a: 0x0C210FE9.into(), n: 7 });
        vv.set(5, 0xB);
        assert_eq!(vv, V { a: 0x0CB10FE9.into(), n: 7 });
        vv.set(4, 0xA);
        assert_eq!(vv, V { a: 0x0CBA0FE9.into(), n: 7 });
        vv.set(3, 0x9);
        assert_eq!(vv, V { a: 0x0CBA9FE9.into(), n: 7 });
        vv.set(2, 0x8);
        assert_eq!(vv, V { a: 0x0CBA98E9.into(), n: 7 });
        vv.set(1, 0x7);
        assert_eq!(vv, V { a: 0x0CBA9879.into(), n: 7 });
        vv.set(0, 0x6);
        assert_eq!(vv, V { a: 0x0CBA9876.into(), n: 7 });
    }
}
