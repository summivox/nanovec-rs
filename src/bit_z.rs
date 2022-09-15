use core::{
    fmt::{Debug, Formatter},
};

use num_traits::PrimInt;

use super::NanoArrayBit;

/// Represents a bounded stack of unsigned integers in the range `1..(1 << NUM_ELEM_BITS)`,
/// stored as a wider unsigned integer with each element taking up exactly `NUM_ELEM_BITS`.
///
/// - `TContainer`: an unsigned integer storing all elements in the stack (`n` bits).
/// - `TElem`: an unsigned integer that can fit each element (`m` bits).
/// - `NUM_ELEM_BITS == k`: determines the range of each element (`k` bits).
///
/// The following must hold: `n >= m >= k`, i.e. `TContainer` must be at least as wide as `TElem`,
/// and `TElem` must be at least `NUM_ELEM_BITS` wide.
///
/// This stack can fit at most `floor(n / k)` elements, which is available as [`Self::CAPACITY`]
/// and [`Self::capacity()`].
///
/// ## Summary of supported operations
///
/// - {Immutable,Mutable} {push,pop} at the top of the stack.
/// - Partitioning the stack into top and everything else.
/// - Get element at index.
///
/// ## Iterator support
///
/// - This stack is [`Copy`] and self-iterates (directly implementing [`Iterator`]).
///   A non-consuming iterator can be emulated using `.clone()`.
/// - This stack implements [`FromIterator`] and can therefore be [`Iterator::collect`]ed into.
///
/// Example:
/// ```
/// use nanovec::NanoVecBitZ;
/// type V = NanoVecBitZ::<u64, u16, 12>;
/// let v = [0x123, 0x456, 0x789, 0xABC, 0xDEF].iter().collect::<V>();
/// assert_eq!(v.clone().collect::<Vec<_>>(), vec![0xDEF, 0xABC, 0x789, 0x456, 0x123]);
/// // NOTE: The order is reversed because we pushed everything into a stack then popped them.
/// assert_eq!(v.top(), Some(0xDEF));
/// ```
///
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct NanoVecBitZ<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>(
    NanoArrayBit::<TContainer, TElem, NUM_ELEM_BITS>
);

// Avoid typing this out throughout the implementation.
// Usage: `<arr!()>::LENGTH`
macro_rules! arr {
    () => { NanoArrayBit::<TContainer, TElem, NUM_ELEM_BITS> };
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
NanoVecBitZ<TContainer, TElem, NUM_ELEM_BITS> {
    /// The maximum number of elements this stack can store.
    pub const CAPACITY: usize = <arr!()>::LENGTH;
    /// The maximum number of bits occupied in `TContainer`.
    pub const CAPACITY_BITS: usize = <arr!()>::LENGTH_BITS;

    ////////////////////////////////////////////////////////////////////
    // basics

    /// Creates an empty stack.
    pub fn new() -> Self {
        Self(<arr!()>::new())
    }

    /// Creates a stack from its bit-packed integer representation.
    pub fn from_packed(packed: TContainer) -> Self {
        Self(<arr!()>::from_packed(packed))
    }

    /// Converts the stack to its bit-packed integer representation.
    pub fn packed(self) -> TContainer {
        self.0.packed()
    }

    /// Returns whether this stack is empty.
    pub fn is_empty(self) -> bool {
        self.0.get_unchecked(0) == TElem::zero()
    }

    /// Returns whether this stack can fit no more elements.
    pub fn is_full(self) -> bool {
        self.cap_bottom_unchecked() != TElem::zero()
    }

    /// Returns how many elements are currently in the stack.
    pub fn len(self) -> usize {
        // Formula: ceil((N - clz) / K) == floor(((N + K - 1) - clz) / K)
        // Example (N = 64, K = 12):
        //     [4] [3] [2] [1] [0]
        // 0x0_000_000_000_000_000 => clz = 64, (N - clz) = 0, result = 0
        // 0x0_000_000_000_000_001 => clz = 63, (N - clz) = 1, result = 1
        // 0x0_000_000_000_000_800 => clz = 52, (N - clz) = 12, result = 1
        // 0x0_000_000_000_001_000 => clz = 51, (N - clz) = 13, result = 2
        // 0x0_000_000_000_800_000 => clz = 40, (N - clz) = 24, result = 2
        // ...
        // 0x0_001_000_000_000_000 => clz = 15, (N - clz) = 49, result = 5
        // 0x0_800_000_000_000_000 => clz = 4, (N - clz) = 60, result = 5
        let n = <arr!()>::NUM_CONTAINER_BITS;
        let k = NUM_ELEM_BITS;
        let clz = self.0.packed().leading_zeros() as usize;
        ((n + k - 1) - clz) / k
    }

    /// Returns the maximum number of elements this stack can store.
    pub const fn capacity(self) -> usize {
        Self::CAPACITY
    }

    ////////////////////////////////////////////////////////////////////
    // push

    /// Returns a new stack = this stack with an additional element on top
    /// (a.k.a. immutable push).
    /// Panics if the element is out of range, or the stack is full.
    pub fn with(self, elem: TElem) -> Self {
        assert!(elem != TElem::zero());
        assert!(!self.is_full());
        self.with_unchecked(elem)
    }

    /// Pushes an element onto the top of this stack.
    /// Panics if the element is out of range, or the stack is full.
    pub fn push(&mut self, elem: TElem) {
        assert!(elem != TElem::zero());
        assert!(!self.is_full());
        self.push_unchecked(elem);
    }

    /// Pushes an element on to the top of this stack.
    /// If the stack is full, removes and returns the element at the bottom of the stack;
    /// otherwise returns `None`.
    /// Panics if the pushed element is out of range.
    pub fn push_circular(&mut self, elem: TElem) -> Option<TElem> {
        assert!(elem != TElem::zero());
        let cap_last = self.cap_bottom_unchecked();
        self.push_unchecked(elem);
        if cap_last != TElem::zero() { Some(cap_last) } else { None }
    }

    /// Returns a new stack = this stack with an additional element on top
    /// (immutable push).
    /// If the original stack is full, the element at the bottom of the stack will be removed in
    /// the new stack.
    pub fn with_unchecked(self, elem: TElem) -> Self {
        Self(self.0.shl(1).with(0, elem))
    }

    /// Pushes an element on to the top of this stack.
    /// If the stack is full, removes the element silently at the bottom of the stack.
    pub fn push_unchecked(&mut self, elem: TElem) {
        self.0 = self.0.shl(1).with(0, elem)
    }

    /// Returns the element at the top of the stack, or `None` if the stack is empty.
    pub fn top(self) -> Option<TElem> {
        let elem = self.top_unchecked();
        if elem != TElem::zero() { Some(elem) } else { None }
    }

    /// Returns the element at the top of the stack, or `0` if the stack is empty.
    /// Note that elements are not allowed to be `0` to begin with.
    pub fn top_unchecked(self) -> TElem {
        self.0.get_unchecked(0)
    }

    /// Returns the element at the bottom of the stack if the stack is full; otherwise `None`.
    pub fn cap_bottom(self) -> Option<TElem> {
        let elem = self.cap_bottom_unchecked();
        if elem != TElem::zero() { Some(elem) } else { None }
    }

    /// Returns the element at the bottom of the stack if the stack is full; otherwise `0`.
    /// Note that elements are not allowed to be `0` to begin with.
    pub fn cap_bottom_unchecked(self) -> TElem {
        self.0.get_unchecked(Self::CAPACITY - 1)
    }

    /// Returns a stack with all elements of this stack except for the one on top
    /// (a.k.a. immutable pop).
    /// When the original stack is empty, returns an empty stack.
    pub fn rest(self) -> Self {
        Self(self.0.shr(1))
    }

    /// Partitions the stack into the top element + all other elements in a stack.
    /// Returns `None` if the stack is empty.
    pub fn top_rest(self) -> Option<(TElem, Self)> {
        let elem = self.top_unchecked();
        if elem != TElem::zero() { Some((elem, self.rest())) } else { None }
    }

    /// Partitions the stack into the top element + all other elements in a stack.
    /// Returns `0` + empty stack if the original stack is empty.
    pub fn top_rest_unchecked(self) -> (TElem, Self) {
        (self.top_unchecked(), self.rest())
    }

    /// Returns the `i`-th element from the top of the stack; `None` if the element does not exist.
    /// e.g. `get(0)` returns the top, `get(1)` returns the one just below it, etc.
    pub fn get(self, i: usize) -> Option<TElem> {
        let elem = self.get_unchecked(i);
        if elem != TElem::zero() { Some(elem) } else { None }
    }

    /// Returns the `i`-th element from the top of the stack; `0` if the element does not exist.
    /// e.g. `get(0)` returns the top, `get(1)` returns the one just below it, etc.
    /// Note that elements are not allowed to be `0` to begin with.
    pub fn get_unchecked(self, i: usize) -> TElem {
        self.0.get_unchecked(i)
    }

    /// Removes the element on top and returns it; `None` if the stack is empty.
    pub fn pop(&mut self) -> Option<TElem> {
        let (elem, rest) = self.top_rest_unchecked();
        self.0 = rest.0;
        if elem != TElem::zero() { Some(elem) } else { None }
    }
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
Default for NanoVecBitZ<TContainer, TElem, NUM_ELEM_BITS> {
    fn default() -> Self { Self::new() }
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
From<TContainer> for NanoVecBitZ<TContainer, TElem, NUM_ELEM_BITS> {
    fn from(packed: TContainer) -> Self {
        Self::from_packed(packed)
    }
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
From<arr!()> for NanoVecBitZ<TContainer, TElem, NUM_ELEM_BITS> {
    fn from(a: arr!()) -> Self { Self(a) }
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
FromIterator<TElem> for NanoVecBitZ<TContainer, TElem, NUM_ELEM_BITS> {
    fn from_iter<T: IntoIterator<Item=TElem>>(iter: T) -> Self {
        let mut v = Self::new();
        for elem in iter {
            v.push(elem);
        }
        v
    }
}

impl<'a, TContainer: PrimInt, TElem: PrimInt + 'a, const NUM_ELEM_BITS: usize>
FromIterator<&'a TElem> for NanoVecBitZ<TContainer, TElem, NUM_ELEM_BITS> {
    fn from_iter<T: IntoIterator<Item=&'a TElem>>(iter: T) -> Self {
        let mut v = Self::new();
        for elem in iter {
            v.push(*elem);
        }
        v
    }
}

impl<TContainer: PrimInt, TElem: PrimInt, const NUM_ELEM_BITS: usize>
Iterator for NanoVecBitZ<TContainer, TElem, NUM_ELEM_BITS> {
    type Item = TElem;
    fn next(&mut self) -> Option<Self::Item> { self.pop() }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(Self::CAPACITY))
    }
}

impl<TContainer: PrimInt, TElem: PrimInt + Debug, const NUM_ELEM_BITS: usize>
Debug for NanoVecBitZ<TContainer, TElem, NUM_ELEM_BITS> {
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
    use std::vec;
    use std::vec::Vec;
    use super::*;

    #[test]
    fn test_64_16_12() {
        type V = NanoVecBitZ::<u64, u16, 12>;
        assert_eq!(V::CAPACITY, 5);

        let a = V::new();
        assert_eq!(a.0, 0.into());
        assert_eq!(a.len(), 0);
        let b = a.with(0x123);
        assert_eq!(b.0, 0x123.into());
        assert_eq!(b.len(), 1);
        let c = b.with(0x456);
        assert_eq!(c.0, 0x123456.into());
        assert_eq!(c.len(), 2);
        let e = c.with(0x789).with(0xABC);
        assert_eq!(e.0, 0x123456789ABC.into());
        assert_eq!(e.len(), 4);
        let f = e.with(0xDEF);
        assert_eq!(f.0, 0x123456789ABCDEF.into());
        assert_eq!(f.len(), 5);
        let g = f.with_unchecked(0x321);
        assert_eq!(g.0, 0x456789ABCDEF321.into());
        assert_eq!(g.len(), 5);

        assert_eq!(a.with(0xFFF).with(0xFFF).len(), 2);

        assert_eq!(a.top(), None);
        assert_eq!(b.top(), Some(0x123));
        assert_eq!(c.top(), Some(0x456));
        assert_eq!(e.top(), Some(0xABC));
        assert_eq!(f.top(), Some(0xDEF));
        assert_eq!(g.top(), Some(0x321));

        assert_eq!(a.top_rest(), None);
        assert_eq!(b.top_rest(), Some((0x123, a)));
        assert_eq!(c.top_rest(), Some((0x456, b)));
        assert_eq!(e.top_rest(), Some((0xABC, c.with(0x789))));
        assert_eq!(f.top_rest(), Some((0xDEF, e)));

        let mut aa = a;
        aa.push(0x123);
        assert_eq!(aa, b);
        aa.push(0x456);
        assert_eq!(aa, c);
        aa.push(0x789);
        aa.push(0xABC);
        assert_eq!(aa, e);
        aa.push(0xDEF);
        assert_eq!(aa, f);
        aa.push_unchecked(0x321);
        assert_eq!(aa, g);

        let mut aa = a;
        assert_eq!(aa.push_circular(0x123), None);
        assert_eq!(aa, b);
        assert_eq!(aa.push_circular(0x456), None);
        assert_eq!(aa, c);
        assert_eq!(aa.push_circular(0x789), None);
        assert_eq!(aa.push_circular(0xABC), None);
        assert_eq!(aa, e);
        assert_eq!(aa.push_circular(0xDEF), None);
        assert_eq!(aa, f);
        assert_eq!(aa.push_circular(0x321), Some(0x123));
        assert_eq!(aa, g);

        let mut ff = f;
        assert_eq!(ff.pop(), Some(0xDEF));
        assert_eq!(ff.pop(), Some(0xABC));
        assert_eq!(ff.pop(), Some(0x789));
        assert_eq!(ff.pop(), Some(0x456));
        assert_eq!(ff.pop(), Some(0x123));
        assert_eq!(ff.pop(), None);

        assert_eq!(f.get(0), Some(0xDEF));
        assert_eq!(f.get(1), Some(0xABC));
        assert_eq!(f.get(2), Some(0x789));
        assert_eq!(f.get(3), Some(0x456));
        assert_eq!(f.get(4), Some(0x123));

        assert_eq!(f.collect::<Vec<_>>(),
                   vec![0xDEF, 0xABC, 0x789, 0x456, 0x123]);
        assert_eq!([0x123, 0x456, 0x789, 0xABC, 0xDEF].iter().collect::<V>(), f);
    }

    #[test]
    fn test_conv() {
        type V = NanoVecBitZ::<u64, u16, 12>;
        let a = V::new().with(0x123).with(0x456);
        let x = a.0;
        let xa = V::from(x);
        let y = a.packed();
        let ya = V::from(y);
        assert_eq!(xa, a);
        assert_eq!(ya, a);
    }

    #[test]
    fn test_32_8() {
        type V = NanoVecBitZ<u32, u8, 8>;
        let a = V::new().with(0x11).with(0x55).with(0x99).with(0xDD);
        assert_eq!(a.0, 0x115599DD.into());
        assert_eq!(a.collect::<Vec<_>>(),
                   vec![0xDD, 0x99, 0x55, 0x11]);
        let mut aa = a;
        assert_eq!(aa.push_circular(0x33), Some(0x11));
        assert_eq!(aa.0, 0x5599DD33.into());
        assert_eq!(aa.collect::<Vec<_>>(),
                   vec![0x33, 0xDD, 0x99, 0x55]);
        assert_eq!(aa,
                   [0x55, 0x99, 0xDD, 0x33].iter().collect::<V>());
    }

    #[test]
    fn print_it() {
        std::println!("{:?}", NanoVecBitZ::<u64, u16, 12>::new()
            .with(1).with(2).with(3).with(0xfff).with(0x800).clone());
    }
}
