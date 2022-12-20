use core::{
    fmt::{Debug, Formatter},
};

use num_traits::Zero;

use crate::array::NanoArray;

/// A _zero-terminated_ stack of _non-zero_ unsigned integers backed by [`NanoArray`] alone.
/// Maximum number of elements (capacity) is the length of the underlying [`NanoArray`].
///
/// ## Summary of supported operations
///
/// - {Immutable,Mutable} {push,pop} at the top of the stack.
///
/// - Partitioning the stack into top and everything else.
///
/// - Get element at index (set is not allowed).
///
/// ## Iterator support
///
/// - This stack is [`Copy`] and self-iterates (directly implementing [`Iterator`]).
///   A non-consuming iterator can be emulated using `.clone()`.
///
/// - This stack implements [`FromIterator`] and can therefore be [`Iterator::collect`]ed into.
///
/// Example:
/// ```
/// use nanovec::NanoStackBit;
/// type V = NanoStackBit::<u64, u16, 12>;
/// let v = [0x123, 0x456, 0x789, 0xABC, 0xDEF].into_iter().collect::<V>();
/// assert_eq!(v.clone().collect::<Vec<_>>(), vec![0xDEF, 0xABC, 0x789, 0x456, 0x123]);
/// // NOTE: The order is reversed because we pushed everything into a stack then popped them.
/// assert_eq!(v.top(), Some(0xDEF));
/// ```
///
#[derive(Copy, Clone, Default, Eq, PartialEq)]
pub struct NanoStack<Array: NanoArray>(Array);

impl<Array: NanoArray>
NanoStack<Array> {
    pub const CAPACITY: usize = Array::LENGTH;

    /// Creates an empty stack.
    pub fn new() -> Self { Self(Array::new()) }

    /// Creates a stack from its packed [`NanoArray`].
    pub fn from_packed(packed: Array::Packed) -> Self { Self(Array::from_packed(packed)) }

    /// Creates a stack from its [`NanoArray`].
    pub fn from_array(array: Array) -> Self { Self(array) }

    /// Returns the inner packed [`NanoArray`].
    pub fn packed(self) -> Array::Packed { self.0.packed() }

    /// Returns the inner [`NanoArray`].
    pub fn array(self) -> Array { self.0 }

    /// Returns whether this stack is empty.
    pub fn is_empty(self) -> bool { self.top().is_none() }

    /// Returns whether this stack is full.
    pub fn is_full(self) -> bool { self.cap_bottom().is_some() }

    /// Returns the number of elements currently in the stack.
    pub fn len(self) -> usize {
        // TODO(summivox): backdoor arrays to optimize this?
        self.count()
    }

    /// Returns a new stack = this stack with an additional element on top
    /// (a.k.a. immutable push).
    /// Panics if the element is out of range, or the stack is full.
    pub fn with(self, elem: Array::Element) -> Self {
        assert!(elem != Array::Element::zero());
        assert!(!self.is_full());
        self.with_unchecked(elem)
    }

    /// Pushes an element onto the top of this stack.
    /// Panics if the element is out of range, or the stack is full.
    pub fn push(&mut self, elem: Array::Element) {
        assert!(elem != Array::Element::zero());
        assert!(!self.is_full());
        self.push_unchecked(elem);
    }

    /// Pushes an element on to the top of this stack.
    /// If the stack is full, removes and returns the element at the bottom of the stack;
    /// otherwise returns `None`.
    /// Panics if the pushed element is out of range.
    pub fn push_circular(&mut self, elem: Array::Element) -> Option<Array::Element> {
        assert!(elem != Array::Element::zero());
        let cap_last = self.cap_bottom_unchecked();
        self.push_unchecked(elem);
        if cap_last != Array::Element::zero() { Some(cap_last) } else { None }
    }

    /// Returns a new stack = this stack with an additional element on top
    /// (immutable push).
    /// If the original stack is full, the element at the bottom of the stack will be removed in
    /// the new stack.
    pub fn with_unchecked(self, elem: Array::Element) -> Self {
        Self(self.0.shift_high(1).with(0, elem))
    }

    /// Pushes an element on to the top of this stack.
    /// If the stack is full, removes the element silently at the bottom of the stack.
    pub fn push_unchecked(&mut self, elem: Array::Element) {
        self.0 = self.0.shift_high(1).with(0, elem)
    }

    /// Returns the element at the top of the stack, or `None` if the stack is empty.
    pub fn top(self) -> Option<Array::Element> {
        let elem = self.top_unchecked();
        if elem != Array::Element::zero() { Some(elem) } else { None }
    }

    /// Returns the element at the top of the stack, or `0` if the stack is empty.
    /// Note that elements are not allowed to be `0` to begin with.
    pub fn top_unchecked(self) -> Array::Element {
        self.0.get(0)
    }

    /// Returns the element at the bottom of the stack if the stack is full; otherwise `None`.
    pub fn cap_bottom(self) -> Option<Array::Element> {
        let elem = self.cap_bottom_unchecked();
        if elem != Array::Element::zero() { Some(elem) } else { None }
    }

    /// Returns the element at the bottom of the stack if the stack is full; otherwise `0`.
    /// Note that elements are not allowed to be `0` to begin with.
    pub fn cap_bottom_unchecked(self) -> Array::Element {
        self.0.get(Self::CAPACITY - 1)
    }

    /// Returns a stack with all elements of this stack except for the one on top
    /// (a.k.a. immutable pop).
    /// When the original stack is empty, returns an empty stack.
    pub fn rest(self) -> Self {
        Self(self.0.shift_low(1))
    }

    /// Partitions the stack into the top element + all other elements in a stack.
    /// Returns `None` if the stack is empty.
    pub fn top_rest(self) -> Option<(Array::Element, Self)> {
        let elem = self.top_unchecked();
        if elem != Array::Element::zero() { Some((elem, self.rest())) } else { None }
    }

    /// Partitions the stack into the top element + all other elements in a stack.
    /// Returns `0` + empty stack if the original stack is empty.
    pub fn top_rest_unchecked(self) -> (Array::Element, Self) {
        (self.top_unchecked(), self.rest())
    }

    /// Returns the `i`-th element from the top of the stack; `None` if the element does not exist.
    /// e.g. `get(0)` returns the top, `get(1)` returns the one just below it, etc.
    pub fn get(self, i: usize) -> Option<Array::Element> {
        let elem = self.get_unchecked(i);
        if elem != Array::Element::zero() { Some(elem) } else { None }
    }

    /// Returns the `i`-th element from the top of the stack; `0` if the element does not exist.
    /// e.g. `get(0)` returns the top, `get(1)` returns the one just below it, etc.
    /// Note that elements are not allowed to be `0` to begin with.
    pub fn get_unchecked(self, i: usize) -> Array::Element {
        self.0.get(i)
    }

    /// Removes the element on top and returns it; `None` if the stack is empty.
    pub fn pop(&mut self) -> Option<Array::Element> {
        let (elem, rest) = self.top_rest_unchecked();
        self.0 = rest.0;
        if elem != Array::Element::zero() { Some(elem) } else { None }
    }
}

/*
impl<Array: NanoArray>
From<Array::Packed> for NanoStack<Array> {
    fn from(packed: Array::Packed) -> Self {
        Self::from_packed(packed)
    }
}
*/

impl<Array: NanoArray>
From<Array> for NanoStack<Array> {
    fn from(a: Array) -> Self { Self(a) }
}

// NOTE: this cannot be implemented due to:
// https://stackoverflow.com/a/73791185/4876553
/*
impl<Array: NanoArray>
From<NanoStack<Array>> for Array {
    fn from(stack: NanoStack<Array>) -> Self {
        stack.0
    }
}
*/

impl<Array: NanoArray>
FromIterator<Array::Element> for NanoStack<Array> {
    fn from_iter<It: IntoIterator<Item=Array::Element>>(iter: It) -> Self {
        let mut v = Self::new();
        for elem in iter {
            v.push(elem);
        }
        v
    }
}

// TODO(summivox): rust (negative impl?) for FromIterator
/*
impl<'a, Array: NanoArray>
FromIterator<&'a Array::Element> for NanoStack<Array> {
    fn from_iter<It: IntoIterator<Item=&'a Array::Element>>(iter: It) -> Self {
        let mut v = Self::new();
        for elem in iter {
            v.push(*elem);
        }
        v
    }
}
*/

impl<Array: NanoArray>
Iterator for NanoStack<Array> {
    type Item = Array::Element;
    fn next(&mut self) -> Option<Self::Item> { self.pop() }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(Self::CAPACITY))
    }
}

impl<Array: NanoArray>
Debug for NanoStack<Array>
    where
        Array::Element: Debug {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "[")?;
        for (i, elem) in self.enumerate() {
            if i == 0 {
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
    use crate::NanoArrayBit;
    use super::*;

    #[test]
    fn pushes() {
        type S = NanoStack<[u8; 4]>;
        let a = S::new();
        assert_eq!(a.len(), 0);
        let b = a.with(0x12);
        assert_eq!(b.len(), 1);
        let c = b.with(0x34);
        assert_eq!(c.len(), 2);
        let e = c.with(0x56).with(0x78);

        let mut ee = e;
        assert_eq!(ee.len(), 4);
        assert_eq!(ee.pop(), Some(0x78));
        assert_eq!(ee.len(), 3);
        assert_eq!(ee.pop(), Some(0x56));
        assert_eq!(ee.len(), 2);
        assert_eq!(ee.pop(), Some(0x34));
        assert_eq!(ee.len(), 1);
        assert_eq!(ee.pop(), Some(0x12));
        assert_eq!(ee.len(), 0);
        assert_eq!(ee.pop(), None);

        // TODO(summivox): finish porting these
    }

    // TODO(summivox): test array and stack behaviors separately here

    #[test]
    fn test_64_16_12() {
        type V = NanoStack<NanoArrayBit<u64, u16, 12>>;
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
        assert_eq!([0x123, 0x456, 0x789, 0xABC, 0xDEF].into_iter().collect::<V>(), f);
    }

    #[test]
    fn test_conv() {
        type V = NanoStack<NanoArrayBit<u64, u16, 12>>;
        let a = V::new().with(0x123).with(0x456);
        let x = a.0;
        let xa = V::from(x);
        let y = a.packed();
        let ya = V::from(NanoArrayBit::<u64, u16, 12>::from(y));
        assert_eq!(xa, a);
        assert_eq!(ya, a);
    }

    #[test]
    fn test_32_8() {
        type V = NanoStack<NanoArrayBit<u32, u8, 8>>;
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
                   [0x55, 0x99, 0xDD, 0x33].into_iter().collect::<V>());
    }

    #[test]
    fn print_it() {
        type V = NanoStack<NanoArrayBit<u64, u16, 12>>;
        std::println!("{:?}", V::from_iter([1, 2, 3, 0xFFF, 0x800]));
    }
}
