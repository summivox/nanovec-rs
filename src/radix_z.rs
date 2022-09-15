use core::fmt::{Debug, Formatter};

use num_traits::{PrimInt, WrappingAdd, WrappingMul, WrappingSub};

use super::NanoArrayRadix;

/// Represents a bounded stack of unsigned integers in the range `1..RADIX` (no `0`, no `RADIX`),
/// stored as a base-`RADIX` unsigned integer with 1 "digit" per element.
///
/// - `T`: a backing unsigned integer used to store the encoded number.
/// - `RADIX`: determines the range of each element.
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
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct NanoVecRadixZ<T, const RADIX: usize>(NanoArrayRadix<T, RADIX>)
    where T: PrimInt + WrappingAdd + WrappingSub + WrappingMul;

// Avoid typing this out throughout the implementation.
// Usage: `<arr!()>::LENGTH`
macro_rules! arr {
    () => { NanoArrayRadix::<T, RADIX> };
}

// TODO(summivox):
//     Most of this is duplicate from `bit_z`, since the underlying storage has really been
//     abstracted away by the corresponding "Array" type.
//     Due to language limits, this might be hard to dedupe though... We won't bother for now.
impl<T: PrimInt + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
NanoVecRadixZ<T, RADIX> {
    pub const NUM_BYTES: usize = core::mem::size_of::<T>();
    pub const NUM_BITS: usize = Self::NUM_BYTES * 8;

    pub const MIN_ELEM: usize = 1;
    pub const MAX_ELEM: usize = RADIX - 1;

    pub const CAPACITY: usize = <arr!()>::LENGTH;

    ////////////////////////////////////////////////////////////////////
    // basics

    /// Creates an empty stack.
    pub fn new() -> Self { Self(<arr!()>::new()) }

    /// Creates a stack from its base-`RADIX` integer representation.
    pub fn from_packed(packed: T) -> Self { Self(<arr!()>::from_packed(packed)) }

    /// Converts the stack to its base-`RADIX` integer representation.
    pub fn packed(self) -> T { self.0.packed() }

    /// Returns whether this stack is empty.
    pub fn is_empty(self) -> bool { self.0.get(0) == T::zero() }

    /// Returns whether this stack is full.
    pub fn is_full(self) -> bool { self.0.get(Self::CAPACITY - 1) > T::zero() }


    ////////////////////////////////////////////////////////////////////
    // push

    /// Returns a new stack = this stack with an additional element on top
    /// (a.k.a. immutable push).
    /// Panics if the element is out of range, or the stack is full.
    pub fn with(self, elem: T) -> Self {
        assert!(elem != T::zero());
        assert!(!self.is_full());
        self.with_unchecked(elem)
    }

    /// Pushes an element onto the top of this stack.
    /// Panics if the element is out of range, or the stack is full.
    pub fn push(&mut self, elem: T) {
        assert!(elem != T::zero());
        assert!(!self.is_full());
        self.push_unchecked(elem);
    }

    /// Pushes an element on to the top of this stack.
    /// If the stack is full, removes and returns the element at the bottom of the stack;
    /// otherwise returns `None`.
    /// Panics if the pushed element is out of range.
    pub fn push_circular(&mut self, elem: T) -> Option<T> {
        assert!(elem != T::zero());
        let cap_last = self.cap_bottom_unchecked();
        self.push_unchecked(elem);
        if cap_last != T::zero() { Some(cap_last) } else { None }
    }

    /// Returns a new stack = this stack with an additional element on top
    /// (immutable push).
    /// If the original stack is full, the element at the bottom of the stack will be removed in
    /// the new stack.
    pub fn with_unchecked(self, elem: T) -> Self {
        Self(self.0.shl(1).with(0, elem))
    }

    /// Pushes an element on to the top of this stack.
    /// If the stack is full, removes the element silently at the bottom of the stack.
    pub fn push_unchecked(&mut self, elem: T) {
        self.0 = self.0.shl(1).with(0, elem)
    }

    /// Returns the element at the top of the stack, or `None` if the stack is empty.
    pub fn top(self) -> Option<T> {
        let elem = self.top_unchecked();
        if elem != T::zero() { Some(elem) } else { None }
    }

    /// Returns the element at the top of the stack, or `0` if the stack is empty.
    /// Note that elements are not allowed to be `0` to begin with.
    pub fn top_unchecked(self) -> T {
        self.0.get(0)
    }

    /// Returns the element at the bottom of the stack if the stack is full; otherwise `None`.
    pub fn cap_bottom(self) -> Option<T> {
        let elem = self.cap_bottom_unchecked();
        if elem != T::zero() { Some(elem) } else { None }
    }

    /// Returns the element at the bottom of the stack if the stack is full; otherwise `0`.
    /// Note that elements are not allowed to be `0` to begin with.
    pub fn cap_bottom_unchecked(self) -> T {
        self.0.get(Self::CAPACITY - 1)
    }

    /// Returns a stack with all elements of this stack except for the one on top
    /// (a.k.a. immutable pop).
    /// When the original stack is empty, returns an empty stack.
    pub fn rest(self) -> Self {
        Self(self.0.shr(1))
    }

    /// Partitions the stack into the top element + all other elements in a stack.
    /// Returns `None` if the stack is empty.
    pub fn top_rest(self) -> Option<(T, Self)> {
        let elem = self.top_unchecked();
        if elem != T::zero() { Some((elem, self.rest())) } else { None }
    }

    /// Partitions the stack into the top element + all other elements in a stack.
    /// Returns `0` + empty stack if the original stack is empty.
    pub fn top_rest_unchecked(self) -> (T, Self) {
        (self.top_unchecked(), self.rest())
    }

    /// Returns the `i`-th element from the top of the stack; `None` if the element does not exist.
    /// e.g. `get(0)` returns the top, `get(1)` returns the one just below it, etc.
    pub fn get(self, i: usize) -> Option<T> {
        let elem = self.get_unchecked(i);
        if elem != T::zero() { Some(elem) } else { None }
    }

    /// Returns the `i`-th element from the top of the stack; `0` if the element does not exist.
    /// e.g. `get(0)` returns the top, `get(1)` returns the one just below it, etc.
    /// Note that elements are not allowed to be `0` to begin with.
    pub fn get_unchecked(self, i: usize) -> T {
        self.0.get(i)
    }

    /// Removes the element on top and returns it; `None` if the stack is empty.
    pub fn pop(&mut self) -> Option<T> {
        let (elem, rest) = self.top_rest_unchecked();
        self.0 = rest.0;
        if elem != T::zero() { Some(elem) } else { None }
    }
}

impl<T: PrimInt + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
Default for NanoVecRadixZ<T, RADIX> {
    fn default() -> Self { Self::new() }
}

impl<T: PrimInt + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
From<T> for NanoVecRadixZ<T, RADIX> {
    fn from(packed: T) -> Self {
        Self::from_packed(packed)
    }
}

impl<T: PrimInt + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
From<arr!()> for NanoVecRadixZ<T, RADIX> {
    fn from(a: arr!()) -> Self { Self(a) }
}

impl<T: PrimInt + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
FromIterator<T> for NanoVecRadixZ<T, RADIX> {
    fn from_iter<It: IntoIterator<Item=T>>(iter: It) -> Self {
        let mut v = Self::new();
        for elem in iter {
            v.push(elem);
        }
        v
    }
}

impl<'a, T: PrimInt + WrappingAdd + WrappingSub + WrappingMul + 'a, const RADIX: usize>
FromIterator<&'a T> for NanoVecRadixZ<T, RADIX> {
    fn from_iter<It: IntoIterator<Item=&'a T>>(iter: It) -> Self {
        let mut v = Self::new();
        for elem in iter {
            v.push(*elem);
        }
        v
    }
}

impl<T: PrimInt + WrappingAdd + WrappingSub + WrappingMul, const RADIX: usize>
Iterator for NanoVecRadixZ<T, RADIX> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> { self.pop() }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(Self::CAPACITY))
    }
}

impl<T: PrimInt + WrappingAdd + WrappingSub + WrappingMul + Debug, const RADIX: usize>
Debug for NanoVecRadixZ<T, RADIX> {
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
    fn test_radix_100() {
        type V = NanoVecRadixZ<u32, 100>;

        let a = V::new();
        assert_eq!(a.0, 0.into());
        let b = a.with(1);
        assert_eq!(b.0, 1.into());
        let c = b.with(2);
        assert_eq!(c.0, 102.into());
        let d = c.with(99);
        assert_eq!(d.0, 10299.into());
        let e = d.with(98);
        assert_eq!(e.0, 1029998.into());

        assert_eq!(a.top_rest(), None);
        assert_eq!(b.top_rest(), Some((1, a)));
        assert_eq!(c.top_rest(), Some((2, b)));
        assert_eq!(d.top_rest(), Some((99, c)));
        assert_eq!(e.top_rest(), Some((98, d)));

        let mut aa = a;
        aa.push(1);
        assert_eq!(aa, b);
        aa.push(2);
        assert_eq!(aa, c);
        aa.push(99);
        assert_eq!(aa, d);
        aa.push(98);
        assert_eq!(aa, e);

        let mut ee = e;
        assert_eq!(ee.pop(), Some(98));
        assert_eq!(ee.pop(), Some(99));
        assert_eq!(ee.pop(), Some(2));
        assert_eq!(ee.pop(), Some(1));
        assert_eq!(ee.pop(), None);

        assert_eq!(e.collect::<Vec<_>>(),
                   vec![98, 99, 2, 1]);
    }

    #[test]
    #[should_panic]
    fn test_radix_100_overflow() {
        type V = NanoVecRadixZ<u32, 100>;
        let a = V::new().with(50).with(51).with(52).with(53);
        assert_eq!(a.0, 50515253.into());
        let _ = a.with(1);  // should fail
    }

    #[test]
    fn print_it() {
        extern crate std;
        type V = NanoVecRadixZ<u32, 100>;
        let a = V::new().with(50).with(51).with(52).with(53);
        std::println!("{:?}", a);
    }
}
