#![doc = include_str!("../README.md")]
#![no_std]
#![forbid(unsafe_code)]

pub mod array;
pub mod adapter;
mod radix_utils;

pub use self::{
    array::*,
    adapter::*,
};

/// Double-ended queue (deque), bit-packed.
///
/// - Element range: `0..(1 << NUM_ELEM_BITS)`.
/// - Capacity: `floor(n / NUM_ELEM_BITS)` (see below).
///
/// Generic parameters:
///
/// - `TContainer`: `n`-bit unsigned integer.
/// - `TElem`: `m`-bit unsigned integer.
/// - `NUM_ELEM_BITS`: bit-width of the element.
///
/// Must satisfy: `n >= m >= NUM_ELEM_BITS`.
///
/// See [`NanoDeque`] for supported operations, [`NanoArrayBit`] for packing strategy.
pub type NanoDequeBit<TContainer, TElem, const NUM_ELEM_BITS: usize> =
NanoDeque<NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS>>;

/// Zero-terminated stack, bit-packed.
///
/// - Element range: `1..(1 << NUM_ELEM_BITS)`.
/// - Capacity: `floor(n / NUM_ELEM_BITS)` (see below).
///
/// Generic parameters:
///
/// - `TContainer`: `n`-bit unsigned integer
/// - `TElem`: `m`-bit unsigned integer
/// - `NUM_ELEM_BITS == k`
///
/// Must satisfy: `n >= m >= k`.
///
/// See [`NanoStack`] for supported operations, [`NanoArrayBit`] for packing strategy.
pub type NanoStackBit<TContainer, TElem, const NUM_ELEM_BITS: usize> =
NanoStack<NanoArrayBit<TContainer, TElem, NUM_ELEM_BITS>>;

/// Double-ended queue (deque), base-`RADIX`-packed.
///
/// - Element range: `0..RADIX`.
/// - Capacity: `argmax(m) RADIX.pow(m) <= 2.pow(n)`; `floor(n / log2(r))` (see below).
///
/// Generic parameters:
///
/// - `T`: `n`-bit unsigned integer
/// - `RADIX`: range of the element (exclusive)
///
/// See [`NanoDeque`] for supported operations, [`NanoArrayRadix`] for packing strategy.
pub type NanoDequeRadix<T, const RADIX: usize> = NanoDeque<NanoArrayRadix<T, RADIX>>;

/// Zero-terminated stack, base-`RADIX`-packed.
///
/// - Element range: `1..RADIX`.
/// - Capacity: `argmax(m) RADIX.pow(m) <= 2.pow(n)`; `floor(n / log2(r))` (see below).
///
/// Generic parameters:
///
/// - `T`: `n`-bit unsigned integer
/// - `RADIX`: range of the element (exclusive)
///
/// See [`NanoStack`] for supported operations, [`NanoArrayRadix`] for packing strategy.
pub type NanoStackRadix<T, const RADIX: usize> = NanoStack<NanoArrayRadix<T, RADIX>>;
