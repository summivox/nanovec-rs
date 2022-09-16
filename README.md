# `nanovec`: Arrays and friends, packed in an integer or two.

[![Crates.io](https://img.shields.io/crates/v/nanovec)](https://crates.io/crates/nanovec)
[![docs.rs](https://img.shields.io/docsrs/nanovec)](https://docs.rs/nanovec)

Ever felt the need to store a few small integers, but a `Vec` (or even [tinyvec]) takes up more space than you'd like?

`nanovec` offers both fixed- and variable-length arrays of integers with limited range, all packed within one or two
machine words that you can effortlessly lug around.

This crate:

- is `no_std`.
- is inspired by [tinyvec], including the name.
- has minimum dependencies.

[tinyvec]: https://crates.io/crates/tinyvec

## Cheatsheet of types offered

| [`NanoArray`] (trait)     | [`NanoDeque`] (adapter)    | [`NanoStack`] (adapter)    |
|---------------------------|----------------------------|----------------------------|
| [`NanoArrayBit`] (impl)   | [`NanoDequeBit`] (alias)   | [`NanoStackBit`] (alias)   |
| [`NanoArrayRadix`] (impl) | [`NanoDequeRadix`] (alias) | [`NanoStackRadix`] (alias) |

## Packed Arrays

Two space-saving strategies are offered: bit-packing and radix-packing.
Both support the same set of operations defined as trait [`NanoArray`].

A wide unsigned integer (e.g. `u64`) can be treated as an array of narrower integers (e.g. 16 x 4-bit or 5 x 12-bit).
Given the packed integer type (`n` bits) and the bit-width of each element (`k` bits), the capacity can be determined as
`floor(n / k)`. This is implemented as [`NanoArrayBit`].

Generalizing the bit-packing approach, a base-`r` integer can be treated as an array of integers in the range `0..r`.
A good example is a decimal (base-10) number --- `12345678` can be treated as an array of `[8, 7, 6, 5, 4, 3, 2, 1]`
(least-significant digit first). This is implemented as [`NanoArrayRadix`].

Bit-packing is expected to perform better than radix-packing, as bit operations are cheaper than mul-div-mod.
**Therefore, bit-packing is the preferred approach**, unless you need to squeeze in more elements when the element
range is inconvenient for bit-packing (i.e. when `r` is only marginally larger than a power of two, but much smaller
than the next power of two).

## Adapters

Building upon the fixed-length packed arrays, the following variable-length data structures are offered:

- [`NanoDeque`] implements a double-ended queue as [`NanoArray`] + length. This is the most versatile as it supports
  pushing/popping at both ends, and get/set at any index. The only drawback is the extra space and padding needed
  for storing the length.

- [`NanoStack`] implements a zero-terminated stack backed by [`NanoArray`] alone, but its elements must be non-zero
  (think C-style strings with `'\0'` at the end). This supports pushing/popping at only one end, and get at any index.

