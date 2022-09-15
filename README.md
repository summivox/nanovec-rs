# `nanovec`: Vec-packed-in-an-Integer

Ever felt the need to store a few small integers, but `Vec` (or even [tinyvec]) takes up more space than you'd like?

`nanovec` offers both fixed- and variable-length arrays of integers with limited range, all packed within one or two
machine registers that you can effortlessly lug around.

This crate:

- is `no_std`.
- is inspired by [tinyvec], including the name.
- only depends on `num_traits` to generalize over primitive integer types.

Two space-saving strategies are offered: bit-packing and radix-packing.

## Bit-packed arrays

A wide integer (e.g. `u64`) can be treated as an array of narrower integers (e.g. 16 x 4-bit or 5 x 12-bit).
Given the packed integer type (`n` bits) and the bit-width of each element (`k` bits), the capacity can be determined as
`floor(n / k)`.

- If the length is constant or can be determined externally, [`NanoArrayBit`] is a fixed-length bit-packed array.

- If the length is variable:

  - If you can afford to also store the total number of elements (length) as a `u8` alongside with the bit-packed 
    array itself, [`NanoVecBitN`] gives you the best versatility as an index-able double-ended queue (deque).

  - Alternatively, if you are willing to reduce the range of elements by 1, [`NanoVecBitZ`] represents a stack of 
    _non-zero_ elements using the zero-termination technique (like C-strings) to encode the length without storing it.

## Radix-packed arrays

Generalizing the bit-packing approach, a base-`r` integer can be treated as an array of integers in the range `0..r`.
A good example is a decimal (base-10) number --- `12345678` can be treated as an array of `[8, 7, 6, 5, 4, 3, 2, 1]` 
(least-significant digit first).

This approach allows you to pack even more elements when the range of each element can be more precisely defined.
Especially, when `r` is only marginally larger than `2.pow(k)` but a lot smaller than `2.pow(k + 1)`, packing in
base-`r` can save a lot of space compared to (effectively) packing in base-`2.pow(k + 1)`.

The main drawback of radix-packing is more expensive computations: mul-div-mod vs. bit operations.
For this reason, the bit-packed alternatives are preferred as long as they fit.

- [`NanoArrayRadix`] is a fixed-length base-`k` array; <=> [`NanoArrayBit`].
- [`NanoVecRadixZ`] is a bound-length non-zero stack; <=> [`NanoVecBitZ`].
- (length-attached vec TBD)


[tinyvec]: https://crates.io/crates/tinyvec
