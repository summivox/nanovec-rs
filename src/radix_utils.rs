#![allow(unused)]

/// Find max `n` s.t. `radix.pow(n) <= 2.pow(bits)`.
/// - if `radix == 2.pow(m)`:
///   - `2.pow(m).pow(n) <= 2.pow(bits)`
///   - `m * n <= bits`
///   - `n <= bits / m`
///   - `max n = floor(bits / m)`
/// - otherwise, `radix.pow(n) != 2.pow(bits)`
///   - find `n` s.t. `radix.pow(n) < 2.pow(bits) < radix.pow(n + 1)`
pub const fn get_capacity(bits: usize, radix: usize) -> usize {
    if radix.is_power_of_two() {
        let m = radix.trailing_zeros() as usize;
        return bits / m;
    }
    let limit = match bits {
        0..=127 => (1u128 << bits) - 1,
        128 => u128::MAX,
        _ => panic!("too many bits"),
    };
    let mut i = 0;
    let mut x = 1u128;
    loop {
        // TODO(summivox): rust (if-let-chain)
        (i, x) = match x.checked_mul(radix as u128) {
            Some(y) => if y < limit { (i + 1, y) } else { return i; }
            None => return i
        }
    }
}

/// This is another hack --- `min(get_capacity(bits, radix), upper_limit)`.
/// Reason: `min` is not const fn.
pub const fn get_capacity_clamped(bits: usize, radix: usize, upper_limit: usize) -> usize {
    let capacity = get_capacity(bits, radix);
    if capacity > upper_limit { upper_limit } else { capacity }
}

/// `(0..).map(|i| radix.pow(i)).take(CAPACITY)` => `[1, radix.pow(1), radix.pow(2), ...]`
pub const fn get_powers<const CAPACITY: usize>(radix: usize) -> [u128; CAPACITY] {
    let mut powers = [0u128; CAPACITY];
    let mut i = 0;
    let mut x = 1u128;
    while i < CAPACITY {
        powers[i] = x;
        (i, x) = (i + 1, x * (radix as u128));
    }
    powers
}

/// This is a hack --- allow specifying a separate powers array size.
/// Otherwise the same as [`get_powers`].
pub const fn get_powers_fixed<const LENGTH: usize>(
    capacity: usize, radix: usize
) -> [u128; LENGTH] {
    let mut powers = [0u128; LENGTH];
    let mut i = 0;
    let mut x = 1u128;
    while i < capacity {
        powers[i] = x;
        (i, x) = (i + 1, x * (radix as u128));
    }
    powers
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capacity_examples() {
        assert_eq!(get_capacity(64, 2), 64);
        assert_eq!(get_capacity(64, 4), 32);
        assert_eq!(get_capacity(64, 35), 12);
        assert_eq!(get_capacity(128, 2), 128);
        assert_eq!(get_capacity(128, 35), 24);
        assert_eq!(get_capacity(8, 3), 5);
    }

    #[test]
    fn powers_examples() {
        assert_eq!(get_powers::<5>(10), [1, 10, 100, 1000, 10000]);
        assert_eq!(get_powers_fixed::<6>(5, 10), [1, 10, 100, 1000, 10000, 0])
    }
}
