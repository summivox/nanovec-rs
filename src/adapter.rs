//! Defines adapters of [`crate::NanoArray`]: data structures built on top of raw packed arrays.

mod deque;
mod stack;

pub use self::{
    deque::*,
    stack::*,
};
