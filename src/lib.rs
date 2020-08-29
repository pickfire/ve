//! Faster, more compact implementation of `Vec`.
//!
//! ```rust
//! use std::mem::size_of;
//! use ve::Vec;
//!
//! const WORD: usize = size_of::<usize>();
//!
//! assert_eq!(size_of::<Vec<u8>>(), 2 * WORD);
//! ```
#![allow(incomplete_features)]
#![deny(unsafe_op_in_unsafe_fn)]
#![feature(allocator_api)]
#![feature(allow_internal_unstable)]
#![feature(const_fn)]
#![feature(const_generics)]
#![feature(core_intrinsics)]
#![feature(exact_size_is_empty)]
#![feature(dropck_eyepatch)]
#![feature(new_uninit)]
#![feature(slice_partition_dedup)]
#![feature(slice_ptr_len)]
#![feature(min_specialization)]
#![feature(rustc_attrs)]
#![feature(trusted_len)]
#![feature(try_reserve)]
#![feature(unsafe_block_in_unsafe_fn)]
#![warn(missing_docs)]
#![no_std]
extern crate alloc;

// Module with internal macros used by other modules (needs to be included before other modules).
#[macro_use]
mod macros;

pub mod raw_vec;
pub mod slice;
pub mod vec;

pub use crate::vec::Vec;
