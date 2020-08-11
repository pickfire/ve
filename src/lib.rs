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
#![feature(allocator_api)]
#![feature(allow_internal_unstable)]
#![feature(const_fn)]
#![feature(const_generics)]
#![feature(core_intrinsics)]
#![feature(exact_size_is_empty)]
#![feature(dropck_eyepatch)]
#![feature(new_uninit)]
#![feature(ptr_offset_from)]
#![feature(slice_partition_dedup)]
#![feature(slice_ptr_len)]
#![feature(specialization)]
#![feature(trusted_len)]
#![feature(try_reserve)]
#![warn(missing_docs)]
#![no_std]
extern crate alloc;

// Module with internal macros used by other modules (needs to be included before other modules).
#[macro_use]
mod macros;

mod raw_vec;

#[doc(hidden)]
pub mod slice;
pub mod vec;

pub use crate::vec::Vec;
