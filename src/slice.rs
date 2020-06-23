/// Replace standard library `slice` implementation to interface with `Vec`.
use alloc::boxed::Box;

use crate::vec::Vec;

// Use japaric hack for `impl [T]` for `cfg(test)` which `impl [T]` is not available.
pub fn into_vec<T>(b: Box<[T]>) -> Vec<T> {
    let len = b.len();
    let b = Box::into_raw(b);
    unsafe { Vec::from_raw_parts(b as *mut T, len, len) }
}
