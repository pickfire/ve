/// Replace standard library `slice` implementation to interface with `Vec`.
use alloc::borrow::Borrow;

use crate::vec::Vec;

////////////////////////////////////////////////////////////////////////////////
// Basic slice extension methods
////////////////////////////////////////////////////////////////////////////////

pub use hack::into_vec;
pub use hack::to_vec;

// Use japaric hack for `impl [T]` for `cfg(test)` which `impl [T]` is not available.
mod hack {
    use crate::vec::Vec;
    use alloc::boxed::Box;

    pub fn into_vec<T>(b: Box<[T]>) -> Vec<T> {
        let len = b.len();
        let b = Box::into_raw(b);
        unsafe { Vec::from_raw_parts(b as *mut T, len, len) }
    }

    pub fn to_vec<T>(s: &[T]) -> Vec<T>
    where
        T: Clone,
    {
        let mut vec = Vec::with_capacity(s.len());
        vec.extend_from_slice(s);
        vec
    }
}

////////////////////////////////////////////////////////////////////////////////
// Standard trait implementations for slices
////////////////////////////////////////////////////////////////////////////////

impl<T> Borrow<[T]> for Vec<T> {
    fn borrow(&self) -> &[T] {
        &self[..]
    }
}
