//! A contiguous growable array type with heap-allocated contents, written `Vec<T>`.
//!
//! Vectors have `O(1)` indexing, amortized `O(1)` push (to the end) and `O(1)` pop (from the end).
//!
//! Vectors ensure they never alloctae more than `isize::MAX` bytes.
//!
//! # Examples
//!
//! You can explicitly create a [`Vec<T>`] with [`new`]:
//!
//! ```
//! use ve::Vec;
//!
//! let v: Vec<i32> = Vec::new();
//! ```
//!
//! ...or by using the [`vec!`] macro:
//!
//! ```
//! use ve::{Vec, vec};
//!
//! let v: Vec<i32> = vec![];
//!
//! let v = vec![1, 2, 3, 4, 5];
//!
//! let v = vec![0; 10]; // ten zeros
//! ```
//!
//! You can [`push`] values onto the end of a vector (which will grow the vector as needed):
//!
//! ```
//! # use ve::vec;
//! let mut v = vec![1, 2];
//!
//! v.push(3);
//! ```
//!
//! Popping values works in much the same way:
//!
//! ```
//! # use ve::vec;
//! let mut v = vec![1, 2];
//!
//! let two = v.pop();
//! ```
//!
//! Vectors also support indexing (through the [`Index`] and [`IndexMut`] traits):
//!
//! ```
//! # use ve::vec;
//! let mut v = vec![1, 2, 3];
//! let three = v[2];
//! v[1] = v[1] + 5;
//! ```
//!
//! [`Vec<T>`]: Vec
//! [`new`]: Vec::new
//! [`push`]: Vec::push

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::intrinsics::{arith_offset, assume};
use core::iter::{FromIterator, FusedIterator, TrustedLen};
use core::marker::PhantomData;
use core::mem::{self, ManuallyDrop};
use core::ops::Bound::{Excluded, Included, Unbounded};
use core::ops::{self, Index, IndexMut, RangeBounds};
use core::ptr::{self, NonNull};
use core::slice::{self, SliceIndex};

use alloc::borrow::{Cow, ToOwned};
use alloc::boxed::Box;

use crate::raw_vec::{RawVec, MASK_HI, MASK_LO};

/// A continuous growable array type, written `Vec<T>` but pronounced 'vector'.
///
/// # Examples
///
/// ```
/// # use ve::Vec;
/// let mut vec = Vec::new();
/// vec.push(1);
/// vec.push(2);
///
/// assert_eq!(vec.len(), 2);
/// assert_eq!(vec[0], 1);
///
/// assert_eq!(vec.pop(), Some(2));
/// assert_eq!(vec.len(), 1);
///
/// vec[0] = 7;
/// assert_eq!(vec[0], 7);
///
/// vec.extend([1, 2, 3].iter().copied());
///
/// for x in &vec {
///     println!("{}", x);
/// }
/// assert_eq!(vec, [7, 1, 2, 3]);
/// ```
///
/// The [`vec!`] macro is provided to make initialization more convenient:
///
/// ```
/// # use ve::vec;
/// let mut vec = vec![1, 2, 3];
/// vec.push(4);
/// assert_eq!(vec, [1, 2, 3, 4]);
/// ```
///
/// It can also initialize each element of a `Vec<T>` with a given value.
/// This may be more efficient than performing allocation and initialization in separate steps,
/// especially when initializing a vector of zeros:
///
/// ```
/// # use ve::vec;
/// let vec = vec![0; 5];
/// assert_eq!(vec, [0, 0, 0, 0, 0]);
///
/// // The follwing is equavalent, but potentially slower:
/// let mut vec1 = Vec::with_capacity(5);
/// vec1.resize(5, 0);
/// ```
///
/// Use a `Vec<T>` as an efficient stack:
///
/// ```
/// # use ve::Vec;
/// let mut stack = Vec::new();
///
/// stack.push(1);
/// stack.push(2);
/// stack.push(3);
///
/// while let Some(top) = stack.pop() {
///     // Prints 3, 2, 1
///     println!("{}", top);
/// }
/// ```
///
/// # Indexing
///
/// The `Vec` type allows to access values by index, because it implements [`Index`] trait.
/// An example will be more explicit:
///
/// ```
/// # use ve::vec;
/// let v = vec![0, 2, 4, 6];
/// println!("{}", v[1]); // it will display '2'
/// ```
///
/// However be careful: if you try to access an index which isn't in the `Vec`,
/// your software will panic! You cannot do this:
///
/// ```should_panic
/// # use ve::vec;
/// let v = vec![0, 2, 4, 6];
/// println!("{}", v[6]); // it will panic!
/// ```
///
/// Use [`get`] and [`get_mut`] if you want to check whether the index is in the `Vec`.
///
/// # Slicing
///
/// A `Vec` can be mutable. Slices, on the other hand, are read-only objects.
/// To get a slice, use `&`. Example:
///
/// ```
/// # use ve::vec;
/// fn read_slice(slice: &[usize]) {
///     // ...
/// }
///
/// let v = vec![0, 1];
/// read_slice(&v);
///
/// // ... and that's all!
/// // you can also do it like this:
/// let u: &[usize] = &v;
/// ```
///
/// In Rust, it's more common to pass slices as arguments rather than vectors when you just want to
/// provide read access. The same goes for [`String`] and [`&str`].
///
/// # Capacity and reallocation
///
/// The capacity of a vector is the amount of space allocated for any future elements that will be
/// added onto the vector. This is not to be confused with the *length* of a vector, which
/// specifies the number of actual elements within the vector. If a vector's length exceeds its
/// capacity, its capacity will automatically be increased but its elements will have to be
/// reallocated.
///
/// For example, a vector with capacity 10 and length 0 would be an empty vector with space for 10
/// more elements. Pushing 10 or fewer elements onto the vector will not change its capacity or
/// cause reallocation to occur. However, if the vector's length is increased to 11, it will have
/// to reallocate, which can be slow. For this reason, it is recommended to use
/// [`Vec::with_capacity`] whenever possible to specify how big the vector is expected to get.
///
/// # Guarantees
///
/// TODO Guarantees
pub struct Vec<T> {
    buf: RawVec<T>,
}

impl<T> Vec<T> {
    /// Constructs a new empty, `Vec<T>`.
    ///
    /// The vector will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::Vec;
    /// let mut vec: Vec<i32> = Vec::new();
    /// ```
    #[inline]
    pub const fn new() -> Vec<T> {
        Vec { buf: RawVec::new() }
    }

    /// Constructs a new, empty `Vec<T>` with the specified capacity.
    ///
    /// The vector will be able to hold exactly `capacity` elements without reallocating. If
    /// `capacity` is 0, the vector will not allocate.
    ///
    /// It is important to note that although the returned vector has the *capacity* specified, the
    /// vector will have a zero *length*. For an explanation of the difference between length and
    /// capacity, see *[Capacity and reallocation]*.
    ///
    /// [Capacity and reallocation]: #capacity-and-reallocation
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::Vec;
    /// let mut vec = Vec::with_capacity(10);
    ///
    /// // The vector contains no items, even though it has capacity for more
    /// assert_eq!(vec.len(), 0);
    /// assert_eq!(vec.capacity(), 10);
    ///
    /// // These are all done without reallocating...
    /// for i in 0..10 {
    ///     vec.push(i);
    /// }
    /// assert_eq!(vec.len(), 10);
    /// assert_eq!(vec.capacity(), 10);
    ///
    /// // ...but this may make the vector reallocate
    /// vec.push(11);
    /// assert_eq!(vec.len(), 11);
    /// assert!(vec.capacity() >= 11);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Vec<T> {
        Vec {
            buf: RawVec::with_capacity(capacity),
        }
    }

    /// Creates a `Vec<T>` directly from the raw components of another vector.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't checked:
    ///
    /// * `ptr` needs to have been previously allocated via [`String`]/`Vec<T>` (at least, it's
    ///   highly likely to be incorrect if it wasn't).
    /// * `T` needs to have the same size and alignment as what `ptr` was allocated with. (`T`
    ///   having a less strict alignment is not sufficient, the alignment really needs to be equal
    ///   to satisfy the [`dealloc`] requirement that memory must be allocated and deallocated with
    ///   the same layout.)
    /// * `length` needs to be less than or equal to `capacity`.
    /// * `capacity` needs to be the capacity that the pointer was allocated with.
    ///
    /// Violating these may cause problems like corrupting the allocator's internal data
    /// structures.  For example it is **not** safe to build a `Vec<u8>` from a pointer to a C
    /// `char` array with length `size_t`. It's also not safe to build one from a `Vec<u16>` and
    /// its length, because the allocator cares about the alignment, and these two types have
    /// different alignments. The buffer was allocated with alignment 2 (for `u16`), but after
    /// turning it into a `Vec<u8>` it'll be deallocated with alignment 1.
    ///
    /// The ownership of `ptr` is effectively transferred to the `Vec<T>` which may then
    /// deallocate, reallocate or change the contents of memory pointed to by the pointer at will.
    /// Ensure that nothing else uses the pointer after calling this function.
    ///
    /// [`String`]: https://doc.rust-lang.org/stable/std/string/struct.String.html
    /// [`dealloc`]: https://doc.rust-lang.org/stable/std/alloc/trait.GlobalAlloc.html#tymethod.dealloc
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// use std::ptr;
    /// use std::mem;
    ///
    /// let v = vec![1, 2, 3];
    ///
    // FIXME Update this when vec_into_raw_parts is stabilized
    /// // Prevent running `v`'s destructor so we are in complete control
    /// // of the allocation.
    /// let mut v = mem::ManuallyDrop::new(v);
    ///
    /// // Pull out the various important pieces of information about `v`
    /// let p = v.as_mut_ptr();
    /// let len = v.len();
    /// let cap = v.capacity();
    ///
    /// unsafe {
    ///     // Overwrite memory with 4, 5, 6
    ///     for i in 0..len as isize {
    ///         ptr::write(p.offset(i), 4 + i);
    ///     }
    ///
    ///     // Put everything back together into a Vec
    ///     let rebuilt = Vec::from_raw_parts(p, len, cap);
    ///     assert_eq!(rebuilt, [4, 5, 6]);
    /// }
    /// ```
    pub unsafe fn from_raw_parts(ptr: *mut T, length: usize, capacity: usize) -> Vec<T> {
        Vec {
            buf: RawVec::from_raw_parts(ptr, capacity, length),
        }
    }

    /// Returns the number of elements the vector can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::Vec;
    /// let vec: Vec<i32> = Vec::with_capacity(10);
    /// assert_eq!(vec.capacity(), 10);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the given
    /// `Vec<T>`. The collection may reserve more space to avoid frequent reallocations. After
    /// calling `reserve`, capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec![1];
    /// vec.reserve(10);
    /// assert!(vec.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.buf.reserve(self.buf.len(), additional);
    }

    /// Reserves the minimum capacity for exactly `additional` more elements to be inserted in the
    /// given `Vec<T>`. After calling `reserve_exact`, capacity will be greater than or equal to
    /// `self.len() + additional`. Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests. Therefore,
    /// capacity can not be relied upon to be precisely minimal. Prefer `reverse` if future
    /// insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec![1];
    /// vec.reserve_exact(10);
    /// assert!(vec.capacity() >= 11);
    /// ```
    pub fn reserve_exact(&mut self, additional: usize) {
        self.buf.reserve_exact(self.len(), additional);
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator may still inform the
    /// vector that there is space for a few more elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = Vec::with_capacity(10);
    /// vec.extend([1, 2, 3].iter().cloned());
    /// assert_eq!(vec.capacity(), 10);
    /// vec.shrink_to_fit();
    /// assert!(vec.capacity() >= 3);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        // The capacity is never less than the length, and there's nothing to do when they are
        // equal, so we can avoid the panic case in `RawVec::shrink_to_fit` by only calling it
        // with a greater capacity.
        if self.capacity() > self.len() {
            self.buf.shrink_to_fit(self.len());
        }
    }

    /// Converts the vector into [`Box<[T]>`][owned slice].
    ///
    /// Note that this will drop any excess capacity.
    ///
    /// [owned slice]: Box
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let v = vec![1, 2, 3];
    ///
    /// let slice = v.into_boxed_slice();
    /// ```
    ///
    /// Any excess capacity is removed:
    ///
    /// ```
    /// # use ve::Vec;
    /// let mut vec = Vec::with_capacity(10);
    /// vec.extend([1, 2, 3].iter().cloned());
    ///
    /// assert_eq!(vec.capacity(), 10);
    /// let slice = vec.into_boxed_slice();
    /// assert_eq!(slice.into_vec().capacity(), 3);
    /// ```
    pub fn into_boxed_slice(mut self) -> Box<[T]> {
        self.shrink_to_fit();
        let me = ManuallyDrop::new(self);
        unsafe {
            let buf = ptr::read(&me.buf);
            let len = me.len();
            buf.into_box(len).assume_init()
        }
    }

    /// Shortens the vector, keeping the first `len` elements and dropping the rest.
    ///
    /// If `len` is greater than the vector's current length, this has no effect.
    ///
    /// The [`drain`] method can emulate `truncate`, but causes the excess elements to be returned
    /// instead of dropped.
    ///
    /// Note that this method has no effect on the allocated capacity of the vector.
    ///
    /// # Examples
    ///
    /// Truncating a five element vector to two elements:
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec![1, 2, 3, 4, 5];
    /// vec.truncate(2);
    /// assert_eq!(vec, [1, 2]);
    /// ```
    ///
    /// No truncation occurs when `len` is greater than the vector's current length:
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec![1, 2, 3];
    /// vec.truncate(8);
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    ///
    /// Truncating when `len == 0` is equivalent to calling the [`clear`] method.
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec![1, 2, 3];
    /// vec.truncate(0);
    /// assert_eq!(vec, []);
    /// ```
    ///
    /// [`clear`]: Vec::clear
    /// [`drain`]: Vec::drain
    pub fn truncate(&mut self, len: usize) {
        // This is safe because:
        //
        // * the slice passed to `drop_in_place` is valid; the `len > self.len` case avoids
        //   creating an invalid slice, and
        // * the `len` of the vector is shrunk before calling `drop_in_place`, such that no value
        //   will be dropped twice in case `drop_in_place` were to panic once (if it panics twice,
        //   the program aborts).
        unsafe {
            if len > self.len() {
                return;
            }
            let remaining_len = self.len() - len;
            let s = ptr::slice_from_raw_parts_mut(self.as_mut_ptr().add(len), remaining_len);
            self.buf.set_len(len);
            ptr::drop_in_place(s);
        }
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// Equivalent to `&s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// use std::io::{self, Write};
    /// let buffer = vec![1, 2, 3, 4, 5];
    /// io::sink().write(buffer.as_slice()).unwrap();
    /// ```
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self
    }

    /// Extracts a mutable slice containing the entire vector.
    ///
    /// Equivalent to `&mut s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// use std::io::{self, Read};
    /// let mut buffer = vec![0; 3];
    /// io::repeat(0b101).read_exact(buffer.as_mut_slice()).unwrap();
    /// ```
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self
    }

    /// Returns a raw pointer to the vector's buffer.
    ///
    /// The caller must ensure that the vector outlives the ponitre this function requires, or else
    /// it will end up pointing to garbage. Modifying the vector may cause its buffer to be
    /// reallocated, which would also make any pointers to it invalid.
    ///
    /// The caller must also ensure that the memory (non-transitively) points to is never written
    /// to (except inside an `UnsafeCell`) using this pointer or any pointer derived from it. If
    /// you need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let x = vec![1, 2, 4];
    /// let x_ptr = x.as_ptr();
    ///
    /// unsafe {
    ///     for i in 0..x.len() {
    ///         assert_eq!(*x_ptr.add(i), 1 << i);
    ///     }
    /// }
    /// ```
    ///
    /// [`as_mut_ptr`]: Vec::as_mut_ptr
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        // We shadow the slice method of thesame name to avoid going through `deref`, which creates
        // an immediate reference.
        let ptr = self.buf.ptr();
        unsafe {
            assume(!ptr.is_null());
        }
        ptr
    }

    /// Returns an unsafe mutable pointer to the vector's buffer.
    ///
    /// The caller must ensure that the vector outlives the pointer this function returns, or else
    /// it will end up pointing to garbage. Modifying the vector may cause its buffer to be
    /// reallocated, which would also make any pointers to it invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::Vec;
    /// // Allocate vector big enough for 4 elements.
    /// let size = 4;
    /// let mut x: Vec<i32> = Vec::with_capacity(size);
    /// let x_ptr = x.as_mut_ptr();
    ///
    /// // Initialize elements via raw pointer writes, then set length.
    /// unsafe {
    ///     for i in 0..size {
    ///         *x_ptr.add(i) = i as i32;
    ///     }
    ///     x.set_len(size);
    /// }
    /// assert_eq!(&*x, &[0,1,2,3]);
    /// ```
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        // We shadow the slice method of the same name to avoid going around `deref_mut`, which
        // creates an intermediate referenc.
        let ptr = self.buf.ptr();
        unsafe {
            assume(!ptr.is_null());
        }
        ptr
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// THis is a low-level operation that maintains none of the normal invariants of the types.
    /// Normally changing the length of a vector is done using one of the safe operations instead,
    /// such as [`truncate`], [`resize`], [`extend`], or [`clear`].
    ///
    /// [`truncate`]: Vec::truncate
    /// [`resize`]: Vec::resize
    /// [`extend`]: Extend::extend
    /// [`clear`]: Vec::clear
    ///
    /// # Safety
    ///
    /// - `new_len` must be less than or equal to [`capacity()`].
    /// - The elements at `old_len..new_len` must be initialized.
    ///
    /// [`capacity()`]: Vec::capacity
    ///
    /// # Examples
    ///
    /// This method can be useful for situations in which the vector is serving as a buffer for
    /// other code, particularly over FFI:
    ///
    /// ```no_run
    /// # #![allow(dead_code)]
    /// # use ve::Vec;
    /// # // This is just a minimal skeleton for the doc sample;
    /// # // don't use this as a starting point for a real library.
    /// # pub struct StreamWrapper { strm: *mut std::ffi::c_void }
    /// # const Z_OK: i32 = 0;
    /// # extern "C" {
    /// #     fn deflateGetDictionary(
    /// #         strm: *mut std::ffi::c_void,
    /// #         dictionary: *mut u8,
    /// #         dictLength: *mut usize,
    /// #     ) -> i32;
    /// # }
    /// # impl StreamWrapper {
    /// pub fn get_dictionary(&self) -> Option<Vec<u8>> {
    ///     // Per the FFI method's docs, "32768 bytes is always enough".
    ///     let mut dict = Vec::with_capacity(32_768);
    ///     let mut dict_length = 0;
    ///     // SAFETY: When `deflateGetDictionary` returns `Z_OK`, it holds that:
    ///     // 1. `dict_length` elements were initialized.
    ///     // 2. `dict_length` <= the capacity (32_768)
    ///     unsafe {
    ///         // Make the FFI call...
    ///         let r = deflateGetDictionary(self.strm, dict.as_mut_ptr(), &mut dict_length);
    ///         if r == Z_OK {
    ///             // ...and update the length to what was initialized
    ///             dict.set_len(dict_length);
    ///             Some(dict)
    ///         } else {
    ///             None
    ///         }
    ///     }
    /// }
    /// # }
    /// ```
    ///
    /// While the following example is sound, there is a memory leak since the inner vectors were
    /// not freed prior to the `set_len` call:
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec![vec![1, 0, 0],
    ///                    vec![0, 1, 0],
    ///                    vec![0, 0, 1]];
    /// // SAFETY:
    /// // 1. `old_len..0` is empty so no elements need to be initialized.
    /// // 2. `0 <= capacity` always holds whatever `capacity` is.
    /// unsafe {
    ///     vec.set_len(0);
    /// }
    /// ```
    ///
    /// Normally, here, one would use [`clear`] instead to correctly drop the contents and thus
    /// not leak memory.
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());

        self.buf.set_len(new_len);
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut v = vec!["foo", "bar", "baz", "qux"];
    ///
    /// assert_eq!(v.swap_remove(1), "bar");
    /// assert_eq!(v, ["foo", "qux", "baz"]);
    ///
    /// assert_eq!(v.swap_remove(0), "foo");
    /// assert_eq!(v, ["baz", "qux"]);
    /// ```
    #[inline]
    pub fn swap_remove(&mut self, index: usize) -> T {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!(
                "swap_remove index (is {}) should be < len (is {})",
                index, len
            );
        }

        let len = self.len();
        if index >= len {
            assert_failed(index, len);
        }
        unsafe {
            // We replace self[index] with the last element. Note that if the bounds check above
            // succeeds there must be a last element (which can be self[index] itself).
            let last = ptr::read(self.as_ptr().add(len - 1));
            let hole = self.as_mut_ptr().add(index);
            self.set_len(len - 1);
            ptr::replace(hole, last)
        }
    }

    /// Inserts an element at position `index` within the vector, shifting all elements after it to
    /// the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec![1, 2, 3];
    /// vec.insert(1, 4);
    /// assert_eq!(vec, [1, 4, 2, 3]);
    /// vec.insert(4, 5);
    /// assert_eq!(vec, [1, 4, 2, 3, 5]);
    /// ```
    pub fn insert(&mut self, index: usize, element: T) {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!(
                "insertion index (is {}) should be <= len (is {})",
                index, len
            );
        }

        let len = self.len();
        if index > len {
            assert_failed(index, len);
        }

        // space for the new element
        if len == self.buf.capacity() {
            self.reserve(1);
        }

        unsafe {
            // infallible
            // The spot to put the new value
            {
                let p = self.as_mut_ptr().add(index);
                // Shift everything over to make space. (Duplicating the `index`th element into two
                // consecutive places.)
                ptr::copy(p, p.offset(1), len - index);
                // Write it in, overwriting the first copy of the `index`th element.
                ptr::write(p, element);
            }
            self.set_len(len + 1);
        }
    }

    /// Removes all but the first of consecutive elements in the vector satisfying a given equality
    /// relation.
    ///
    /// The `same_bucket` function is passed references to two elements from the vector and must
    /// determine if the elements compare equal. The elements are passed in opposite order from
    /// their order in the slice, so if `same_bucket(a, b)` returns `true`, `a` is removed.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec!["foo", "bar", "Bar", "baz", "bar"];
    ///
    /// vec.dedup_by(|a, b| a.eq_ignore_ascii_case(b));
    ///
    /// assert_eq!(vec, ["foo", "bar", "baz", "bar"]);
    /// ```
    pub fn dedup_by<F>(&mut self, same_bucket: F)
    where
        F: FnMut(&mut T, &mut T) -> bool,
    {
        let len = {
            let (dedup, _) = self.as_mut_slice().partition_dedup_by(same_bucket);
            dedup.len()
        };
        self.truncate(len);
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Panics
    ///
    /// * Panics if the requested capacity exceeds `usize::MAX` bytes.
    /// * Panics on 32-bit platforms if the requested capacity exceeds
    ///   `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec![1, 2];
    /// vec.push(3);
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    #[inline]
    pub fn push(&mut self, value: T) {
        // This will panic or abort if we would allocate > isize::MAX bytes or if the length
        // increment would overflow for zero-sized types.
        if self.len() == self.buf.capacity() {
            self.reserve(1);
        }
        unsafe {
            let end = self.as_mut_ptr().add(self.len());
            ptr::write(end, value);
            self.set_len(self.len() + 1);
        }
    }

    /// Removes the last element from a vector and returns it, or [`None`] if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec![1, 2, 3];
    /// assert_eq!(vec.pop(), Some(3));
    /// assert_eq!(vec, [1, 2]);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.len() == 0 {
            None
        } else {
            unsafe {
                self.set_len(self.len() - 1);
                Some(ptr::read(self.as_ptr().add(self.len())))
            }
        }
    }

    /// Moves all the elements of `other` into `Self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the vector overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3];
    /// let mut vec2 = vec![4, 5, 6];
    /// vec.append(&mut vec2);;
    /// assert_eq!(vec, [1, 2, 3, 4, 5, 6]);
    /// assert_eq!(vec2, []);
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        unsafe {
            self.append_elements(other.as_slice() as _);
            other.set_len(0);
        }
    }

    /// Appends elements to `Self` from other buffer.
    #[inline]
    unsafe fn append_elements(&mut self, other: *const [T]) {
        let count = unsafe { (*other).len() };
        self.reserve(count);
        let len = self.len();
        unsafe { ptr::copy_nonoverlapping(other as *const T, self.as_mut_ptr().add(len), count) };
        self.set_len(len + count);
    }

    /// Creates a draining iterator that removes the specified range in the vector and yields the
    /// removed items.
    ///
    /// When the iterator **is** dropped, all elements in the range are removed from the vector,
    /// even if the iterator was not fully consumed. If the iterator **is not** dropped (with
    /// [`mem::forget`] for example), it is unspecified how many elements are removed.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the ending point or if the ending point is
    /// greater than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut v = vec![1, 2, 3];
    /// let u: Vec<_> = v.drain(1..).collect();
    /// assert_eq!(v, &[1]);
    /// assert_eq!(u, &[2, 3]);
    ///
    /// // A full range clears the vector
    /// v.drain(..);
    /// assert_eq!(v, &[]);
    /// ```
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T>
    where
        R: RangeBounds<usize>,
    {
        // Memory safety
        //
        // When the Drain is first created, it shortens the length of the source vector to make
        // sure no uninitialized or moved-from elements are accessible at all if the Drain's
        // destructor never gets to run.
        //
        // Drain will ptr::read out the values to remove.
        // When finished, remaining tail of the vec is copied back to cover the hole, and the
        // vector length is restored to the new depth.
        let len = self.len();
        let start = match range.start_bound() {
            Included(&n) => n,
            Excluded(&n) => n + 1,
            Unbounded => 0,
        };
        let end = match range.end_bound() {
            Included(&n) => n + 1,
            Excluded(&n) => n,
            Unbounded => len,
        };

        #[cold]
        #[inline(never)]
        fn start_assert_failed(start: usize, end: usize) -> ! {
            panic!(
                "start drain index (is {}) should be <= end drain index (is {})",
                start, end
            );
        }

        #[cold]
        #[inline(never)]
        fn end_assert_failed(end: usize, len: usize) -> ! {
            panic!("end drain index (is {}) should be <= len (is {})", end, len);
        }

        if start > end {
            start_assert_failed(start, end);
        }
        if end > len {
            end_assert_failed(end, len);
        }

        unsafe {
            // set self.vec length's to start, to be safe in case Drain is leaked
            self.set_len(start);
            // Use the borrow in the IterMut to indicate borrowing behavior of the whole Drain
            // iterator (like &mut T).
            let range_slice = slice::from_raw_parts_mut(self.as_mut_ptr().add(start), end - start);
            Drain {
                tail_start: end,
                tail_len: len - end,
                iter: range_slice.iter(),
                vec: NonNull::from(self),
            }
        }
    }

    /// Clears the vector, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut v = vec![1, 2, 3];
    ///
    /// v.clear();
    ///
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Returns the number of elements in the vector, also referred to as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// let a = vec![1, 2, 3];
    /// assert_eq!(a.len(), 3);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.buf.len()
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::Vec;
    /// let mut v = Vec::new();
    /// assert!(v.is_empty());
    ///
    /// v.push(1);
    /// assert!(!v.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    // TODO split_off

    /// Resizes the `Vec` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the `Vec` is extended by the difference, with each
    /// additional slot filled with the result of calling the closure `f`. The return values from
    /// `f` will end up in the `Vec` in the order they have been generated.
    ///
    /// If `new_len` is less than `len`, the `Vec` is simply truncated.
    ///
    /// This method uses a closure to create new values on every push. If you'd rather [`Clone`] a
    /// given value, use [`Vec::resize`]. If you want to use the [`Default`] trait to generate
    /// values, you can pass [`Default::default`] as the second argument.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec![1, 2, 3];
    /// vec.resize_with(5, Default::default);
    /// assert_eq!(vec, [1, 2, 3, 0, 0]);
    ///
    /// let mut vec = vec![];
    /// let mut p = 1;
    /// vec.resize_with(4, || { p *= 2; p });
    /// assert_eq!(vec, [2, 4, 8, 16]);
    /// ```
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> T,
    {
        let len = self.len();
        if new_len > len {
            self.extend_with(new_len - len, ExtendFunc(f));
        } else {
            self.truncate(new_len);
        }
    }
}

impl<T: Clone> Vec<T> {
    /// Resizes the `Vec` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the `Vec` is extended by the difference, with each
    /// additional slot filled with `value`. If `new_len` is less than `len`, the `Vec` is simply
    /// truncated.
    ///
    /// This method requires `T` to implement [`Clone`], in order to be able to clone the passed
    /// value.
    /// If you need more flexibility (or want to rely on [`Default`] instead of [`Clone`]), use
    /// [`resize_with`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec!["hello"];
    /// vec.resize(3, "world");
    /// assert_eq!(vec, ["hello", "world", "world"]);
    ///
    /// let mut vec = vec![1, 2, 3, 4];
    /// vec.resize(2, 0);
    /// assert_eq!(vec, [1, 2]);
    /// ```
    pub fn resize(&mut self, new_len: usize, value: T) {
        let len = self.len();

        if new_len > len {
            self.extend_with(new_len - len, ExtendElement(value))
        } else {
            self.truncate(new_len);
        }
    }

    /// Clones and appends all the elements in a slice to the `Vec`.
    ///
    /// Iterates over the slice `other`, clones each element, and then appends it to this `Vec`.
    /// The `other` vector is traversed in-order.
    ///
    /// Note that this function is same as [`extend`] except that it is specialized to work with
    /// slices instead. If and when Rust gets specialization this function will likely be
    /// deprecated (but still available).
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec![1];
    /// vec.extend_from_slice(&[2, 3, 4]);
    /// assert_eq!(vec, [1, 2, 3, 4]);
    /// ```
    ///
    /// [`extend`]: Extend::extend
    pub fn extend_from_slice(&mut self, other: &[T]) {
        self.spec_extend(other.iter())
    }
}

// This code generalizes `extend_with_{element,default}`.
trait ExtendWith<T> {
    fn next(&mut self) -> T;
    fn last(self) -> T;
}

struct ExtendElement<T>(T);
impl<T: Clone> ExtendWith<T> for ExtendElement<T> {
    fn next(&mut self) -> T {
        self.0.clone()
    }
    fn last(self) -> T {
        self.0
    }
}

struct ExtendDefault;
impl<T: Default> ExtendWith<T> for ExtendDefault {
    fn next(&mut self) -> T {
        Default::default()
    }
    fn last(self) -> T {
        Default::default()
    }
}

struct ExtendFunc<F>(F);
impl<T, F: FnMut() -> T> ExtendWith<T> for ExtendFunc<F> {
    fn next(&mut self) -> T {
        (self.0)()
    }
    fn last(mut self) -> T {
        (self.0)()
    }
}

impl<T> Vec<T> {
    /// Extend the vector by `n` values, using the given generator.
    fn extend_with<E: ExtendWith<T>>(&mut self, n: usize, mut value: E) {
        self.reserve(n);

        unsafe {
            let mut ptr = self.as_mut_ptr().add(self.len());
            // Use SetLenOnDrop to work around bug where compiler may not realize the store through
            // `ptr` through` self.set_len() don't alias.
            let mut local_len = SetLenOnDrop::new(self.buf.fat_mut());

            // Write all elements extend the last one
            for _ in 1..n {
                ptr::write(ptr, value.next());
                ptr = ptr.offset(1);
                // Increment the length in every step in case next() panics
                local_len.increment_len(1);
            }

            if n > 0 {
                // We can write the last element directly without cloning needlessly
                ptr::write(ptr, value.last());
                local_len.increment_len(1);
            }

            // len set by scope guard
        }
    }
}

// Set the length of the vec when the `SetLenOnDrop` goes out of scope.
//
// The idea is: The length field in SetLenOnDrop is a local variable that the optimizer will see
// does not alias with any stores through the Vec's data pointer. This is a workaround for alias
// analysis issue #32115
struct SetLenOnDrop<'a> {
    fat: &'a mut usize,
    local_len: usize,
}

impl<'a> SetLenOnDrop<'a> {
    #[inline]
    fn new(fat: &'a mut usize) -> Self {
        SetLenOnDrop {
            local_len: *fat & MASK_LO,
            fat,
        }
    }

    #[inline]
    fn increment_len(&mut self, increment: usize) {
        self.local_len += increment;
    }
}

impl Drop for SetLenOnDrop<'_> {
    #[inline]
    fn drop(&mut self) {
        *self.fat = *self.fat & MASK_HI | self.local_len & MASK_LO;
    }
}

impl<T: PartialEq> Vec<T> {
    /// Removes consecutive repeated elemnts in the vector according to the [`PartialEq`] trait
    /// implementation.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec![1, 2, 2, 3, 2];
    ///
    /// vec.dedup();
    ///
    /// assert_eq!(vec, [1, 2, 3, 2]);
    /// ```
    #[inline]
    pub fn dedup(&mut self) {
        self.dedup_by(|a, b| a == b)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Internal methods and functions
////////////////////////////////////////////////////////////////////////////////

#[doc(hidden)]
pub fn from_elem<T: Clone>(elem: T, n: usize) -> Vec<T> {
    <T as SpecFromElem>::from_elem(elem, n)
}

// Specialization trait used for Vec::from_elem
trait SpecFromElem: Sized {
    fn from_elem(elem: Self, n: usize) -> Vec<Self>;
}

impl<T: Clone> SpecFromElem for T {
    default fn from_elem(elem: Self, n: usize) -> Vec<Self> {
        let mut v = Vec::with_capacity(n);
        v.extend_with(n, ExtendElement(elem));
        v
    }
}

impl SpecFromElem for i8 {
    #[inline]
    fn from_elem(elem: i8, n: usize) -> Vec<i8> {
        if elem == 0 {
            return Vec {
                buf: RawVec::with_capacity_zeroed(n),
            };
        }
        unsafe {
            let mut v = Vec::with_capacity(n);
            ptr::write_bytes(v.as_mut_ptr(), elem as u8, n);
            v.set_len(n);
            v
        }
    }
}

impl SpecFromElem for u8 {
    #[inline]
    fn from_elem(elem: u8, n: usize) -> Vec<u8> {
        if elem == 0 {
            return Vec {
                buf: RawVec::with_capacity_zeroed(n),
            };
        }
        unsafe {
            let mut v = Vec::with_capacity(n);
            ptr::write_bytes(v.as_mut_ptr(), elem, n);
            v.set_len(n);
            v
        }
    }
}

impl<T: Clone + IsZero> SpecFromElem for T {
    #[inline]
    fn from_elem(elem: T, n: usize) -> Vec<T> {
        if elem.is_zero() {
            return Vec {
                buf: RawVec::with_capacity_zeroed(n),
            };
        }
        let mut v = Vec::with_capacity(n);
        v.extend_with(n, ExtendElement(elem));
        v
    }
}

#[rustc_specialization_trait]
unsafe trait IsZero {
    /// Whether this value is zero
    fn is_zero(&self) -> bool;
}

macro_rules! impl_is_zero {
    ($t:ty, $is_zero:expr) => {
        unsafe impl IsZero for $t {
            #[inline]
            fn is_zero(&self) -> bool {
                $is_zero(*self)
            }
        }
    };
}

impl_is_zero!(i16, |x| x == 0);
impl_is_zero!(i32, |x| x == 0);
impl_is_zero!(i64, |x| x == 0);
impl_is_zero!(i128, |x| x == 0);
impl_is_zero!(isize, |x| x == 0);

impl_is_zero!(u16, |x| x == 0);
impl_is_zero!(u32, |x| x == 0);
impl_is_zero!(u64, |x| x == 0);
impl_is_zero!(u128, |x| x == 0);
impl_is_zero!(usize, |x| x == 0);

impl_is_zero!(bool, |x| x == false);
impl_is_zero!(char, |x| x == '\0');

impl_is_zero!(f32, |x: f32| x.to_bits() == 0);
impl_is_zero!(f64, |x: f64| x.to_bits() == 0);

unsafe impl<T> IsZero for *const T {
    #[inline]
    fn is_zero(&self) -> bool {
        (*self).is_null()
    }
}

unsafe impl<T> IsZero for *mut T {
    #[inline]
    fn is_zero(&self) -> bool {
        (*self).is_null()
    }
}

// `Option<&T>` and `Option<Box<T>>` are guaranteed to represent `None` as null.
// For fat pointers, the bytes that would be the pointer metadata in the `Some` variant are padding
// in the `None` variant, so ignoring them and zero-initializing instead is ok.
// `Option<&mut T>` never implements `Clone`, so there's no need for an impl of `SpecFromElem`.

unsafe impl<T: ?Sized> IsZero for Option<&T> {
    #[inline]
    fn is_zero(&self) -> bool {
        self.is_none()
    }
}

unsafe impl<T: ?Sized> IsZero for Option<Box<T>> {
    #[inline]
    fn is_zero(&self) -> bool {
        self.is_none()
    }
}

////////////////////////////////////////////////////////////////////////////////
// Common trait implementations for Vec
////////////////////////////////////////////////////////////////////////////////

impl<T> ops::Deref for Vec<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl<T> ops::DerefMut for Vec<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }
}

impl<T: Clone> Clone for Vec<T> {
    fn clone(&self) -> Vec<T> {
        let mut vec = Vec::with_capacity(self.len());
        vec.extend_from_slice(&**self);
        vec
    }
}

impl<T: Hash> Hash for Vec<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

impl<T, I: SliceIndex<[T]>> Index<I> for Vec<T> {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        Index::index(&**self, index)
    }
}

impl<T, I: SliceIndex<[T]>> IndexMut<I> for Vec<T> {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        IndexMut::index_mut(&mut **self, index)
    }
}

impl<T> Extend<T> for Vec<T> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        <Self as SpecExtend<T, I::IntoIter>>::spec_extend(self, iter.into_iter())
    }
}

impl<T> FromIterator<T> for Vec<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Vec<T> {
        <Self as SpecExtend<T, I::IntoIter>>::from_iter(iter.into_iter())
    }
}

impl<T> IntoIterator for Vec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    /// Creates a consuming iterator, that is, one that moves each value out of the vector (from
    /// start to end). The vector cannot be used after calling this.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let v = vec!["a".to_string(), "b".to_string()];
    /// for s in v.into_iter() {
    ///     // s has type String, not &String
    ///     println!("{}", s);
    /// }
    /// ```
    #[inline]
    fn into_iter(self) -> IntoIter<T> {
        unsafe {
            let mut me = ManuallyDrop::new(self);
            let begin = me.as_mut_ptr();
            let end = if mem::size_of::<T>() == 0 {
                arith_offset(begin as *const i8, me.len() as isize) as *const T
            } else {
                begin.add(me.len()) as *const T
            };
            let cap = me.buf.capacity();
            IntoIter {
                buf: NonNull::new_unchecked(begin),
                phantom: PhantomData,
                cap,
                ptr: begin,
                end,
            }
        }
    }
}

impl<'a, T> IntoIterator for &'a Vec<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> slice::Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Vec<T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> slice::IterMut<'a, T> {
        self.iter_mut()
    }
}

// Specialization trait used for Vec::from_iter and Vec::extend
trait SpecExtend<T, I> {
    fn from_iter(iter: I) -> Self;
    fn spec_extend(&mut self, iter: I);
}

impl<T, I> SpecExtend<T, I> for Vec<T>
where
    I: Iterator<Item = T>,
{
    default fn from_iter(mut iterator: I) -> Self {
        // Unroll the first iteration, as the vector is going to be expanded on this iteration in
        // every case when the iterable is not empty, but the loop in extend_desugared() is not
        // going to see the vector being full in the few subsequent loop iterations. So we get
        // better branch prediction.
        let mut vec = match iterator.next() {
            None => return Vec::new(),
            Some(element) => {
                let (lower, _) = iterator.size_hint();
                let mut vec = Vec::with_capacity(lower.saturating_add(1));
                unsafe {
                    ptr::write(vec.as_mut_ptr(), element);
                    vec.set_len(1);
                }
                vec
            }
        };
        <Vec<T> as SpecExtend<T, I>>::spec_extend(&mut vec, iterator);
        vec
    }

    default fn spec_extend(&mut self, iter: I) {
        self.extend_desugared(iter)
    }
}

impl<T, I> SpecExtend<T, I> for Vec<T>
where
    I: TrustedLen<Item = T>,
{
    default fn from_iter(iterator: I) -> Self {
        let mut vec = Vec::new();
        vec.spec_extend(iterator);
        vec
    }

    default fn spec_extend(&mut self, iterator: I) {
        // This is the case for a TrustedLen iterator.
        let (low, high) = iterator.size_hint();
        if let Some(high_value) = high {
            debug_assert_eq!(
                low,
                high_value,
                "TrustedLen iterator's size hint is not exact: {:?}",
                (low, high)
            );
        }
        if let Some(additional) = high {
            self.reserve(additional);
            unsafe {
                let mut ptr = self.as_mut_ptr().add(self.len());
                let mut local_len = SetLenOnDrop::new(self.buf.fat_mut());
                iterator.for_each(move |element| {
                    ptr::write(ptr, element);
                    ptr = ptr.offset(1);
                    local_len.increment_len(1);
                });
            }
        } else {
            self.extend_desugared(iterator)
        }
    }
}

// impl<T> SpecExtend<T, IntoIter<T>> for Vec<T> {
//     fn from_iter(iterator: IntoIter<T>) -> Self {
//         // A common
//     }
// }

impl<'a, T: 'a, I> SpecExtend<&'a T, I> for Vec<T>
where
    I: Iterator<Item = &'a T>,
    T: Clone,
{
    default fn from_iter(iterator: I) -> Self {
        SpecExtend::from_iter(iterator.cloned())
    }

    default fn spec_extend(&mut self, iterator: I) {
        self.spec_extend(iterator.cloned())
    }
}

impl<'a, T: 'a> SpecExtend<&'a T, slice::Iter<'a, T>> for Vec<T>
where
    T: Copy,
{
    fn spec_extend(&mut self, iterator: slice::Iter<'a, T>) {
        let slice = iterator.as_slice();
        self.reserve(slice.len());
        unsafe {
            let len = self.len();
            let dst_slice = slice::from_raw_parts_mut(self.as_mut_ptr().add(len), slice.len());
            dst_slice.copy_from_slice(slice);
            self.set_len(len + slice.len());
        }
    }
}

impl<T> Vec<T> {
    fn extend_desugared<I: Iterator<Item = T>>(&mut self, mut iterator: I) {
        // This is the case for a general iterator.
        //
        // This function should be the moral equivalent of:
        //
        //     for item in iterator {
        //         self.push(item);
        //     }
        while let Some(element) = iterator.next() {
            let len = self.len();
            if len == self.capacity() {
                let (lower, _) = iterator.size_hint();
                self.reserve(lower.saturating_add(1));
            }
            unsafe {
                ptr::write(self.as_mut_ptr().add(len), element);
                // NB can't overflow since we would have had to alloc the address space
                self.set_len(len + 1);
            }
        }
    }

    /// Creates a splicing iterator that replaces the specified range in the vector with the given
    /// `replace_with` iterator and yields the remove items.
    /// `replace_with` does not need to be the same length as `range`.
    ///
    /// `range` is removed even if the iterator is not consumed until the end.
    ///
    /// It is unspecified how many elements are removed from the vector if the `Splice` value is
    /// leaked.
    ///
    /// The input iterator `replace_with` is only consumed when the `Splice` value is dropped.
    ///
    /// This is optimal if:
    ///
    /// * The tail (elements in the vector after `range`) is empty,
    /// * or `replace_with` yields fewer elements than `range`'s length
    /// * or the lower bound of its `size_hint()` is exact.
    ///
    /// Otherwise, a temporary vector is allocated and the tail is moved twice.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if the end point is greater
    /// than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut v = vec![1, 2, 3];
    /// let new = [7, 8];
    /// let u: Vec<_> = v.splice(..2, new.iter().cloned()).collect();
    /// assert_eq!(v, &[7, 8, 3]);
    /// assert_eq!(u, &[1, 2]);
    /// ```
    #[inline]
    pub fn splice<R, I>(&mut self, range: R, replace_with: I) -> Splice<'_, I::IntoIter>
    where
        R: RangeBounds<usize>,
        I: IntoIterator<Item = T>,
    {
        Splice {
            drain: self.drain(range),
            replace_with: replace_with.into_iter(),
        }
    }
}

macro_rules! __impl_slice_eq1 {
    ([$($vars:tt)*] $lhs:ty, $rhs:ty $(where $ty:ty: $bound:ident)?) => {
        impl<A, B, $($vars)*> PartialEq<$rhs> for $lhs
        where
            A: PartialEq<B>,
            $($ty: $bound)?
        {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool { self[..] == other[..] }
            #[inline]
            fn ne(&self, other: &$rhs) -> bool { self[..] != other[..] }
        }
    }
}

__impl_slice_eq1! { [] Vec<A>, Vec<B> }
__impl_slice_eq1! { [] Vec<A>, &[B] }
__impl_slice_eq1! { [] Vec<A>, &mut [B] }
__impl_slice_eq1! { [] &[A], Vec<B> }
__impl_slice_eq1! { [] &mut [A], Vec<B> }
__impl_slice_eq1! { [] Cow<'_, [A]>, Vec<B> where A: Clone }
// __impl_slice_eq1! { [] Cow<'_, [A]>, &[B], A: Clone }
// __impl_slice_eq1! { [] Cow<'_, [A]>, &mut [B], A: Clone }
__impl_slice_eq1! { [const N: usize] Vec<A>, [B; N] }
__impl_slice_eq1! { [const N: usize] Vec<A>, &[B; N] }

/// Implements comparison of vectors, lexographically.
impl<T: PartialOrd> PartialOrd for Vec<T> {
    #[inline]
    fn partial_cmp(&self, other: &Vec<T>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<T: Eq> Eq for Vec<T> {}

/// Implements ordering of vectors, lexographically.
impl<T: Ord> Ord for Vec<T> {
    #[inline]
    fn cmp(&self, other: &Vec<T>) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

unsafe impl<#[may_dangle] T> Drop for Vec<T> {
    fn drop(&mut self) {
        unsafe {
            // use drop for [T]
            // use a raw slice to refer to the elements of the vector as weakest necessary type;
            // could avoid questions of validity in certain cases
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.as_mut_ptr(), self.len()))
        }
    }
}

impl<T> Default for Vec<T> {
    /// Creates an empty `Vec<T>`.
    fn default() -> Vec<T> {
        Vec::new()
    }
}

impl<T: fmt::Debug> fmt::Debug for Vec<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T> AsRef<Vec<T>> for Vec<T> {
    fn as_ref(&self) -> &Vec<T> {
        self
    }
}

impl<T> AsMut<Vec<T>> for Vec<T> {
    fn as_mut(&mut self) -> &mut Vec<T> {
        self
    }
}

impl<T> AsRef<[T]> for Vec<T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T> AsMut<[T]> for Vec<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T: Clone> From<&[T]> for Vec<T> {
    fn from(s: &[T]) -> Vec<T> {
        crate::slice::to_vec(s)
    }
}

impl<T: Clone> From<&mut [T]> for Vec<T> {
    fn from(s: &mut [T]) -> Vec<T> {
        crate::slice::to_vec(s)
    }
}

impl<T, const N: usize> From<[T; N]> for Vec<T> {
    fn from(s: [T; N]) -> Vec<T> {
        crate::slice::into_vec(Box::new(s))
    }
}

impl<'a, T> From<Cow<'a, [T]>> for Vec<T>
where
    [T]: ToOwned<Owned = Vec<T>>,
{
    fn from(s: Cow<'a, [T]>) -> Vec<T> {
        s.into_owned()
    }
}

impl<T> From<Box<[T]>> for Vec<T> {
    fn from(s: Box<[T]>) -> Vec<T> {
        crate::slice::into_vec(s)
    }
}

impl<T> From<Vec<T>> for Box<[T]> {
    fn from(v: Vec<T>) -> Box<[T]> {
        v.into_boxed_slice()
    }
}

impl From<&str> for Vec<u8> {
    fn from(s: &str) -> Vec<u8> {
        From::from(s.as_bytes())
    }
}

////////////////////////////////////////////////////////////////////////////////
// Clone-on-write
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Iterators
////////////////////////////////////////////////////////////////////////////////

/// An iterator that moves out of a vector.
///
/// This `struct` is created by the `into_iter` method on [`Vec`] (provided by the [`IntoIterator`]
/// trait).
pub struct IntoIter<T> {
    buf: NonNull<T>,
    phantom: PhantomData<T>,
    cap: usize,
    ptr: *const T,
    end: *const T,
}

impl<T: fmt::Debug> fmt::Debug for IntoIter<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IntoIter").field(&self.as_slice()).finish()
    }
}

impl<T> IntoIter<T> {
    /// Returns the remaining items of this iterator as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let vec = vec!['a', 'b', 'c'];
    /// let mut into_iter = vec.into_iter();
    /// assert_eq!(into_iter.as_slice(), &['a', 'b', 'c']);
    /// let _ = into_iter.next().unwrap();
    /// assert_eq!(into_iter.as_slice(), &['b', 'c']);
    /// ```
    pub fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.ptr, self.len()) }
    }

    /// Returns the remaining items of this iterator as a mutable slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let vec = vec!['a', 'b', 'c'];
    /// let mut into_iter = vec.into_iter();
    /// assert_eq!(into_iter.as_slice(), &['a', 'b', 'c']);
    /// into_iter.as_mut_slice()[2] = 'z';
    /// assert_eq!(into_iter.next().unwrap(), 'a');
    /// assert_eq!(into_iter.next().unwrap(), 'b');
    /// assert_eq!(into_iter.next().unwrap(), 'z');
    /// ```
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { &mut *self.as_raw_mut_slice() }
    }

    fn as_raw_mut_slice(&mut self) -> *mut [T] {
        unsafe { &mut *ptr::slice_from_raw_parts_mut(self.ptr as *mut T, self.len()) }
    }
}

impl<T> AsRef<[T]> for IntoIter<T> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

unsafe impl<T: Send> Send for IntoIter<T> {}
unsafe impl<T: Sync> Sync for IntoIter<T> {}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        if self.ptr as *const _ == self.end {
            None
        } else if mem::size_of::<T>() == 0 {
            // purposely don't use 'ptr.offset' because for vectors with 0-size elements
            // this would return the same pointer.
            self.ptr = unsafe { arith_offset(self.ptr as *const T, 1) as *mut T };

            // Make up a value of this ZST.
            Some(unsafe { mem::zeroed() })
        } else {
            let old = self.ptr;
            self.ptr = unsafe { self.ptr.offset(1) };

            Some(unsafe { ptr::read(old) })
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = if mem::size_of::<T>() == 0 {
            (self.end as usize).wrapping_sub(self.ptr as usize)
        } else {
            unsafe { self.end.offset_from(self.ptr) as usize }
        };
        (exact, Some(exact))
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        if self.end == self.ptr {
            None
        } else if mem::size_of::<T>() == 0 {
            // See above for why 'ptr.offset' isn't used
            self.end = unsafe { arith_offset(self.end as *const T, -1) as *mut T };

            // Make up a value of this ZST.
            Some(unsafe { mem::zeroed() })
        } else {
            self.end = unsafe { self.end.offset(-1) };

            Some(unsafe { ptr::read(self.end) })
        }
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn is_empty(&self) -> bool {
        self.ptr == self.end
    }
}

impl<T> FusedIterator for IntoIter<T> {}

unsafe impl<T> TrustedLen for IntoIter<T> {}

impl<T: Clone> Clone for IntoIter<T> {
    fn clone(&self) -> IntoIter<T> {
        Vec::from(self.as_slice()).into_iter()
    }
}

unsafe impl<#[may_dangle] T> Drop for IntoIter<T> {
    fn drop(&mut self) {
        struct DropGuard<'a, T>(&'a mut IntoIter<T>);

        impl<T> Drop for DropGuard<'_, T> {
            fn drop(&mut self) {
                // RawVec handles deallocation
                let _ = unsafe { RawVec::from_raw_parts(self.0.buf.as_ptr(), self.0.cap, 0) };
            }
        }

        let guard = DropGuard(self);
        // destroy the remaining elements
        unsafe {
            ptr::drop_in_place(guard.0.as_raw_mut_slice());
        }
        // now `guard` will be dropped and do the rest
    }
}

/// A draining iterator for `Vec<T>`.
///
/// This `struct` is created by the [`Vec::drain`].
pub struct Drain<'a, T: 'a> {
    /// Index of tail to preserve
    tail_start: usize,
    /// Length of tail
    tail_len: usize,
    /// Current remaining range to remove
    iter: slice::Iter<'a, T>,
    vec: NonNull<Vec<T>>,
}

impl<T: fmt::Debug> fmt::Debug for Drain<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain").field(&self.iter.as_slice()).finish()
    }
}

impl<'a, T> Drain<'a, T> {
    /// Returns the remaining items of this iterator as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ve::vec;
    /// let mut vec = vec!['a', 'b', 'c'];
    /// let mut drain = vec.drain(..);
    /// assert_eq!(drain.as_slice(), &['a', 'b', 'c']);
    /// let _ = drain.next().unwrap();
    /// assert_eq!(drain.as_slice(), &['b', 'c']);
    /// ```
    pub fn as_slice(&self) -> &[T] {
        self.iter.as_slice()
    }
}

impl<'a, T> AsRef<[T]> for Drain<'a, T> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

unsafe impl<T: Sync> Sync for Drain<'_, T> {}
unsafe impl<T: Send> Send for Drain<'_, T> {}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.iter
            .next()
            .map(|elt| unsafe { ptr::read(elt as *const _) })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T> DoubleEndedIterator for Drain<'_, T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.iter
            .next_back()
            .map(|elt| unsafe { ptr::read(elt as *const _) })
    }
}

impl<T> Drop for Drain<'_, T> {
    fn drop(&mut self) {
        /// Continues dropping the remaining elements in the `Drain`, then moves back the
        /// un-`Drain`ed elements to restore the original `Vec`.
        struct DropGuard<'r, 'a, T>(&'r mut Drain<'a, T>);

        impl<'r, 'a, T> Drop for DropGuard<'r, 'a, T> {
            fn drop(&mut self) {
                // Continue the same loop we have below. If the loop already finished, this does
                // nothing.
                self.0.for_each(drop);

                if self.0.tail_len > 0 {
                    unsafe {
                        let source_vec = self.0.vec.as_mut();
                        // memmove back untouched tail, update to new length
                        let start = source_vec.len();
                        let tail = self.0.tail_start;
                        if tail != start {
                            let src = source_vec.as_ptr().add(tail);
                            let dst = source_vec.as_mut_ptr().add(start);
                            ptr::copy(src, dst, self.0.tail_len);
                        }
                        source_vec.set_len(start + self.0.tail_len);
                    }
                }
            }
        }

        // exhaust self first
        while let Some(item) = self.next() {
            let guard = DropGuard(self);
            drop(item);
            mem::forget(guard);
        }

        // Drop a `DropGuard` to move back the non-drained tail of `self`.
        DropGuard(self);
    }
}

impl<T> ExactSizeIterator for Drain<'_, T> {
    fn is_empty(&self) -> bool {
        self.iter.is_empty()
    }
}

impl<T> FusedIterator for Drain<'_, T> {}

/// A splicing iterator for `Vec`.
///
/// This struct is created by the [`Vec::splice`].
/// See its documentation for more.
#[derive(Debug)]
pub struct Splice<'a, I: Iterator + 'a> {
    drain: Drain<'a, I::Item>,
    replace_with: I,
}

impl<I: Iterator> Iterator for Splice<'_, I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.drain.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.drain.size_hint()
    }
}

impl<I: Iterator> DoubleEndedIterator for Splice<'_, I> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.drain.next_back()
    }
}

impl<I: Iterator> ExactSizeIterator for Splice<'_, I> {}

impl<I: Iterator> Drop for Splice<'_, I> {
    fn drop(&mut self) {
        self.drain.by_ref().for_each(drop);

        unsafe {
            if self.drain.tail_len == 0 {
                self.drain.vec.as_mut().extend(self.replace_with.by_ref());
                return;
            }

            // First fill the range left by drain().
            if !self.drain.fill(&mut self.replace_with) {
                return;
            }

            // There may be more elements. Use the lower bound as an estimate.
            // FIXME: Is the upper bound a better guess? Or something else?
            let (lower_bound, _upper_bound) = self.replace_with.size_hint();
            if lower_bound > 0 {
                self.drain.move_tail(lower_bound);
                if !self.drain.fill(&mut self.replace_with) {
                    return;
                }
            }

            // Collect any remaining elements.
            // This is a zero-length vector which does not allocate if `lower_bound` was exact.
            let mut collected = self
                .replace_with
                .by_ref()
                .collect::<Vec<I::Item>>()
                .into_iter();
            // Now we have an exact count.
            if collected.len() > 0 {
                self.drain.move_tail(collected.len());
                let filled = self.drain.fill(&mut collected);
                debug_assert!(filled);
                debug_assert_eq!(collected.len(), 0);
            }
        }
        // Let `Drain::Drop` move the tail back if necessary and restore `vec.len`.
    }
}

/// Private helper methods for `Splice::Drop`
impl<T> Drain<'_, T> {
    /// The range from `self.vec.len` to `self.tail_start` contains elements that have been moved
    /// out.
    /// Fill that range as much as possible with the new elements from the `replace_with` iterator.
    /// Returns `true` if we filled the entire range. (`replace_with.next()` didn't return `None`.)
    unsafe fn fill<I: Iterator<Item = T>>(&mut self, replace_with: &mut I) -> bool {
        let vec = unsafe { self.vec.as_mut() };
        let range_start = vec.len();
        let range_end = self.tail_start;
        let range_slice = unsafe {
            slice::from_raw_parts_mut(vec.as_mut_ptr().add(range_start), range_end - range_start)
        };

        for place in range_slice {
            if let Some(new_item) = replace_with.next() {
                unsafe { ptr::write(place, new_item) };
                vec.set_len(vec.len() + 1);
            } else {
                return false;
            }
        }
        true
    }

    // Makes room for inserting more elements before the tail.
    unsafe fn move_tail(&mut self, additional: usize) {
        let vec = unsafe { self.vec.as_mut() };
        let len = self.tail_start + self.tail_len;
        vec.buf.reserve(len, additional);

        let new_tail_start = self.tail_start + additional;
        unsafe {
            let src = vec.as_ptr().add(self.tail_start);
            let dst = vec.as_mut_ptr().add(new_tail_start);
            ptr::copy(src, dst, self.tail_len);
        }
        self.tail_start = new_tail_start;
    }
}
