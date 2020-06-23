/// Implementation details for `Vec`.
use core::alloc::AllocInit::{self, *};
use core::alloc::{AllocRef, Layout, LayoutErr, MemoryBlock};
use core::mem::{self, ManuallyDrop, MaybeUninit};
use core::ptr::NonNull;
use core::{cmp, slice};

use alloc::alloc::ReallocPlacement::{self, *};
use alloc::alloc::{handle_alloc_error, Global};
use alloc::boxed::Box;
use alloc::collections::TryReserveError::{self, *};

pub(crate) const MASK_LO: usize = u32::MAX as usize; // len
pub(crate) const MASK_HI: usize = !MASK_LO; // cap

/// A low-level utility for more ergonomically allocating, reallocating, and deallocating a buffer
/// of memory on the heap without having to worry about all the corner cases involved. This type is
/// excellent for building your own data structures like Vec and Veque.
pub(crate) struct RawVec<T, A: AllocRef = Global> {
    ptr: NonNull<T>,
    /// Consists of `cap` and `len`.
    fat: usize,
    alloc: A,
}

impl<T> RawVec<T, Global> {
    /// Creates the biggest possible `RawVec` (on the system heap) without allocating. If `T` has
    /// positive size, then this makes a `RawVec` with capacity `0`. If `T` is zero-sized, then it
    /// makes a `RawVec` with capacity `usize::MAX`. Useful for implementing delayed allocation.
    pub(crate) const fn new() -> Self {
        Self::new_in(Global)
    }

    /// Constructs a new, empty `Vec<T>` with the specified capacity.
    #[inline]
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_in(capacity, Global)
    }

    /// Like `with_capacity`, but guarantees the buffer is zeroed.
    #[inline]
    pub(crate) fn with_capacity_zeroed(capacity: usize) -> Self {
        Self::with_capacity_zeroed_in(capacity, Global)
    }

    /// Reconstitutes a `RawVec` from a pointer, capacity and length.
    ///
    /// # Safety
    ///
    /// The `ptr` must be allocated (on the system heap), and with the given `capacity`.
    /// The `capacity` cannot exceed `u32::MAX` for sized types. ZST vectors may have capacity up to
    /// `usize::MAX`.
    /// If the `ptr` and `capacity` come from a `RawVec`, then this is guaranteed.
    #[inline]
    pub(crate) unsafe fn from_raw_parts(ptr: *mut T, capacity: usize, len: usize) -> Self {
        Self::from_raw_parts_in(ptr, capacity, len, Global)
    }

    /// Converts the entire buffer into `Box<[MaybeUninit<T>]>` with the specified `len`.
    ///
    /// Note that this will correctly reconstitute any `cap` change that may have been performed.
    /// (See description of type for details.)
    ///
    /// # Safety
    ///
    /// * `len` must be greater than or equal to the most recently requested capacity
    /// * `len` must be less than or equal to `self.cap()`
    pub(crate) unsafe fn into_box(self, len: usize) -> Box<[MaybeUninit<T>]> {
        // Sanity-check on half of safety requirement (we cannot check the other half).
        debug_assert!(
            len <= self.cap(),
            "`len` must be smaller or equal to `self.cap()`"
        );

        let me = ManuallyDrop::new(self);
        let slice = slice::from_raw_parts_mut(me.ptr() as *mut MaybeUninit<T>, len);
        Box::from_raw(slice)
    }
}

impl<T, A: AllocRef> RawVec<T, A> {
    /// Like `new`, but parameterized over the choice of allocator for the
    /// returned `RawVec`.
    pub(crate) const fn new_in(alloc: A) -> Self {
        Self {
            ptr: NonNull::dangling(),
            fat: 0,
            alloc,
        }
    }

    /// Like `with_capacity`, but parameterized over the choice of allocator for the returned
    /// `RawVec`.
    #[inline]
    pub(crate) fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Self::allocate_in(capacity, 0, Uninitialized, alloc)
    }

    /// Like `with_capacity_zeroed`, but parameterized over the choice of allocator for the
    /// returned `RawVec`.
    #[inline]
    pub(crate) fn with_capacity_zeroed_in(capacity: usize, alloc: A) -> Self {
        Self::allocate_in(capacity, capacity, Zeroed, alloc)
    }

    fn allocate_in(capacity: usize, len: usize, init: AllocInit, mut alloc: A) -> Self {
        if mem::size_of::<T>() == 0 {
            Self::new_in(alloc)
        } else {
            let layout = Layout::array::<T>(capacity).unwrap_or_else(|_| capacity_overflow());
            alloc_guard(layout.size()).unwrap_or_else(|_| capacity_overflow());

            let memory = alloc
                .alloc(layout, init)
                .unwrap_or_else(|_| handle_alloc_error(layout));
            Self {
                ptr: memory.ptr.cast(),
                // Safety: No need for MASK_LO, already checked from alloc_guard
                fat: Self::capacity_from_bytes(memory.size) << 32 | len,
                alloc,
            }
        }
    }

    /// Reconstitutes a `RawVec` from a pointer, capacity, length and allocator.
    ///
    /// # Safety
    ///
    /// The `ptr` must be allocated (via the given allocator `alloc`), and with the given
    /// `capacity`.
    /// The `capacity` cannot exceed `u32::MAX` for sized types. ZST vectors may have a capacity up
    /// to `usize::MAX`.
    /// If the `ptr` and `capacity` come from a `RawVec` created via `alloc`, then this is
    /// guaranteed.
    #[inline]
    pub(crate) unsafe fn from_raw_parts_in(
        ptr: *mut T,
        capacity: usize,
        length: usize,
        alloc: A,
    ) -> Self {
        Self {
            ptr: NonNull::new_unchecked(ptr),
            fat: (capacity & MASK_LO) << 32 | length & MASK_LO,
            alloc,
        }
    }

    /// Gets a raw pointer to the start of the allocation. Note that this is `NonNull::dangling()`
    /// if `capacity == 0` or `T` is zero-sized. In the former case, you must be careful.
    pub(crate) fn ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }

    /// Gets the capacity of the allocation.
    ///
    /// This will always be `usize::MAX` if `T` is zero-sized.
    pub(crate) fn cap(&self) -> usize {
        if mem::size_of::<T>() == 0 {
            usize::MAX
        } else {
            (self.fat & MASK_HI) >> 32
        }
    }

    /// Gets the length of the allocation.
    pub(crate) fn len(&self) -> usize {
        self.fat & MASK_LO
    }

    /// Set the length of the allocation.
    pub(crate) fn set_len(&mut self, len: usize) {
        self.fat = self.fat & MASK_HI | len & MASK_LO;
    }

    /// Returns a mutable reference to fat.
    pub(crate) fn fat_mut(&mut self) -> &mut usize {
        &mut self.fat
    }

    /// Returns a shared reference to the allocator backing this `RawVec`.
    pub(crate) fn alloc(&self) -> &A {
        &self.alloc
    }

    /// Returns a mutable reference to the allocator backing this `RawVec`.
    pub(crate) fn alloc_mut(&mut self) -> &mut A {
        &mut self.alloc
    }

    fn current_memory(&self) -> Option<(NonNull<u8>, Layout)> {
        if mem::size_of::<T>() == 0 || self.cap() == 0 {
            None
        } else {
            // We have allocated chunk of memory, so we can bypass runtime checks to get our
            // current layout.
            unsafe {
                let align = mem::size_of::<T>();
                let size = mem::size_of::<T>() * self.cap();
                let layout = Layout::from_size_align_unchecked(size, align);
                Some((self.ptr.cast(), layout))
            }
        }
    }

    /// Ensures that the buffer contains at least enough space to hold `len + additional` elements.
    /// If it doesn't already have enough capacity, will reallocate enough space plus comfortable
    /// slack space to get amortized `O(1)` behavior. Will limit this behavior if it would
    /// needlessly cause itself to panic.
    ///
    /// If `len` exceeds `self.cap()`, this may fail to actually allocate the requested space.
    /// This is not really unsafe, but the unsafe code *you* write that relies on the behavior of
    /// this function may break.
    ///
    /// This is ideal or implementing a bulk-push operation like `extend`.
    ///
    /// # Panics
    ///
    /// * Panics if the requested capacity exceeds `u32::MAX` bytes.
    ///
    /// # Aborts
    ///
    /// Aborts on OOM.
    pub(crate) fn reserve(&mut self, len: usize, additional: usize) {
        match self.try_reserve(len, additional) {
            Err(CapacityOverflow) => capacity_overflow(),
            Err(AllocError { layout, .. }) => handle_alloc_error(layout),
            Ok(()) => { /* yay */ }
        }
    }

    /// The same as `reserve`, but returns on errors instead of panicking or aborting.
    pub(crate) fn try_reserve(
        &mut self,
        len: usize,
        additional: usize,
    ) -> Result<(), TryReserveError> {
        if self.needs_to_grow(len, additional) {
            self.grow_amortized(len, additional)
        } else {
            Ok(())
        }
    }

    /// Ensures that the buffer contains at least enough space to hold `len + additional` elements.
    /// If it doesn't already, will reallocate the minimum possible ammount of memory necessary.
    /// Generally this will be exactly the amount of memory necessary, but in principle the
    /// allocator is free to give back more than what we asked for.
    ///
    /// If `len` exceeds `self.cap()`, this may fail to actually allocate the requested space. This
    /// is not really unsafe, but the unsafe code *you* write that relies on the behavior of this
    /// function may break.
    ///
    /// # Panics
    ///
    /// * Panics if the requested capacity exceeds `u32::MAX` bytes.
    ///
    /// # Aborts
    ///
    /// Aborts on OOM.
    pub(crate) fn reserve_exact(&mut self, len: usize, additional: usize) {
        match self.try_reserve_exact(len, additional) {
            Err(CapacityOverflow) => capacity_overflow(),
            Err(AllocError { layout, .. }) => handle_alloc_error(layout),
            Ok(()) => { /* yay */ }
        }
    }

    /// The same as `reserve_exact`, but returns on errors instead of panicking or aborting.
    pub(crate) fn try_reserve_exact(
        &mut self,
        len: usize,
        additional: usize,
    ) -> Result<(), TryReserveError> {
        if self.needs_to_grow(len, additional) {
            self.grow_exact(len, additional)
        } else {
            Ok(())
        }
    }

    /// Shrinks the allocation down to the specified amount. If the given amount is 0, actually
    /// completely deallocates.
    ///
    /// # Panics
    ///
    /// Panics if the given amount is *larger* than the current capacity.
    ///
    /// # Aborts
    ///
    /// Aborts on OOM.
    pub(crate) fn shrink_to_fit(&mut self, amount: usize) {
        match self.shrink(amount, MayMove) {
            Err(CapacityOverflow) => capacity_overflow(),
            Err(AllocError { layout, .. }) => handle_alloc_error(layout),
            Ok(()) => { /* yay */ }
        }
    }
}

impl<T, A: AllocRef> RawVec<T, A> {
    /// Returns if the buffer needs to grow to fulfill the needed extra capacity.
    /// Mainly used to make inlining reserve-calls possible without inlining `grow`.
    fn needs_to_grow(&self, len: usize, additional: usize) -> bool {
        additional > self.cap().wrapping_sub(len)
    }

    fn capacity_from_bytes(excess: usize) -> usize {
        debug_assert_ne!(mem::size_of::<T>(), 0);
        excess / mem::size_of::<T>()
    }

    fn set_memory(&mut self, memory: MemoryBlock) {
        self.ptr = memory.ptr.cast();
        self.fat = (memory.size & MASK_LO) << 32 | self.fat & MASK_LO;
    }

    /// This method is usually instantiated many times. So we want it to be as small as possible,
    /// to improve compile times. But we also want as much of generated code to run faster.
    /// Therefore, this method is carefully written so that all the code that depends on `T` is
    /// within it, while as much of the code that doesn't depend on `T` as possible is in functions
    /// that are non-generic over `T`.
    fn grow_amortized(&mut self, len: usize, additional: usize) -> Result<(), TryReserveError> {
        // This is ensured by the calling contents.
        debug_assert!(additional > 0);

        if mem::size_of::<T>() == 0 {
            // Since we return a capacity of `u32::MAX` when `elem_size` is 0, getting to here
            // necessarily means the `RawVec` is overfull.
            return Err(CapacityOverflow);
        }

        // Nothing we can really do about these checks, sadly.
        let required_cap = len.checked_add(additional).ok_or(CapacityOverflow)?;

        // This guarantees exponential growth. The doubling cannot overflow because
        // `cap <= isize::MAX` and the type of `cap` is `u32`.
        let cap = cmp::max(self.cap() * 2, required_cap);

        // Tiny Vecs are dump. Skip to:
        // - 8 if the element size is 1, because any heap allocators is likely to round up a
        //   request of less than 8 bytes to at least 8 bytes.
        // - 4 if elements are moderate-sized (<= 1KiB).
        // - 1 otherwise, to avoid wasting too much space for very short Vecs.
        // Note that `min_non_zero_cap` is computed statistically.
        let elem_size = mem::size_of::<T>();
        let min_non_zero_cap = if elem_size == 1 {
            8
        } else if elem_size <= 1024 {
            4
        } else {
            1
        };
        let cap = cmp::max(min_non_zero_cap, cap);

        let new_layout = Layout::array::<T>(cap);

        // `finish_grow` is non-generic over `T`.
        let memory = finish_grow(new_layout, self.current_memory(), &mut self.alloc)?;
        self.set_memory(memory);
        Ok(())
    }

    /// The constraints on this method are much the same as those on `grow_amortized`, but this
    /// method is usually instantiated less often so it's less critical.
    fn grow_exact(&mut self, len: usize, additional: usize) -> Result<(), TryReserveError> {
        if mem::size_of::<T>() == 0 {
            // Since we return a capacity of `u32::MAX` when `elem_size` is 0, getting to here
            // necessarily means the `RawVec` is overfull.
            return Err(CapacityOverflow);
        }

        let cap = len.checked_add(additional).ok_or(CapacityOverflow)?;
        let new_layout = Layout::array::<T>(cap);

        // `finish_grow` is non-generic over `T`.
        let memory = finish_grow(new_layout, self.current_memory(), &mut self.alloc)?;
        self.set_memory(memory);
        Ok(())
    }

    fn shrink(
        &mut self,
        amount: usize,
        placement: ReallocPlacement,
    ) -> Result<(), TryReserveError> {
        assert!(amount <= self.cap(), "Tried to shrink to a larger capacity");

        let (ptr, layout) = if let Some(mem) = self.current_memory() {
            mem
        } else {
            return Ok(());
        };
        let new_size = amount * mem::size_of::<T>();

        let memory = unsafe {
            self.alloc
                .shrink(ptr, layout, new_size, placement)
                .map_err(|_| AllocError {
                    layout: Layout::from_size_align_unchecked(new_size, layout.align()),
                    non_exhaustive: (),
                })?
        };
        self.set_memory(memory);
        Ok(())
    }
}

// This function is outside `RawVec` to minimize compile times. See the comment above
// `RawVec::grow_amortized` for details. (The `A` parameter isn't significant, because the number
// of different `A` types seen in practice is much smaller than number of `T` types.)
fn finish_grow<A>(
    new_layout: Result<Layout, LayoutErr>,
    current_memory: Option<(NonNull<u8>, Layout)>,
    alloc: &mut A,
) -> Result<MemoryBlock, TryReserveError>
where
    A: AllocRef,
{
    // Check for the error here to minimize the size of `RawVec::grow_*`.
    let new_layout = new_layout.map_err(|_| CapacityOverflow)?;

    alloc_guard(new_layout.size())?;

    let memory = if let Some((ptr, old_layout)) = current_memory {
        debug_assert_eq!(old_layout.align(), new_layout.align());
        unsafe { alloc.grow(ptr, old_layout, new_layout.size(), MayMove, Uninitialized) }
    } else {
        alloc.alloc(new_layout, Uninitialized)
    }
    .map_err(|_| AllocError {
        layout: new_layout,
        non_exhaustive: (),
    })?;

    Ok(memory)
}

unsafe impl<#[may_dangle] T, A: AllocRef> Drop for RawVec<T, A> {
    /// Frees the memory owned by `RawVec` *without* trying to drop its contents.
    fn drop(&mut self) {
        if let Some((ptr, layout)) = self.current_memory() {
            unsafe { self.alloc.dealloc(ptr, layout) }
        }
    }
}

// We need to guarantee the following:
// * We don't ever allocate `> u32::MAX` byte-size objects.
// * We don't overflow `usize::MAX` and actually allocate too little.
#[inline]
fn alloc_guard(alloc_size: usize) -> Result<(), TryReserveError> {
    if alloc_size > u32::MAX as usize {
        Err(CapacityOverflow)
    } else {
        Ok(())
    }
}

// One central function responsible for repoting capacity overflows. This'll ensure that the code
// generation related to these panics is minimal as there's only one location which panics rather
// than a bunch throughout the module.
fn capacity_overflow() -> ! {
    panic!("capacity overflow");
}
