use std::mem::size_of;
use ve::Vec;

#[test]
fn test_small_vec_struct() {
    assert_eq!(size_of::<Vec<u8>>(), size_of::<usize>() * 2);
}
