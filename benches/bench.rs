#![feature(test)]

extern crate test;

use std::iter::repeat;
use test::{black_box, Bencher};

#[bench]
fn bench_new(b: &mut Bencher) {
    b.iter(|| {
        let v: ve::Vec<u32> = black_box(ve::Vec::new());
        assert_eq!(v.len(), 0);
        assert_eq!(v.capacity(), 0);
    });
}

#[bench]
fn bench_new_std(b: &mut Bencher) {
    b.iter(|| {
        let v: Vec<u32> = black_box(Vec::new());
        assert_eq!(v.len(), 0);
        assert_eq!(v.capacity(), 0);
    });
}

fn do_bench_with_capacity(b: &mut Bencher, src_len: usize) {
    b.bytes = src_len as u64;

    b.iter(|| {
        let v: ve::Vec<u32> = black_box(ve::Vec::with_capacity(src_len));
        assert_eq!(v.len(), 0);
        assert_eq!(v.capacity(), src_len);
    });
}

fn do_bench_with_capacity_std(b: &mut Bencher, src_len: usize) {
    b.bytes = src_len as u64;

    b.iter(|| {
        let v: Vec<u32> = black_box(Vec::with_capacity(src_len));
        assert_eq!(v.len(), 0);
        assert_eq!(v.capacity(), src_len);
    });
}

#[bench]
fn bench_with_capacity_0000(b: &mut Bencher) {
    do_bench_with_capacity(b, 0)
}

#[bench]
fn bench_with_capacity_0000_std(b: &mut Bencher) {
    do_bench_with_capacity_std(b, 0)
}

#[bench]
fn bench_with_capacity_0010(b: &mut Bencher) {
    do_bench_with_capacity(b, 10)
}

#[bench]
fn bench_with_capacity_0010_std(b: &mut Bencher) {
    do_bench_with_capacity_std(b, 10)
}

#[bench]
fn bench_with_capacity_0100(b: &mut Bencher) {
    do_bench_with_capacity(b, 100)
}

#[bench]
fn bench_with_capacity_0100_std(b: &mut Bencher) {
    do_bench_with_capacity_std(b, 100)
}

#[bench]
fn bench_with_capacity_1000(b: &mut Bencher) {
    do_bench_with_capacity(b, 1000)
}
#[bench]
fn bench_with_capacity_1000_std(b: &mut Bencher) {
    do_bench_with_capacity_std(b, 1000)
}

fn do_bench_from_fn(b: &mut Bencher, src_len: usize) {
    b.bytes = src_len as u64;

    b.iter(|| {
        let dst = (0..src_len).collect::<Vec<_>>();
        assert_eq!(dst.len(), src_len);
        assert!(dst.iter().enumerate().all(|(i, x)| i == *x));
    })
}

fn do_bench_from_fn_std(b: &mut Bencher, src_len: usize) {
    b.bytes = src_len as u64;

    b.iter(|| {
        let dst = (0..src_len).collect::<ve::Vec<_>>();
        assert_eq!(dst.len(), src_len);
        assert!(dst.iter().enumerate().all(|(i, x)| i == *x));
    })
}

#[bench]
fn bench_from_fn_0000(b: &mut Bencher) {
    do_bench_from_fn(b, 0)
}

#[bench]
fn bench_from_fn_0010(b: &mut Bencher) {
    do_bench_from_fn(b, 10)
}

#[bench]
fn bench_from_fn_0100(b: &mut Bencher) {
    do_bench_from_fn(b, 100)
}

#[bench]
fn bench_from_fn_1000(b: &mut Bencher) {
    do_bench_from_fn(b, 1000)
}

// fn do_bench_from_elem(b: &mut Bencher, src_len: usize) {
//     b.bytes = src_len as u64;
//
//     b.iter(|| {
//         let dst: ve::Vec<usize> = repeat(5).take(src_len).collect();
//         assert_eq!(dst.len(), src_len);
//         assert!(dst.iter().all(|x| *x == 5));
//     })
// }
//
// #[bench]
// fn bench_from_elem_0000(b: &mut Bencher) {
//     do_bench_from_elem(b, 0)
// }
//
// #[bench]
// fn bench_from_elem_0010(b: &mut Bencher) {
//     do_bench_from_elem(b, 10)
// }
//
// #[bench]
// fn bench_from_elem_0100(b: &mut Bencher) {
//     do_bench_from_elem(b, 100)
// }
//
// #[bench]
// fn bench_from_elem_1000(b: &mut Bencher) {
//     do_bench_from_elem(b, 1000)
// }

#[bench]
fn do_bench_from_elem_u8(b: &mut Bencher) {
    b.bytes = 8 as u64;
    b.iter(|| {
        let dst = ve::vec![10_u8; 100];
        assert_eq!(dst.len(), 100);
        assert!(dst.iter().all(|x| *x == 10));
    })
}

#[bench]
fn do_bench_from_elem_i8(b: &mut Bencher) {
    b.bytes = 8 as u64;
    b.iter(|| {
        let dst = ve::vec![10_i8; 100];
        assert_eq!(dst.len(), 100);
        assert!(dst.iter().all(|x| *x == 10));
    })
}

fn do_bench_from_elem_std(b: &mut Bencher, src_len: usize) {
    b.bytes = src_len as u64;

    b.iter(|| {
        let dst: Vec<usize> = repeat(5).take(src_len).collect();
        assert_eq!(dst.len(), src_len);
        assert!(dst.iter().all(|x| *x == 5));
    })
}

#[bench]
fn bench_from_elem_0000_std(b: &mut Bencher) {
    do_bench_from_elem_std(b, 0)
}

#[bench]
fn bench_from_elem_0010_std(b: &mut Bencher) {
    do_bench_from_elem_std(b, 10)
}

#[bench]
fn bench_from_elem_0100_std(b: &mut Bencher) {
    do_bench_from_elem_std(b, 100)
}

#[bench]
fn bench_from_elem_1000_std(b: &mut Bencher) {
    do_bench_from_elem_std(b, 1000)
}
