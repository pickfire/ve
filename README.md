ve
===


[![Build Status](https://github.com/pickfire/ve/workflows/Continuous%20Integration/badge.svg?branch=master)](https://github.com/pickfire/ve/actions)
[![Documentation](https://docs.rs/ve/badge.svg)](https://docs.rs/ve)
[![Crates.io](https://img.shields.io/crates/v/ve.svg)](https://crates.io/crates/ve)

More compact version of `Vec`, uses 2 words instead of 3. Currently targetting
only 64-bits machine and aim to be drop in replacement for `Vec`.

This crate is work in progress, requires nightly and is highly experimental.
Porting is done by hand based on rust liballoc, `String` may be next target.

```rust
const WORD: usize = std::mem::size_of::<usize>();

assert_eq!(std::mem::size_of::<std::vec::Vec<u8>>(), 3 * WORD);
assert_eq!(std::mem::size_of::<ve::Vec<u8>>(), 2 * WORD);
```

## How does it work?

                     +-----------+-----------+-----------+
    std::vec::Vec    | Pointer   | Length    | Capacity  |
                     +-----------+-----------+-----------+

                     +-----------+-----------+
    ve::Vec          | Pointer   | Cap | Len |
                     +-----------+-----------+

`ve::Vec` have capacity of 4294967295 compared to `Vec` 18446744073709551615.
If you don't need that much digits, `ve::Vec` should be safe.

Inspired by <https://github.com/maciejhirsz/beef>.

## Benchmarks

Work in progress, so far creation time is slower.


running 0 tests

test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out

```
test bench_clone_0000                  ... bench:          17 ns/iter (+/- 9)
test bench_clone_0000_std              ... bench:          12 ns/iter (+/- 5)
test bench_clone_0010                  ... bench:          41 ns/iter (+/- 10) = 243 MB/s
test bench_clone_0010_std              ... bench:          29 ns/iter (+/- 1) = 344 MB/s
test bench_clone_0100                  ... bench:         119 ns/iter (+/- 5) = 840 MB/s
test bench_clone_0100_std              ... bench:         118 ns/iter (+/- 2) = 847 MB/s
test bench_clone_1000                  ... bench:         929 ns/iter (+/- 68) = 1076 MB/s
test bench_clone_1000_std              ... bench:         927 ns/iter (+/- 8) = 1078 MB/s
test bench_clone_from_01_0000_0000     ... bench:          23 ns/iter (+/- 0)
test bench_clone_from_01_0000_0000_std ... bench:          18 ns/iter (+/- 0)
test bench_clone_from_01_0000_0010     ... bench:          57 ns/iter (+/- 0) = 175 MB/s
test bench_clone_from_01_0000_0010_std ... bench:          43 ns/iter (+/- 0) = 232 MB/s
test bench_clone_from_01_0000_0100     ... bench:         149 ns/iter (+/- 1) = 671 MB/s
test bench_clone_from_01_0000_0100_std ... bench:         139 ns/iter (+/- 13) = 719 MB/s
test bench_clone_from_01_0000_1000     ... bench:       1,074 ns/iter (+/- 17) = 931 MB/s
test bench_clone_from_01_0000_1000_std ... bench:         980 ns/iter (+/- 23) = 1020 MB/s
test bench_clone_from_01_0010_0000     ... bench:          23 ns/iter (+/- 0)
test bench_clone_from_01_0010_0000_std ... bench:          18 ns/iter (+/- 1)
test bench_clone_from_01_0010_0010     ... bench:          57 ns/iter (+/- 0) = 175 MB/s
test bench_clone_from_01_0010_0010_std ... bench:          43 ns/iter (+/- 1) = 232 MB/s
test bench_clone_from_01_0010_0100     ... bench:         149 ns/iter (+/- 0) = 671 MB/s
test bench_clone_from_01_0010_0100_std ... bench:         139 ns/iter (+/- 1) = 719 MB/s
test bench_clone_from_01_0100_0010     ... bench:          57 ns/iter (+/- 3) = 175 MB/s
test bench_clone_from_01_0100_0010_std ... bench:          43 ns/iter (+/- 0) = 232 MB/s
test bench_clone_from_01_0100_0100     ... bench:         153 ns/iter (+/- 87) = 653 MB/s
test bench_clone_from_01_0100_0100_std ... bench:         139 ns/iter (+/- 0) = 719 MB/s
test bench_clone_from_01_0100_1000     ... bench:       1,072 ns/iter (+/- 17) = 932 MB/s
test bench_clone_from_01_0100_1000_std ... bench:         980 ns/iter (+/- 323) = 1020 MB/s
test bench_clone_from_01_1000_0100     ... bench:         149 ns/iter (+/- 2) = 671 MB/s
test bench_clone_from_01_1000_0100_std ... bench:         139 ns/iter (+/- 2) = 719 MB/s
test bench_clone_from_01_1000_1000     ... bench:       1,073 ns/iter (+/- 33) = 931 MB/s
test bench_clone_from_01_1000_1000_std ... bench:         978 ns/iter (+/- 7) = 1022 MB/s
test bench_clone_from_10_0000_0000     ... bench:         133 ns/iter (+/- 6)
test bench_clone_from_10_0000_0000_std ... bench:          84 ns/iter (+/- 1)
test bench_clone_from_10_0000_0010     ... bench:         345 ns/iter (+/- 6) = 289 MB/s
test bench_clone_from_10_0000_0010_std ... bench:         225 ns/iter (+/- 10) = 444 MB/s
test bench_clone_from_10_0000_0100     ... bench:       1,114 ns/iter (+/- 23) = 897 MB/s
test bench_clone_from_10_0000_0100_std ... bench:       1,046 ns/iter (+/- 22) = 956 MB/s
test bench_clone_from_10_0000_1000     ... bench:       8,589 ns/iter (+/- 223) = 1164 MB/s
test bench_clone_from_10_0000_1000_std ... bench:       8,029 ns/iter (+/- 208) = 1245 MB/s
test bench_clone_from_10_0010_0000     ... bench:         134 ns/iter (+/- 9)
test bench_clone_from_10_0010_0000_std ... bench:          85 ns/iter (+/- 2)
test bench_clone_from_10_0010_0010     ... bench:         346 ns/iter (+/- 58) = 289 MB/s
test bench_clone_from_10_0010_0010_std ... bench:         223 ns/iter (+/- 13) = 448 MB/s
test bench_clone_from_10_0010_0100     ... bench:       1,114 ns/iter (+/- 23) = 897 MB/s
test bench_clone_from_10_0010_0100_std ... bench:       1,046 ns/iter (+/- 23) = 956 MB/s
test bench_clone_from_10_0100_0010     ... bench:         344 ns/iter (+/- 6) = 290 MB/s
test bench_clone_from_10_0100_0010_std ... bench:         225 ns/iter (+/- 22) = 444 MB/s
test bench_clone_from_10_0100_0100     ... bench:       1,113 ns/iter (+/- 21) = 898 MB/s
test bench_clone_from_10_0100_0100_std ... bench:       1,046 ns/iter (+/- 20) = 956 MB/s
test bench_clone_from_10_0100_1000     ... bench:       8,616 ns/iter (+/- 242) = 1160 MB/s
test bench_clone_from_10_0100_1000_std ... bench:       8,030 ns/iter (+/- 414) = 1245 MB/s
test bench_clone_from_10_1000_0100     ... bench:       1,115 ns/iter (+/- 19) = 896 MB/s
test bench_clone_from_10_1000_0100_std ... bench:       1,046 ns/iter (+/- 21) = 956 MB/s
test bench_clone_from_10_1000_1000     ... bench:       8,587 ns/iter (+/- 373) = 1164 MB/s
test bench_clone_from_10_1000_1000_std ... bench:       8,012 ns/iter (+/- 146) = 1248 MB/s
test bench_extend_0000_0000            ... bench:          26 ns/iter (+/- 0)
test bench_extend_0000_0000_std        ... bench:          25 ns/iter (+/- 0)
test bench_extend_0000_0010            ... bench:          83 ns/iter (+/- 2) = 120 MB/s
test bench_extend_0000_0010_std        ... bench:          65 ns/iter (+/- 1) = 153 MB/s
test bench_extend_0000_0100            ... bench:         178 ns/iter (+/- 4) = 561 MB/s
test bench_extend_0000_0100_std        ... bench:         168 ns/iter (+/- 4) = 595 MB/s
test bench_extend_0000_1000            ... bench:       1,164 ns/iter (+/- 32) = 859 MB/s
test bench_extend_0000_1000_std        ... bench:       1,170 ns/iter (+/- 73) = 854 MB/s
test bench_extend_0010_0010            ... bench:         171 ns/iter (+/- 3) = 58 MB/s
test bench_extend_0010_0010_std        ... bench:         151 ns/iter (+/- 14) = 66 MB/s
test bench_extend_0100_0100            ... bench:         370 ns/iter (+/- 9) = 270 MB/s
test bench_extend_0100_0100_std        ... bench:         350 ns/iter (+/- 9) = 285 MB/s
test bench_extend_1000_1000            ... bench:       2,920 ns/iter (+/- 75) = 342 MB/s
test bench_extend_1000_1000_std        ... bench:       3,015 ns/iter (+/- 134) = 331 MB/s
test bench_from_elem_0000              ... bench:           5 ns/iter (+/- 0)
test bench_from_elem_0000_std          ... bench:           4 ns/iter (+/- 0)
test bench_from_elem_0010              ... bench:          35 ns/iter (+/- 0) = 285 MB/s
test bench_from_elem_0010_std          ... bench:          32 ns/iter (+/- 1) = 312 MB/s
test bench_from_elem_0100              ... bench:         111 ns/iter (+/- 2) = 900 MB/s
test bench_from_elem_0100_std          ... bench:         111 ns/iter (+/- 2) = 900 MB/s
test bench_from_elem_1000              ... bench:         798 ns/iter (+/- 33) = 1253 MB/s
test bench_from_elem_1000_std          ... bench:         795 ns/iter (+/- 16) = 1257 MB/s
test bench_from_fn_0000                ... bench:           5 ns/iter (+/- 0)
test bench_from_fn_0000_std            ... bench:           5 ns/iter (+/- 0)
test bench_from_fn_0010                ... bench:          33 ns/iter (+/- 0) = 303 MB/s
test bench_from_fn_0010_std            ... bench:          33 ns/iter (+/- 0) = 303 MB/s
test bench_from_fn_0100                ... bench:         121 ns/iter (+/- 2) = 826 MB/s
test bench_from_fn_0100_std            ... bench:         119 ns/iter (+/- 3) = 840 MB/s
test bench_from_fn_1000                ... bench:         948 ns/iter (+/- 23) = 1054 MB/s
test bench_from_fn_1000_std            ... bench:         951 ns/iter (+/- 18) = 1051 MB/s
test bench_from_iter_0000              ... bench:          18 ns/iter (+/- 0)
test bench_from_iter_0000_std          ... bench:          12 ns/iter (+/- 0)
test bench_from_iter_0010              ... bench:          72 ns/iter (+/- 1) = 138 MB/s
test bench_from_iter_0010_std          ... bench:          34 ns/iter (+/- 2) = 294 MB/s
test bench_from_iter_0100              ... bench:         172 ns/iter (+/- 4) = 581 MB/s
test bench_from_iter_0100_std          ... bench:         124 ns/iter (+/- 4) = 806 MB/s
test bench_from_iter_1000              ... bench:       1,168 ns/iter (+/- 70) = 856 MB/s
test bench_from_iter_1000_std          ... bench:         955 ns/iter (+/- 20) = 1047 MB/s
test bench_from_slice_0000             ... bench:          18 ns/iter (+/- 0)
test bench_from_slice_0000_std         ... bench:          17 ns/iter (+/- 0)
test bench_from_slice_0010             ... bench:          53 ns/iter (+/- 2) = 188 MB/s
test bench_from_slice_0010_std         ... bench:          51 ns/iter (+/- 1) = 196 MB/s
test bench_from_slice_0100             ... bench:         163 ns/iter (+/- 4) = 613 MB/s
test bench_from_slice_0100_std         ... bench:         153 ns/iter (+/- 5) = 653 MB/s
test bench_from_slice_1000             ... bench:       1,170 ns/iter (+/- 25) = 854 MB/s
test bench_from_slice_1000_std         ... bench:       1,192 ns/iter (+/- 188) = 838 MB/s
test bench_new                         ... bench:           7 ns/iter (+/- 0)
test bench_new_std                     ... bench:           2 ns/iter (+/- 0)
test bench_push_all_0000_0000          ... bench:          17 ns/iter (+/- 1)
test bench_push_all_0000_0000_std      ... bench:          15 ns/iter (+/- 0)
test bench_push_all_0000_0010          ... bench:          43 ns/iter (+/- 1) = 232 MB/s
test bench_push_all_0000_0010_std      ... bench:          41 ns/iter (+/- 1) = 243 MB/s
test bench_push_all_0000_0100          ... bench:         130 ns/iter (+/- 3) = 769 MB/s
test bench_push_all_0000_0100_std      ... bench:         129 ns/iter (+/- 3) = 775 MB/s
test bench_push_all_0000_1000          ... bench:         957 ns/iter (+/- 27) = 1044 MB/s
test bench_push_all_0000_1000_std      ... bench:         956 ns/iter (+/- 35) = 1046 MB/s
test bench_push_all_0010_0010          ... bench:         116 ns/iter (+/- 2) = 86 MB/s
test bench_push_all_0010_0010_std      ... bench:         114 ns/iter (+/- 3) = 87 MB/s
test bench_push_all_0100_0100          ... bench:         292 ns/iter (+/- 5) = 342 MB/s
test bench_push_all_0100_0100_std      ... bench:         287 ns/iter (+/- 6) = 348 MB/s
test bench_push_all_1000_1000          ... bench:       1,926 ns/iter (+/- 60) = 519 MB/s
test bench_push_all_1000_1000_std      ... bench:       1,923 ns/iter (+/- 42) = 520 MB/s
test bench_push_all_move_0000_0000     ... bench:          26 ns/iter (+/- 5)
test bench_push_all_move_0000_0000_std ... bench:          25 ns/iter (+/- 2)
test bench_push_all_move_0000_0010     ... bench:          70 ns/iter (+/- 3) = 142 MB/s
test bench_push_all_move_0000_0010_std ... bench:          65 ns/iter (+/- 4) = 153 MB/s
test bench_push_all_move_0000_0100     ... bench:         164 ns/iter (+/- 5) = 609 MB/s
test bench_push_all_move_0000_0100_std ... bench:         175 ns/iter (+/- 3) = 571 MB/s
test bench_push_all_move_0000_1000     ... bench:       1,165 ns/iter (+/- 25) = 858 MB/s
test bench_push_all_move_0000_1000_std ... bench:       1,182 ns/iter (+/- 24) = 846 MB/s
test bench_push_all_move_0010_0010     ... bench:         144 ns/iter (+/- 3) = 69 MB/s
test bench_push_all_move_0010_0010_std ... bench:         134 ns/iter (+/- 10) = 74 MB/s
test bench_push_all_move_0100_0100     ... bench:         335 ns/iter (+/- 10) = 298 MB/s
test bench_push_all_move_0100_0100_std ... bench:         331 ns/iter (+/- 8) = 302 MB/s
test bench_push_all_move_1000_1000     ... bench:       2,906 ns/iter (+/- 60) = 344 MB/s
test bench_push_all_move_1000_1000_std ... bench:       2,975 ns/iter (+/- 85) = 336 MB/s
test bench_with_capacity_0000          ... bench:           3 ns/iter (+/- 0)
test bench_with_capacity_0000_std      ... bench:           3 ns/iter (+/- 0)
test bench_with_capacity_0010          ... bench:          17 ns/iter (+/- 1) = 588 MB/s
test bench_with_capacity_0010_std      ... bench:          30 ns/iter (+/- 0) = 333 MB/s
test bench_with_capacity_0100          ... bench:          17 ns/iter (+/- 0) = 5882 MB/s
test bench_with_capacity_0100_std      ... bench:          30 ns/iter (+/- 1) = 3333 MB/s
test bench_with_capacity_1000          ... bench:          38 ns/iter (+/- 5) = 26315 MB/s
test bench_with_capacity_1000_std      ... bench:          39 ns/iter (+/- 0) = 25641 MB/s
```

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
