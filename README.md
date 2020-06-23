ve
===

More compact version of `Vec`, uses 2 bytes/characters instead of 3. Currently
targeting only 64-bits machine and aim to be drop in replacement for `Vec`.

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

```
test bench_new                    ... bench:           7 ns/iter (+/- 0)
test bench_new_std                ... bench:           2 ns/iter (+/- 0)
test bench_with_capacity_0000     ... bench:           3 ns/iter (+/- 0)
test bench_with_capacity_0000_std ... bench:           3 ns/iter (+/- 0)
test bench_with_capacity_0010     ... bench:          17 ns/iter (+/- 1) = 588 MB/s
test bench_with_capacity_0010_std ... bench:          17 ns/iter (+/- 2) = 588 MB/s
test bench_with_capacity_0100     ... bench:          17 ns/iter (+/- 1) = 5882 MB/s
test bench_with_capacity_0100_std ... bench:          17 ns/iter (+/- 0) = 5882 MB/s
test bench_with_capacity_1000     ... bench:          54 ns/iter (+/- 1) = 18518 MB/s
test bench_with_capacity_1000_std ... bench:          54 ns/iter (+/- 0) = 18518 MB/s
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
