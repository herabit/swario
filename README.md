# `::swario`

A small library for achieving SIMD within general purpose registers. This is particularly useful in restricted environments,
such as microcontrollers or a kernel, where accessing SIMD registers is just not feasible.

As such, this crate attempts to balance performance, with the size of codegen.

## What's to do.

- [ ] Implement thorough tests.
- [ ] Implement thorough benchmarks.
- [ ] Achieve parity with primitive methods.
- [ ] Publish to [crates.io](https://crates.io/).
