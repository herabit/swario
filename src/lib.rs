#![cfg_attr(not(test), no_std)]

pub(crate) mod macros;

pub(crate) mod int;
pub(crate) mod int_macros;

pub(crate) mod uint;
pub(crate) mod uint_macros;

pub(crate) mod util;

#[doc(inline)]
pub use uint::*;

#[doc(inline)]
pub use int::*;

#[test]
fn lol() {
    let lanes = [0xAA_u16, 0xBB, 0xCC, 0xDD];
    let test = U16x4::from_lanes(lanes).rotate_lanes_left(1);

    println!("{:?}", test.to_lanes());
}
