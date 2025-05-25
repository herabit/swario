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
