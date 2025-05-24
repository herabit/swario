#![allow(dead_code)]

/// This macro calls the actual uint implementation macro if the lane type is unsigned.
macro_rules! uint_impl {
    ($name:ident[u8; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::uint_macros::uint_impl!(@actual $name[u8; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[u16; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::uint_macros::uint_impl!(@actual $name[u16; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[u32; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::uint_macros::uint_impl!(@actual $name[u32; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[u64; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::uint_macros::uint_impl!(@actual $name[u64; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[u128; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::uint_macros::uint_impl!(@actual $name[u128; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[usize; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::uint_macros::uint_impl!(@actual $name[usize; $count] => $repr {
            $($body)*
        });
    };

    (@actual $name:ident[$lane:ident; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {

    };

    ($($tt:tt)*) => {};
}

pub(crate) use uint_impl;

macro_rules! uint_consts {
    ($name:ident[u8; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::uint_macros::uint_consts!(@actual $name[u8; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[u16; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::uint_macros::uint_consts!(@actual $name[u16; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[u32; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::uint_macros::uint_consts!(@actual $name[u32; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[u64; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::uint_macros::uint_consts!(@actual $name[u64; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[u128; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::uint_macros::uint_consts!(@actual $name[u128; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[usize; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::uint_macros::uint_consts!(@actual $name[usize; $count] => $repr {
            $($body)*
        });
    };

    (@actual $name:ident[$lane:ident; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {

    };

    ($($tt:tt)*) => {};
}

pub(crate) use uint_consts;
