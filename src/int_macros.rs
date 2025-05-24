macro_rules! int_impl {
    ($name:ident[i8; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::int_macros::int_impl!(@actual $name[i8; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[i16; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::int_macros::int_impl!(@actual $name[i16; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[i32; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::int_macros::int_impl!(@actual $name[i32; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[i64; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::int_macros::int_impl!(@actual $name[i64; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[i128; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::int_macros::int_impl!(@actual $name[i128; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[isize; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::int_macros::int_impl!(@actual $name[isize; $count] => $repr {
            $($body)*
        });
    };

    (@actual $name:ident[$lane:ident; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {};

    ($($tt:tt)*) => {};
}

pub(crate) use int_impl;

macro_rules! int_consts {
    ($name:ident[i8; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::int_macros::int_consts!(@actual $name[i8; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[i16; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::int_macros::int_consts!(@actual $name[i16; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[i32; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::int_macros::int_consts!(@actual $name[i32; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[i64; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::int_macros::int_consts!(@actual $name[i64; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[i128; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::int_macros::int_consts!(@actual $name[i128; $count] => $repr {
            $($body)*
        });
    };


    ($name:ident[isize; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        $crate::int_macros::int_consts!(@actual $name[isize; $count] => $repr {
            $($body)*
        });
    };

    (@actual $name:ident[$lane:ident; $count:tt] => $repr:ident {
        $($body:tt)*
    }) => {
        #[doc = concat!("A [`", stringify!($name), "`] with all lanes set to negative one.")]
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// use swario::*;
        ///
        #[doc = concat!("assert_eq!(", stringify!($name), "::NEG_ONE.to_lanes(), [-1; ", $count, "]);")]
        /// ```
        pub const NEG_ONE: $name = $name::splat(-1);
    };

    ($($tt:tt)*) => {};
}

pub(crate) use int_consts;

// const _: () = assert!(i8::MIN == 0x80);
