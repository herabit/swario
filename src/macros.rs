#![allow(unused_imports, unused_macro_rules, unused_macros)]

/// Define a SWAR type.
macro_rules! define {
    (
        $name:ident[$lane:ident; $count:tt] => $repr:ident {
            $($body:tt)*
        }
    ) => {
        #[doc = concat!("\
            A ", $crate::macros::bits!($repr), "-bit SIMD data type containing ",
            $count, " [`", stringify!($lane), "`]s.\
            "
        )]
        #[doc = ""]
        #[doc = "# Memory Layout"]
        #[doc = ""]
        #[doc = concat!("This type has the same memory layout as a [`", stringify!($repr), "`].")]
        #[derive(Clone, Copy, PartialEq, Eq, Default)]
        #[cfg_attr(
            feature = "bytemuck",
            derive(bytemuck::Zeroable, bytemuck::Pod, bytemuck::TransparentWrapper)
        )]
        #[cfg_attr(
            feature = "zerocopy",
            derive(
                zerocopy::FromBytes, zerocopy::Immutable,
                zerocopy::IntoBytes, zerocopy::KnownLayout,
            )
        )]
        #[repr(transparent)]
        pub struct $name(
            #[doc = "The underlying bit representation."]
            pub $repr,
        );

        // Ensure that the array of lanes is the same size as the SWAR type.
        const _: () = assert!(
            size_of::<[$lane; $count]>() == size_of::<$name>(),
            concat!(
                "\
                `[",
                stringify!($lane),
                "; ",
                $count,
                "]` must have the \
                same size as `",
                stringify!($name),
                "`.",
            ),
        );

        // Ensure that the swar type is adequately aligned.
        //
        // In virtually every platform it will be, but this exists to ensure
        // that we don't run into any degenerate platforms, just in case.
        const _: () = assert!(
            align_of::<$name>() >= align_of::<[$lane; $count]>(),
            concat!(
                "\
                `",
                stringify!($name),
                "` has a lower alignment than \
                [`",
                stringify!($lane),
                "; ",
                $count,
                "].\n\n\
                As such, this platform is considered a degenerate edge case, \
                and there are no plans to support it.",
            ),
        );

        impl $name {
            $crate::macros::common_consts!($name[$lane; $count] => $repr);
            $crate::uint_macros::uint_consts!($name[$lane; $count] => $repr { $($body)* });
            $crate::int_macros::int_consts!($name[$lane; $count] => $repr { $($body)* });
        }

        impl $name {
            $crate::macros::common_impl!($name[$lane; $count] => $repr);
            $crate::uint_macros::uint_impl!($name[$lane; $count] => $repr { $($body)* });
            $crate::int_macros::int_impl!($name[$lane; $count] => $repr { $($body)* });
        }
    };
}

pub(crate) use define;

/// Common SWAR impls.
#[rustfmt::skip]
macro_rules! common_impl {
    ($name:ident[$lane:ident; $count:tt] => $repr:ident) => {
        #[doc = concat!("\
            Create a new [`", stringify!($name), "`] from its \
            underlying bit representation ([`", stringify!($repr), "`]).",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn from_bits(bits: $repr) -> $name {
            $name(bits)
        }

        #[doc = concat!("\
            Create a reference to a [`", stringify!($name), "`] from a reference to \
            its underlying bit representation ([`", stringify!($repr), "`]).",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn from_bits_ref(bits: &$repr) -> &$name {
            // SAFETY: A SWAR vector is transparent over it's bit representation.
            unsafe { &*(bits as *const $repr as *const $name) }
        }

        #[doc = concat!("\
            Create a mutable reference to a [`", stringify!($name), "`] from a mutable reference to \
            its underlying bit representation ([`", stringify!($repr), "`]).",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn from_bits_mut(bits: &mut $repr) -> &mut $name {
            // SAFETY: A SWAR vector is transparent over it's bit representation.
            unsafe { &mut *(bits as *mut $repr as *mut $name) }
        }

        #[doc = concat!("\
            Get the underlying bit representation ([`", stringify!($repr), "`]) \
            of this [`", stringify!($name), "`].",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn to_bits(self) -> $repr {
            self.0
        }

        #[doc = concat!("\
            Get a reference to the underlying bit representation ([`", stringify!($repr), "`]) \
            of this [`", stringify!($name), "`].",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn as_bits(&self) -> &$repr {
            &self.0
        }

        #[doc = concat!("\
            Get a mutable reference to the underlying bit representation ([`", stringify!($repr), "`]) \
            of this [`", stringify!($name), "`].",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn as_bits_mut(&mut self) -> &mut $repr {
            &mut self.0
        }

        #[doc = concat!("\
            Create a new [`", stringify!($name), "`] \
            from an array of its lanes."
        )]
        #[inline(always)]
        #[must_use]
        pub const fn from_lanes(lanes: [$lane; $count]) -> $name {
            // SAFETY: A vector has the same memory layout as an array of its lanes.
            unsafe { core::mem::transmute(lanes) }
        }

        #[doc = concat!("\
            Get the underlying array of lanes \
            from this [`", stringify!($name), "`].",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn to_lanes(self) -> [$lane; $count] {
            // SAFETY: A vector has the same memory layout as an array of its lanes.
            unsafe { core::mem::transmute(self) }
        }

        #[doc = concat!("\
            Get a reference to the underlying array of \
            lanes from this [`", stringify!($name), "`].",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn as_lanes(&self) -> &[$lane; $count] {
            // SAFETY: A vector has the same memory layout as an array of its lanes,
            //         and we cause a compile time error if the lane type is somehow,
            //         of a higher alignment than the vector containing it.
            unsafe { &*(self as *const $name as *const [$lane; $count]) }
        }

        #[doc = concat!("\
            Get a mutable reference to the underlying array of \
            lanes from this [`", stringify!($name), "`].",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn as_lanes_mut(&mut self) -> &mut [$lane; $count] {
            // SAFETY: A vector has the same memory layout as an array of its lanes,
            //         and we cause a compile time error if the lane type is somehow,
            //         of a higher alignment than the vector containing it.
            unsafe { &mut *(self as *mut $name as *mut [$lane; $count]) }
        }

        #[doc = concat!("\
            Construct a new [`", stringify!($name), "`] with all lanes set to \
            the given value.",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn splat(value: $lane) -> $name {
            $name::from_lanes([value; $count])
        }

        #[doc = concat!("\
            Performs a bitwise NOT on each [`", stringify!($lane), "`].",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn not(self) -> $name {
            $name(!self.0)
        }

        #[doc = concat!("\
            Performs a bitwise AND on each [`", stringify!($name), "`].",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn and(self, rhs: $name) -> $name {
            $name(self.0 & rhs.0)
        }

        #[doc = concat!("\
            Performs a bitwise OR on each [`", stringify!($name), "`].",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn or(self, rhs: $name) -> $name {
            $name(self.0 | rhs.0)
        }

        #[doc = concat!("\
            Performs a bitwise XOR on each [`", stringify!($name), "`].",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn xor(self, rhs: $name) -> $name {
            $name(self.0 ^ rhs.0)
        }


        #[doc = concat!("\
            Rotates the vector by `n` lanes to the left."
        )]
        ///
        /// # Examples
        ///
        /// Basic example:
        ///
        /// ```
        /// use swario::*;
        ///
        #[doc = concat!("let before = ", stringify!($name), "::from_lanes(", $crate::macros::rotate_lanes_data!($count), ");")]
        #[doc = concat!("let after  = ", stringify!($name), "::from_lanes(", $crate::macros::rotate_lanes_data!($count left), ");")]
        /// 
        /// assert!(before.rotate_lanes_left(1) == after);
        #[inline(always)]
        #[must_use]
        pub const fn rotate_lanes_left(self, n: u32) -> $name {
            let n_bits = $lane::BITS * (n % $name::LANES);

            if cfg!(target_endian = "big") {
                $name(self.0.rotate_left(n_bits))
            } else {
                // NOTE: Little endian is ***weird***.
                $name(self.0.rotate_right(n_bits))
            }
        }

        

        #[doc = concat!("\
            Rotates the vector by `n` lanes to the right."
        )]
        ///
        /// # Examples
        ///
        /// Basic example:
        ///
        /// ```
        /// use swario::*;
        ///
        #[doc = concat!("let before = ", stringify!($name), "::from_lanes(", $crate::macros::rotate_lanes_data!($count), ");")]
        #[doc = concat!("let after  = ", stringify!($name), "::from_lanes(", $crate::macros::rotate_lanes_data!($count right), ");")]
        /// 
        /// assert!(before.rotate_lanes_right(1) == after);
        #[inline(always)]
        #[must_use]
        pub const fn rotate_lanes_right(self, n: u32) -> $name {
            let n_bits = $lane::BITS * (n % $name::LANES);

            if cfg!(target_endian = "big") {
                $name(self.0.rotate_right(n_bits))
            } else {
                // NOTE: Little endian is ***weird***.
                $name(self.0.rotate_left(n_bits))
            }
        }
    };
}

pub(crate) use common_impl;

/// Common constants for SWAR types.
#[rustfmt::skip]
macro_rules! common_consts {
    ($name:ident[$lane:ident; $count:tt] => $repr:ident) => {
        #[doc = concat!("The size of this vector in bits (", $crate::macros::bits!($repr), "-bit).")]
        ///
        /// # Examples
        ///
        /// Basic usage:
        /// 
        /// ```
        /// use swario::*;
        /// 
        #[doc = concat!("assert_eq!(", stringify!($name), "::BITS, ", $crate::macros::bits!($repr), ");")]
        /// ```
        pub const BITS: u32 = $repr::BITS;
        
        #[doc = concat!("The size of this vector's lanes in bits (", $crate::macros::bits!($lane), "-bit).")]
        ///
        /// # Examples
        ///
        /// Basic usage:
        /// 
        /// ```
        /// use swario::*;
        /// 
        #[doc = concat!("assert_eq!(", stringify!($name), "::LANE_BITS, ", $crate::macros::bits!($lane), ");")]
        /// ```
        pub const LANE_BITS: u32 = $lane::BITS;

        
        #[doc = concat!("The amount of lanes this vector contains (", $count, ").")]
        ///
        /// # Examples
        ///
        /// Basic usage:
        /// 
        /// ```
        /// use swario::*;
        /// 
        #[doc = concat!("assert_eq!(", stringify!($name), "::LANES, ", $count, ");")]
        /// ```
        pub const LANES: u32 = $count;

        #[doc = concat!("A [`", stringify!($name), "`] with all lanes set to [`", stringify!($lane), "::MAX`].")]
        ///
        /// # Examples
        ///
        /// Basic usage:
        /// 
        /// ```
        /// use swario::*;
        ///
        #[doc = concat!("assert_eq!(", stringify!($name), "::MAX.to_lanes(), [",  $crate::macros::max!($lane), "; ", $count, "]);")]
        /// ```
        pub const MAX: $name = $name::splat($lane::MAX);

        #[doc = concat!("A [`", stringify!($name), "`] with all lanes set to [`", stringify!($lane), "::MIN`].")]
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// use swario::*;
        /// 
        #[doc = concat!("assert_eq!(", stringify!($name), "::MIN.to_lanes(), [", $crate::macros::min!($lane), "; ", $count, "]);")]
        /// ```
        pub const MIN: $name = $name::splat($lane::MIN);


        #[doc = concat!("A [`", stringify!($name), "`] with all lanes set to their least significant bit.")]
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// use swario::*;
        /// 
        #[doc = concat!("assert_eq!(", stringify!($name), "::LSB.to_lanes(), [", $crate::macros::lsb!($lane), "; ", $count, "]);")]
        /// ```
        pub const LSB: $name = $name::splat(1 << 0);

        #[doc = concat!("A [`", stringify!($name), "`] with all lanes set to their most significant bit.")]
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// use swario::*;
        /// 
        #[doc = concat!("assert_eq!(", stringify!($name), "::MSB.to_lanes(), \
            [", $crate::macros::msb!($lane), $crate::macros::msb_cast!($lane),
            "; ", $count, "]);",
        )]
        /// ```
        #[allow(overflowing_literals)]
        pub const MSB: $name = $name::splat(1 << ($lane::BITS - 1));
    
        #[doc = concat!("A [`", stringify!($name), "`] with all lanes set to zero.")]
        ///
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// use swario::*;
        /// 
        #[doc = concat!("assert_eq!(", stringify!($name), "::ZERO.to_lanes(), [0; ", $count, "]);")]
        /// ```
        pub const ZERO: $name = $name::splat(0);

        #[doc = concat!("A [`", stringify!($name), "`] with all lanes set to one.")]
        /// # Examples
        ///
        /// Basic usage:
        ///
        /// ```
        /// use swario::*;
        /// 
        #[doc = concat!("assert_eq!(", stringify!($name), "::ONE.to_lanes(), [1; ", $count, "]);")]
        /// ```
        pub const ONE: $name = $name::splat(1);
    };
}

pub(crate) use common_consts;

/// Macro that creates macros for handling signedness.
#[rustfmt::skip]
macro_rules! define_signedness {
    ($(
        $unsigned:ident = $signed:ident
    ),+ $(,)?) => {
        /// Macro that inverts the signedness of a given type.
        macro_rules! invert_signedness {
            $(
                ($unsigned) => { $signed   };
                ($signed)   => { $unsigned };
            )*
        }

        pub(crate) use invert_signedness;

        /// Macro that gets the unsigned variant of a given type.
        macro_rules! unsigned {
            $(
                ($unsigned) => { $unsigned };
                ($signed)   => { $unsigned };
            )*
        }

        pub(crate) use unsigned;

        /// Macro that gets the signed variant of a given type.
        macro_rules! signed {
            $(
                ($signed) =>   { $signed   };
                ($unsigned) => { $unsigned };
            )*
        }

        pub(crate) use signed;
    };
}

define_signedness! {
    u8 = i8,
    U8x2 = I8x2,
    U8x4 = I8x4,
    U8x8 = I8x8,
    U8x16 = I8x16,

    u16 = i16,
    U16x2 = I16x2,
    U16x4 = I16x4,
    U16x8 = I16x8,

    u32 = i32,
    U32x2 = I32x2,
    U32x4 = I32x4,

    u64 = i64,
    U64x2 = I64x2,

    u128 = i128,
}

/// Macro that returns the width of a primitive.
#[rustfmt::skip]
macro_rules! bits {
    (u8) =>   {   8 };
    (u16) =>  {  16 };
    (u32) =>  {  32 };
    (u64) =>  {  64 };
    (u128) => { 128 };
    
    (i8) =>   {   8 };
    (i16) =>  {  16 };
    (i32) =>  {  32 };
    (i64) =>  {  64 };
    (i128) => { 128 };
}

pub(crate) use bits;

/// Macro that returns the width of a primitive decremented by one.
#[rustfmt::skip]
macro_rules! bits_dec {
    (u8) =>   {   7 };
    (u16) =>  {  15 };
    (u32) =>  {  31 };
    (u64) =>  {  63 };
    (u128) => { 127 };

    (i8) =>   {   7 };
    (i16) =>  {  15 };
    (i32) =>  {  31 };
    (i64) =>  {  63 };
    (i128) => { 127 };
 }

pub(crate) use bits_dec;

/// Macro that returns the minimum value of a primitive.
#[rustfmt::skip]
macro_rules! min {
    (u8) =>   { 0 };
    (u16) =>  { 0 };
    (u32) =>  { 0 };
    (u64) =>  { 0 };
    (u128) => { 0 };
    
    (i8) =>   {                                     -128 };
    (i16) =>  {                                   -32768 };
    (i32) =>  {                              -2147483648 };
    (i64) =>  {                     -9223372036854775808 };
    (i128) => { -170141183460469231731687303715884105728 };
}

pub(crate) use min;

/// Macro that returns the maximum value of a primitive.
#[rustfmt::skip]
macro_rules! max {
    (u8) =>   {                                     255 };
    (u16) =>  {                                   65535 };
    (u32) =>  {                              4294967295 };
    (u64) =>  {                    18446744073709551615 };
    (u128) => { 340282366920938463463374607431768211455 };
    
    (i8) =>   {                                     127 };
    (i16) =>  {                                   32767 };
    (i32) =>  {                              2147483647 };
    (i64) =>  {                     9223372036854775807 };
    (i128) => { 170141183460469231731687303715884105727 };
}

pub(crate) use max;

/// Macro that returns the cast needed for a MSB literal to ignore
/// the `overflowing_literals` error.
#[rustfmt::skip]
macro_rules! msb_cast {
    (i8) =>     {     "_u8 as i8" };
    (i16) =>    {   "_u16 as i16" };
    (i32) =>    {   "_u32 as i32" };
    (i64) =>    {   "_u64 as i64" };
    (i128) =>   { "_u128 as i128" };
    ($tt:tt) => {              "" };
}

pub(crate) use msb_cast;

/// Macro that returns a constant for a literal with the MSB set.
#[rustfmt::skip]
macro_rules! msb {
    (u8) =>   {                               "0x80" };
    (u16) =>  {                             "0x8000" };
    (u32) =>  {                         "0x80000000" };
    (u64) =>  {                 "0x8000000000000000" };
    (u128) => { "0x80000000000000000000000000000000" };

    (i8) =>   {                               "0x80" };
    (i16) =>  {                             "0x8000" };
    (i32) =>  {                         "0x80000000" };
    (i64) =>  {                 "0x8000000000000000" };
    (i128) => { "0x80000000000000000000000000000000" };
}

pub(crate) use msb;

/// Macro that returns a constant for a literal with the LSB set.
#[rustfmt::skip]
macro_rules! lsb {
    (u8)   => {                               "0x01" };
    (u16)  => {                             "0x0001" };
    (u32)  => {                         "0x00000001" };
    (u64)  => {                 "0x0000000000000001" };
    (u128) => { "0x00000000000000000000000000000001" };
    
    (i8)   => {                               "0x01" };
    (i16)  => {                             "0x0001" };
    (i32)  => {                         "0x00000001" };
    (i64)  => {                 "0x0000000000000001" };
    (i128) => { "0x00000000000000000000000000000001" };
}

pub(crate) use lsb;

/// Macro that returns test data for lane shifts.
#[rustfmt::skip]
macro_rules! rotate_lanes_data {
    (2)       => { "[0x00, 0x01]" };
    (2 right) => { "[0x01, 0x00]" };
    (2 left)  => { "[0x01, 0x00]" };
    
    (4)       => { "[0x00, 0x01, 0x02, 0x03]" };
    (4 right) => { "[0x03, 0x00, 0x01, 0x02]" };
    (4 left)  => { "[0x01, 0x02, 0x03, 0x00]" };
    
    (8)       => { "[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]" };
    (8 right) => { "[0x07, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06]" };
    (8 left)  => { "[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x00]" };
    
    (16)       => { "[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F]" };
    (16 right) => { "[0x0F, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E]" };
    (16 left)  => { "[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x00]" };
}

pub(crate) use rotate_lanes_data;
