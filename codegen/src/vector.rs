use core::fmt;
use std::{iter, num::NonZero};

use anyhow::Context;
use indoc::{formatdoc, writedoc};

use crate::scalar::{Scalar, Unsigned};

#[derive(Debug, Clone, Copy)]
pub struct Vector {
    pub scalar: Scalar,
    pub lanes: NonZero<u32>,
    pub repr: Unsigned,
    pub name: &'static str,
}

impl Vector {
    pub fn new(scalar: Scalar, lanes: NonZero<u32>) -> anyhow::Result<Self> {
        let width = scalar
            .width()
            .context("cannot generate vector for ptr sized scalar")?;
        let repr_width = width.checked_mul(lanes).context("too many lanes")?;
        let repr = Unsigned::from_width(repr_width.get()).context("unsupported vector size")?;
        let name = String::leak(format!("{}x{lanes}", scalar.pascal_name()));

        Ok(Self {
            scalar,
            lanes,
            repr,
            name,
        })
    }

    /// Write all of the definitions and imples for this type.
    pub fn write_all(&self, out: &mut dyn fmt::Write) -> anyhow::Result<()> {
        self.define(out)?;
        self.consts(out)?;
        self.base(out)?;
        self.rotate_lanes(out)?;
        self.shift_lanes(out)?;
        self.bitwise(out)?;
        self.shift(out)?;

        Ok(())
    }

    /// Create a type definition for this vector type.
    pub fn define(&self, out: &mut dyn fmt::Write) -> anyhow::Result<()> {
        let Self {
            scalar,
            lanes,
            repr,
            name,
        } = self;

        let width = repr.width().context("invalid repr")?;
        let unaligned = if width.get() == 8 {
            ", ::zerocopy::Unaligned"
        } else {
            ""
        };

        writedoc!(
            out,
            "
                /// A {width}-bit SWAR vector containing {lanes} [`{scalar}`]s.
                /// 
                ///
                /// # Memory Layout
                ///
                /// This type is a transparent wrapper over a [`{repr}`], but is
                /// treated as a `[{scalar}; {lanes}]`.
                #[derive(Clone, Copy, PartialEq, Eq, Default)]
                #[cfg_attr(\
                    feature = \"bytemuck\", \
                    derive(\
                        ::bytemuck::Zeroable, \
                        ::bytemuck::Pod, \
                        ::bytemuck::TransparentWrapper\
                    )\
                )]
                #[cfg_attr(\
                    feature = \"zerocopy\", \
                    derive(\
                    ::zerocopy::FromBytes, \
                    ::zerocopy::IntoBytes, \
                    ::zerocopy::KnownLayout, \
                    ::zerocopy::Immutable\
                    {unaligned}\
                    )\
                )]
                #[repr(transparent)]
                pub struct {name}(
                    /// The underlying bit representation.
                    ///
                    /// If possible, one should avoid using this field directly.
                    ///
                    /// See the endianness section for more info.
                    ///
                    /// # Endianness
                    ///
                    /// This matters because depending on this target's endianness,
                    /// if you want to directly manipulate the lanes themselves using
                    /// bit shifts or rotations, which direction you need to go in
                    /// depends on endianness.
                    ///
                    /// Big Endian platforms, well, they work as you'd expect. If you want
                    /// to rotate the lanes themselves to the right, you use a rightwards
                    /// bit shift. Leftwards, you shift left.
                    ///
                    /// Little Endian platforms, which represent the overwhelming majority
                    /// of modern day computing platforms, it's inverted. If you want to rotate
                    /// the lanes leftwards, you need to do so with a rotate right.
                    ///
                    /// This does not affect operations that are lanewise (they operate on lanes
                    /// individually). It instead affects operations that are ***swizzles***,
                    /// where instead of operating on lanes, they move where lanes are, not
                    /// affecting the a given lane's value, just where it is.
                    ///
                    /// ***TODO*** rewrite the above documentation.
                    pub {repr},  
                );

                // We need to ensure that `{name}` is the same size as `[{scalar}; {lanes}]`.
                const _: () = {{
                    let vec = ::core::mem::size_of::<{name}>();
                    let lanes = ::core::mem::size_of::<[{scalar}; {lanes}]>();

                    ::core::assert!(vec == lanes, \"\
                        the size of `{name}` must be equal to that of `[{scalar}; {lanes}]`\
                    \");
                }};

                // We need to ensure that `{name}` is sufficiently aligned for `[{scalar}; {lanes}]`.
                //
                // It almost certainly is, however it's still good to catch platforms that, for whatever
                // reason decided to do the insane.
                const _: () = {{
                    let vec = ::core::mem::align_of::<{name}>();
                    let lanes = ::core::mem::align_of::<[{scalar}; {lanes}]>();

                    ::core::assert!(vec >= lanes, \"\
                        the alignment of `{name}` is not sufficiently aligned for `[{scalar}; {lanes}]`.\\n\\n\
                        \
                        This indicates that the platform you're trying to compile for is esoteric to the point \
                        that it is simply just not worth supporting.\
                    \");
                }};

                impl ::core::fmt::Debug for {name} {{
                    #[inline]
                    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {{
                        self.as_array().fmt(f)
                    }}
                }}

            ",
        )?;

        Ok(())
    }

    /// Define the associated constants.
    pub fn consts(&self, out: &mut dyn fmt::Write) -> anyhow::Result<()> {
        let Self {
            scalar,
            lanes,
            repr,
            name,
        } = self;

        let repr_bits = repr.width().unwrap();
        let scalar_bits = scalar.width().unwrap();
        let min = Scalar::min(*scalar).unwrap();
        let max = Scalar::max(*scalar).unwrap();

        let lsb = {
            let nibbles = (0..scalar_bits.get() / 4)
                .map(|n| n == 0)
                .map(|is_lsb| if is_lsb { "1" } else { "0" })
                .rev();

            iter::once("0x")
                .chain(nibbles)
                .chain(["_", scalar.name()])
                .collect::<String>()
        };

        let msb = {
            let nibbles = (0..scalar_bits.get() / 4)
                .map(|n| n == 0)
                .map(|is_msb| if is_msb { "8" } else { "0" });

            let cast = [" as ", scalar.name()]
                .into_iter()
                .skip(if scalar.is_signed() { 0 } else { 2 });

            iter::once("0x")
                .chain(nibbles)
                .chain(["_", scalar.unsigned().name()])
                .chain(cast)
                .collect::<String>()
        };

        let neg_one = if scalar.is_signed() {
            Some(formatdoc!(
                "
                    /// A [`{name}`] with all lanes set to negative one.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::NEG_ONE, {name}::splat(-1));
                    /// 
                    /// ```
                    pub const NEG_ONE: {name} = {name}::splat(-1);

                "
            ))
        } else {
            None
        };

        let neg_one = neg_one.as_deref().unwrap_or("");

        writedoc!(
            out,
            "
                impl {name} {{
                    /// The size of this vector in bits ({repr_bits}-bit).
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::BITS, {repr}::BITS);
                    /// assert_eq!({name}::BITS, {repr_bits});
                    /// 
                    /// ```
                    pub const BITS: u32 = {repr}::BITS;

                    /// The size of this vector's lanes in bits ({scalar_bits}-bit).
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::LANE_BITS, {scalar}::BITS);
                    /// assert_eq!({name}::LANE_BITS, {scalar_bits});
                    /// 
                    /// ```
                    pub const LANE_BITS: u32 = {scalar}::BITS;

                    /// The amount of [`{scalar}`] lanes ({lanes}) this vector contains.
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::LANES, {lanes});
                    /// assert_eq!({name}::LANES, size_of::<{name}>() / size_of::<{scalar}>());
                    ///
                    /// ```
                    pub const LANES: usize = {lanes};

                    /// A [`{name}`] with all lanes set to [`{scalar}::MAX`].
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::MAX, {name}::splat({max}));
                    /// 
                    /// ```
                    pub const MAX: {name} = {name}::splat({scalar}::MAX);

                    /// A [`{name}`] with all lanes set to [`{scalar}::MIN`].
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::MIN, {name}::splat({min}));
                    /// 
                    /// ```
                    pub const MIN: {name} = {name}::splat({scalar}::MIN);

                    /// A [`{name}`] with all lanes set to their least significant bit.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::LSB, {name}::splat({lsb}));
                    ///
                    /// ```
                    pub const LSB: {name} = {name}::splat(1 << 0);

                    /// A [`{name}`] with all lanes set to their most significant bit.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::MSB, {name}::splat({msb}));
                    ///
                    /// ```
                    pub const MSB: {name} = {name}::splat(1 << ({scalar}::BITS - 1));

                    /// A [`{name}`] with all lanes set to zero.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::ZERO, {name}::splat(0));
                    /// 
                    /// ```
                    pub const ZERO: {name} = {name}::splat(0);

                    /// A [`{name}`] with all lanes set to one.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::ONE, {name}::splat(1));
                    /// 
                    /// ```
                    pub const ONE: {name} = {name}::splat(1);

                    {neg_one}
                }}
            "
        )?;

        Ok(())
    }

    /// Define the base functionality.
    pub fn base(&self, out: &mut dyn fmt::Write) -> anyhow::Result<()> {
        let Self {
            scalar,
            lanes,
            repr,
            name,
        } = self;

        let args = (0..lanes.get())
            .into_iter()
            .map(|lane| format!("{}: {scalar}", (b'a' + lane as u8) as char))
            .collect::<Vec<_>>()
            .join(", ");
        let arr = (0..lanes.get())
            .into_iter()
            .map(|lane| String::from((b'a' + lane as u8) as char))
            .collect::<Vec<_>>()
            .join(", ");

        writedoc!(
            out,
            "
                impl {name} {{
                    /// Create a new [`{name}`] from an array of {lanes} [`{scalar}`]s.
                    #[inline(always)]
                    #[must_use]
                    pub const fn from_array(arr: [{scalar}; {lanes}]) -> {name} {{
                        // SAFETY: We know that `{name}` and `[{scalar}; {lanes}]` are POD,
                        //         and have the same size.
                        unsafe {{ ::core::mem::transmute(arr) }}
                    }}
                    
                    /// Get a reference to the underlying lanes as an array.
                    #[inline(always)]
                    #[must_use]
                    pub const fn as_array(&self) -> &[{scalar}; {lanes}] {{
                        // SAFETY: `{name}` and `[{scalar}; {lanes}]` are POD,
                        //         and have the same size, and we cause a
                        //         compile-time error if `{name}` is not sufficiently
                        //         aligned, somehow.
                        unsafe {{ &*(self as *const {name} as *const [{scalar}; {lanes}]) }}
                    }}

                    /// Get a mutable reference to the underlying lanes as an array.
                    #[inline(always)]
                    #[must_use]
                    pub const fn as_array_mut(&mut self) -> &mut [{scalar}; {lanes}] {{
                        // SAFETY: `{name}` and `[{scalar}; {lanes}]` are POD,
                        //         and have the same size, and we cause a
                        //         compile-time error if `{name}` is not sufficiently
                        //         aligned, somehow.
                        unsafe {{ &mut *(self as *mut {name} as *mut [{scalar}; {lanes}]) }}
                    }}

                    /// Get the underlying lanes as an array.
                    #[inline(always)]
                    #[must_use]
                    pub const fn to_array(self) -> [{scalar}; {lanes}] {{
                        // SAFETY: We know that `{name}` and `[{scalar}; {lanes}]` are POD,
                        //         and have the same size.
                        unsafe {{ ::core::mem::transmute(self) }}
                    }}

                    /// Create a new [`{name}`] with all {lanes} lanes set to `value`.
                    #[inline(always)]
                    #[must_use]
                    pub const fn splat(value: {scalar}) -> {name} {{
                        {name}::from_array([value; {lanes}])
                    }}

                    /// Create a new [`{name}`] from its [`{scalar}`] lanes.
                    #[inline(always)]
                    #[must_use]
                    pub const fn new({args}) -> {name} {{
                        {name}::from_array([{arr}])
                    }}

                    /// Create a new [`{name}`] from its underlying bit representation.
                    #[inline(always)]
                    #[must_use]
                    pub const fn from_bits(bits: {repr}) -> {name} {{
                        {name}(bits)
                    }}

                    /// Create a reference to a [`{name}`] from a reference to its underlying
                    /// bit representation.
                    #[inline(always)]
                    #[must_use]
                    pub const fn from_bits_ref(bits: &{repr}) -> &{name} {{
                        // SAFETY: `{name}` is a transparent wrapper over `{repr}`,
                        //         so this is always safe.
                        unsafe {{ &*(bits as *const {repr} as *const {name}) }}
                    }}

                    /// Create a mutable reference to a [`{name}`] from a mutable reference to its
                    /// underlying bit representation.
                    #[inline(always)]
                    #[must_use]
                    pub const fn from_bits_mut(bits: &mut {repr}) -> &mut {name} {{
                        // SAFETY: `{name}` is a transparent wrapper over `{repr}`,
                        //         so this is always safe.
                        unsafe {{ &mut *(bits as *mut {repr} as *mut {name}) }}
                    }}

                    /// Get a reference to the underlying bit representation.
                    #[inline(always)]
                    #[must_use]
                    pub const fn as_bits(&self) -> &{repr} {{
                        &self.0
                    }}

                    /// Get a mutable reference to the underlying bit representation.
                    #[inline(always)]
                    #[must_use]
                    pub const fn as_bits_mut(&mut self) -> &mut {repr} {{
                        &mut self.0
                    }}

                    /// Get the underlying bit representation.
                    #[inline(always)]
                    #[must_use]
                    pub const fn to_bits(self) -> {repr} {{
                        self.0
                    }}
                }}
            "
        )?;

        Ok(())
    }

    /// Add lane rotations.
    pub fn rotate_lanes(&self, out: &mut dyn fmt::Write) -> anyhow::Result<()> {
        let Self {
            scalar,
            lanes,
            name,
            ..
        } = self;

        let mut data = (0..lanes.get())
            .map(|l| format!("{l:#04X}"))
            .collect::<Vec<_>>();

        let base = data.join(", ");

        let right = {
            data.rotate_right(1);

            let right = data.join(", ");
            data.rotate_left(1);

            right
        };

        let left = {
            data.rotate_left(1);

            let left = data.join(", ");
            data.rotate_right(1);

            left
        };

        writedoc!(
            out,
            "
                impl {name} {{
                    /// Rotates the vector by `n` lanes to the right.
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// let before = {name}::from_array([{base}]);
                    /// let after = {name}::from_array([{right}]);
                    ///
                    /// assert_eq!(before.rotate_lanes_right(1), after);
                    ///
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn rotate_lanes_right(self, n: u32) -> {name} {{
                        let n_bits = {scalar}::BITS * (n % {name}::LANES as u32);

                        if ::core::cfg!(target_endian = \"big\") {{
                            {name}(self.0.rotate_right(n_bits))
                        }} else {{
                            // NOTE: Little endian is weird.
                            {name}(self.0.rotate_left(n_bits))
                        }}
                    }}

                    /// Rotates the vector by `n` lanes to the left.
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// let before = {name}::from_array([{base}]);
                    /// let after = {name}::from_array([{left}]);
                    ///
                    /// assert_eq!(before.rotate_lanes_left(1), after);
                    ///
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn rotate_lanes_left(self, n: u32) -> {name} {{
                        let n_bits = {scalar}::BITS * (n % {name}::LANES as u32);

                        if ::core::cfg!(target_endian = \"big\") {{
                            {name}(self.0.rotate_left(n_bits))
                        }} else {{
                            // NOTE: Little endian is weird.
                            {name}(self.0.rotate_right(n_bits))
                        }}
                    }}
                }}
            "
        )?;

        Ok(())
    }

    /// Add lane shifts.
    pub fn shift_lanes(&self, out: &mut dyn fmt::Write) -> anyhow::Result<()> {
        let Self {
            scalar,
            lanes,
            name,
            ..
        } = self;

        let shift = lanes.get() / 2;

        let base = (0..shift)
            .map(|_| "0x0A")
            .chain((0..shift).map(|_| "0x0B"))
            .collect::<Vec<_>>()
            .join(", ");

        let right = (0..shift)
            .map(|_| "0x00")
            .chain((0..shift).map(|_| "0x0A"))
            .collect::<Vec<_>>()
            .join(", ");

        let left = (0..shift)
            .map(|_| "0x0B")
            .chain((0..shift).map(|_| "0x00"))
            .collect::<Vec<_>>()
            .join(", ");

        writedoc!(
            out,
            "
                impl {name} {{
                    /// Shifts the vector by `n` lanes to the right.
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// let before = {name}::from_array([{base}]);
                    /// let after = {name}::from_array([{right}]);
                    ///
                    /// assert_eq!(before.shift_lanes_right({shift}), after);
                    ///
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn shift_lanes_right(self, n: u32) -> {name} {{
                        let n_bits = {scalar}::BITS * (n % {name}::LANES as u32);

                        if ::core::cfg!(target_endian = \"big\") {{
                            {name}(self.0 >> n_bits)
                        }} else {{
                            // NOTE: Little endian is weird.
                            {name}(self.0 << n_bits)
                        }}
                    }}

                    /// Shifts the vector by `n` lanes to the left.
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// let before = {name}::from_array([{base}]);
                    /// let after = {name}::from_array([{left}]);
                    ///
                    /// assert_eq!(before.shift_lanes_left({shift}), after);
                    ///
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn shift_lanes_left(self, n: u32) -> {name} {{
                        let n_bits = {scalar}::BITS * (n % {name}::LANES as u32);

                        if ::core::cfg!(target_endian = \"big\") {{
                            {name}(self.0 << n_bits)
                        }} else {{
                            // NOTE: Little endian is weird.
                            {name}(self.0 >> n_bits)
                        }}
                    }}
                }}
            "
        )?;

        Ok(())
    }

    /// Implements bitwise operations.
    pub fn bitwise(&self, out: &mut dyn fmt::Write) -> anyhow::Result<()> {
        let Self {
            scalar,
            // lanes,
            // repr,
            name,
            ..
        } = self;

        writedoc!(
            out,
            "
                impl {name} {{
                    /// Performs a bitwise NOT on each [`{scalar}`] lane.
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::splat(0x00).not(), {name}::splat(!0x00));
                    /// 
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn not(self) -> {name} {{
                        {name}(!self.0)
                    }}

                    /// Performs a bitwise OR on each [`{scalar}`] lane.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::splat(0b01).or({name}::splat(0b10)), {name}::splat(0b11));
                    /// 
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn or(self, rhs: {name}) -> {name} {{
                        {name}(self.0 | rhs.0)
                    }}

                    /// Performs a bitwise AND on each [`{scalar}`] lane.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::splat(0b1101).and({name}::splat(0b0111)), {name}::splat(0b0101));
                    /// 
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn and(self, rhs: {name}) -> {name} {{
                        {name}(self.0 & rhs.0)
                    }}

                    /// Performs a bitwise XOR on each [`{scalar}`] lane.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::splat(0b1101).xor({name}::splat(0b0111)), {name}::splat(0b1010));
                    /// 
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn xor(self, rhs: {name}) -> {name} {{
                        {name}(self.0 ^ rhs.0)
                    }}
                }}
            "
        )?;

        Ok(())
    }

    /// Implements bit shift operations.
    pub fn shift(&self, out: &mut dyn fmt::Write) -> anyhow::Result<()> {
        let Self {
            scalar,
            lanes,
            repr,
            name,
        } = self;

        let bits = scalar.width().unwrap();

        // let upper_mask = {
        //     let nibbles = (0..lanes.get())
        //         .rev()
        //         .map(|lane| lane % 2 != 0)
        //         .map(|is_upper| if is_upper { "F" } else { "0" })
        //         .flat_map(|nibble| (0..bits.get() / 4).map(move |_| nibble));

        //     iter::once("0x")
        //         .chain(nibbles)
        //         .chain(["_", repr.name()])
        //         .collect::<String>()
        // };

        // let lower_mask = {
        //     let nibbles = (0..lanes.get())
        //         .rev()
        //         .map(|lane| lane % 2 == 0)
        //         .map(|is_lower| if is_lower { "F" } else { "0" })
        //         .flat_map(|nibble| (0..bits.get() / 4).map(move |_| nibble));

        //     iter::once("0x")
        //         .chain(nibbles)
        //         .chain(["_", repr.name()])
        //         .collect::<String>()
        // };

        let splat_one = {
            let nibbles = (0..lanes.get()).flat_map(|_| {
                (0..bits.get() / 4)
                    .map(|n| if n == 0 { "1" } else { "0" })
                    .rev()
            });

            iter::once("0x")
                .chain(nibbles)
                .chain(["_", repr.name()])
                .collect::<String>()
        };

        let splat_two = {
            let nibbles = (0..lanes.get()).flat_map(|_| {
                (0..bits.get() / 4)
                    .map(|n| if n == 0 { "2" } else { "0" })
                    .rev()
            });

            iter::once("0x")
                .chain(nibbles)
                .chain(["_", repr.name()])
                .collect::<String>()
        };

        let splat_msb = {
            let nibbles = (0..lanes.get())
                .flat_map(|_| (0..bits.get() / 4).map(|n| if n == 0 { "8" } else { "0" }));

            iter::once("0x")
                .chain(nibbles)
                .chain(["_", repr.name()])
                .collect::<String>()
        };

        // let shl_mask = format!("({splat_msb} >> {scalar}::BITS - 1 - n).wrapping_sub({splat_one})");

        let shr = if scalar.is_unsigned() {
            formatdoc!(
                "
                    // Perform a logical right shift.
                    {name}((self.0 >> n) & mask)
                "
            )
        } else {
            formatdoc!(
                "
                    // Perform a logical right shift.
                    let logical = (self.0 >> n) & mask;

                    // Calculate the sign mask.
                    let sign_mask = self.0 & {splat_msb};

                    // Calculate the sign extension.
                    //
                    // This essentially calculates a vector where the leading `n` bits of each lane
                    // are all set to the sign bit of the source lane.
                    let sign_ext = (sign_mask - (sign_mask >> n)) << 1;

                    // SAFETY: We know that `logical` and `sign_ext` do not have any overlapping set bits.
                    //
                    //         We know this because `logical` is the result of a zero-extended right shift
                    //         on all of the lanes.
                    //
                    //         Since we know none of that none of the bits overlap, then the sum calculation
                    //         can never overflow. As an overflow for any given bit (in unsigned arithmetic)
                    //         can only occur if both bits are `1`.
                    {name}(unsafe {{ logical.unchecked_add(sign_ext) }})
                "
            )

            // formatdoc!(
            //     "
            //         // Calculate a mask of the sign bits.
            //         let sign_mask = self.0 & {splat_msb};

            //         // Calculate a mask of the negative lanes.
            //         let neg_mask =  sign_mask.wrapping_add(
            //             sign_mask.wrapping_sub(
            //                 sign_mask >> {scalar}::BITS - 1,
            //             ),
            //         );

            //         // Calculate the shift. This works by NOTing the negative lanes,
            //         // performing a right shift, and then NOTing the negative lanes
            //         // again, which performs the sign extension.
            //         //
            //         // For non-negative lanes, it's just the same as an unsigned
            //         // right shift.
            //         let shifted = ((self.0 ^ neg_mask) >> n) ^ neg_mask;

            //         {name}(shifted & mask)

            //     "
            // )
        };

        writedoc!(
            out,
            "
                impl {name} {{
                    /// Performs an unchecked left shift on every [`{scalar}`] lane.
                    ///
                    /// # Safety
                    ///
                    /// The caller must ensure `n < {bits}`. Failure to do so is undefined behavior.
                    #[inline(always)]
                    #[must_use]
                    #[track_caller]
                    pub const unsafe fn unchecked_shl(self, n: u32) -> {name} {{
                        // SAFETY: The caller ensures `n < {bits}`.
                        unsafe {{ ::core::hint::assert_unchecked(n < {scalar}::BITS) }};

                        // Calculate the mask for the bits we want to keep.
                        let mask = !({splat_msb} >> {scalar}::BITS - 1 - n).wrapping_sub({splat_one});

                        // Calculate the left shift.
                        let shifted = self.0 << n;

                        {name}(shifted & mask)
                    }}

                    /// Performs an unchecked right shift on every [`{scalar}`] lane.
                    ///
                    /// # Safety
                    ///
                    /// The caller must ensure `n < {bits}`. Failure to do so is undefined behavior.
                    #[inline(always)]
                    #[must_use]
                    #[track_caller]
                    pub const unsafe fn unchecked_shr(self, n: u32) -> {name} {{
                        // SAFETY: The caller ensures `n < {bits}`.
                        unsafe {{ ::core::hint::assert_unchecked(n < {scalar}::BITS) }};
                    
                        // Calculate the mask for the bits we want to keep.
                        //
                        // TODO: Figure out a way that is as quick as the mask calculation for `shl`.
                        //
                        //       According to LLVM-MCA, on Zen4 this seems to put undue stress on the ALU
                        //       when doing the wrapping subtraction.
                        //
                        //       There *may* be a way around this, but I am unaware of how. Until I figure
                        //       that out, this seems to be the fastest way of calculating the mask.
                        let mask = ({splat_two} << {scalar}::BITS - 1 - n).wrapping_sub({splat_one});
                        
                        {shr}
                    }}

                    /// Performs a wrapping left shift on every [`{scalar}`] lane.
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::splat(0b01).wrapping_shl(1), {name}::splat(0b10));
                    /// 
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn wrapping_shl(self, n: u32) -> {name} {{
                        // SAFETY: By masking by the lane bit size we ensure that
                        //         we're not overflowing when we shift.
                        unsafe {{ self.unchecked_shl(n & ({scalar}::BITS - 1)) }}
                    }}

                    /// Performs a wrapping right shift on every [`{scalar}`] lane.
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::splat(0b10).wrapping_shr(1), {name}::splat(0b01));
                    ///
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn wrapping_shr(self, n: u32) -> {name} {{
                        // SAFETY: By masking by the lane bit size we ensure that
                        //         we're not overflowing when we shift.
                        unsafe {{ self.unchecked_shr(n & ({scalar}::BITS - 1)) }}
                    }}

                    /// Performs an overflowing left shift on every [`{scalar}`] lane.
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::splat(0b001).overflowing_shl(2), ({name}::splat(0b100), false));
                    /// assert_eq!({name}::splat(0b001).overflowing_shl({bits}), ({name}::splat(0b001), true));
                    ///
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn overflowing_shl(self, n: u32) -> ({name}, bool) {{
                        (self.wrapping_shl(n), n >= {scalar}::BITS)
                    }}

                    /// Performs an overflowing right shift on every [`{scalar}`] lane.
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    ///
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::splat(0b100).overflowing_shr(2), ({name}::splat(0b001), false));
                    /// assert_eq!({name}::splat(0b100).overflowing_shr({bits}), ({name}::splat(0b100), true));
                    ///
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn overflowing_shr(self, n: u32) -> ({name}, bool) {{
                        (self.wrapping_shr(n), n >= {scalar}::BITS)
                    }}

                    /// Performs a checked left shift on every [`{scalar}`] lane.
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::splat(0b001).checked_shl(2), Some({name}::splat(0b100)));
                    /// assert_eq!({name}::splat(0b001).checked_shl({bits}), None);
                    ///
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn checked_shl(self, n: u32) -> Option<{name}> {{
                        if n < {scalar}::BITS {{
                            // SAFETY: We just checked that `n` is in range.
                            Some(unsafe {{ self.unchecked_shl(n) }})
                        }} else {{
                            None
                        }}
                    }}

                    /// Performs a checked right shift on every [`{scalar}`] lane.
                    ///
                    /// # Examples
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::splat(0b100).checked_shr(2), Some({name}::splat(0b001)));
                    /// assert_eq!({name}::splat(0b100).checked_shr({bits}), None);
                    ///
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn checked_shr(self, n: u32) -> Option<{name}> {{
                        if n < {scalar}::BITS {{
                            // SAFETY: We just checked that `n` is in range.
                            Some(unsafe {{ self.unchecked_shr(n) }})
                        }} else {{
                            None
                        }}
                    }}

                    /// Performs an unbounded left shift on every [`{scalar}`] lane.
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::splat(0b001).unbounded_shl(2), {name}::splat(0b100));
                    /// assert_eq!({name}::splat(0b001).unbounded_shl({bits}), {name}::splat(0));
                    /// 
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn unbounded_shl(self, n: u32) -> {name} {{
                        if n < {scalar}::BITS {{
                            // SAFETY: We just checked that `n` is in range.
                            unsafe {{ self.unchecked_shl(n) }}
                        }} else {{
                            {name}::splat(0)
                        }}
                    }}

                    /// Performs an unbounded right shift on every [`{scalar}`] lane.
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::splat(0b100).unbounded_shr(2), {name}::splat(0b001));
                    /// assert_eq!({name}::splat(0b100).unbounded_shr({bits}), {name}::splat(0));
                    ///
                    /// ```
                    #[inline(always)]
                    #[must_use]
                    pub const fn unbounded_shr(self, n: u32) -> {name} {{
                        if n < {scalar}::BITS {{
                            // SAFETY: We just checked that `n` is in range.
                            unsafe {{ self.unchecked_shr(n) }}
                        }} else {{
                            {name}::splat(0)
                        }}
                    }}
                }}   
            "
        )?;

        Ok(())
    }
}
