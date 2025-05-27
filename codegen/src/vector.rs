use core::fmt;
use std::num::NonZero;

use anyhow::Context;
use indoc::writedoc;

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
        self.define(out).context("defining type")?;
        self.base(out).context("defining constructors")?;
        self.consts(out).context("defining constants")?;

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
                #[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
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
                    ::zerocopy::FromBytes, \
                    ::zerocopy::IntoBytes, \
                    ::zerocopy::KnownLayout, \
                    ::zerocopy::Immutable\
                    {unaligned}\
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

        let repr_width = repr.width().context("invalid repr")?;
        let scalar_width = scalar.width().context("invalid scalar")?;
        let min = Scalar::min(*scalar).unwrap();
        let max = Scalar::max(*scalar).unwrap();

        let lsb = {
            let mut lsb = String::from("0x");

            for _ in 0..(scalar_width.get() / 4) - 1 {
                lsb.push_str("0");
            }

            lsb.push_str("1");
            lsb
        };

        let msb = {
            let mut msb = String::from("0x8");

            for _ in 0..(scalar_width.get() / 4) - 1 {
                msb.push_str("0");
            }

            // For signed types we need to insert a cast to avoid an `overflowing_literals` lint.
            if scalar.is_signed() {
                msb.push_str("_");
                msb.push_str(scalar.unsigned().name());
                msb.push_str(" as ");
                msb.push_str(scalar.name());
            }

            msb
        };

        writedoc!(
            out,
            "
                impl {name} {{
                    /// The size of this vector in bits ({repr_width}-bit).
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::BITS, {repr}::BITS);
                    /// assert_eq!({name}::BITS, {repr_width});
                    /// 
                    /// ```
                    pub const BITS: u32 = {repr}::BITS;

                    /// The size of this vector's lanes in bits ({scalar_width}-bit).
                    ///
                    /// # Examples
                    ///
                    /// Basic usage:
                    ///
                    /// ```
                    /// use swario::*;
                    ///
                    /// assert_eq!({name}::LANE_BITS, {scalar}::BITS);
                    /// assert_eq!({name}::LANE_BITS, {scalar_width});
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
                    /// assert_eq!({name}::MAX.to_array(), [{max}; {lanes}]);
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
                    /// assert_eq!({name}::MIN.to_array(), [{min}; {lanes}]);
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
                    /// assert_eq!({name}::LSB.to_array(), [{lsb}; {lanes}]);
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
                    /// assert_eq!({name}::MSB.to_array(), [{msb}; {lanes}]);
                    ///
                    /// ```
                    pub const MSB: {name} = {name}::splat(1 << ({scalar}::BITS - 1));
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

    /// Adds lanewise rotations.
    pub fn rotate_lanes(&self, out: &mut dyn fmt::Write) -> anyhow::Result<()> {
        let Self {
            scalar,
            lanes,
            repr,
            name,
        } = self;

        // let base = (0..lanes.get()).map(|l| l a)

        Ok(())
    }
}
