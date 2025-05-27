/// A 16-bit SWAR vector containing 2 [`i8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u16`], but is
/// treated as a `[i8; 2]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(
    feature = "bytemuck",
    derive(::bytemuck::Zeroable, ::bytemuck::Pod, ::bytemuck::TransparentWrapper)
)]
#[cfg_attr(
    feature = "zerocopy",
    ::zerocopy::FromBytes,
    ::zerocopy::IntoBytes,
    ::zerocopy::KnownLayout,
    ::zerocopy::Immutable
)]
#[repr(transparent)]
pub struct I8x2(
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
    pub u16,
);

// We need to ensure that `I8x2` is the same size as `[i8; 2]`.
const _: () = {
    let vec = ::core::mem::size_of::<I8x2>();
    let lanes = ::core::mem::size_of::<[i8; 2]>();

    ::core::assert!(
        vec == lanes,
        "the size of `I8x2` must be equal to that of `[i8; 2]`"
    );
};

// We need to ensure that `I8x2` is sufficiently aligned for `[i8; 2]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<I8x2>();
    let lanes = ::core::mem::align_of::<[i8; 2]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `I8x2` is not sufficiently aligned for `[i8; 2]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl I8x2 {
    /// Create a new [`I8x2`] from an array of 2 [`i8`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [i8; 2]) -> I8x2 {
        // SAFETY: We know that `I8x2` and `[i8; 2]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[i8; 2] {
        // SAFETY: `I8x2` and `[i8; 2]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I8x2` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const I8x2 as *const [i8; 2]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [i8; 2] {
        // SAFETY: `I8x2` and `[i8; 2]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I8x2` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut I8x2 as *mut [i8; 2]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [i8; 2] {
        // SAFETY: We know that `I8x2` and `[i8; 2]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`I8x2`] with all 2 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: i8) -> I8x2 {
        I8x2::from_array([value; 2])
    }

    /// Create a new [`I8x2`] from its [`i8`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(a: i8, b: i8) -> I8x2 {
        I8x2::from_array([a, b])
    }

    /// Create a new [`I8x2`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u16) -> I8x2 {
        I8x2(bits)
    }

    /// Create a reference to a [`I8x2`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u16) -> &I8x2 {
        // SAFETY: `I8x2` is a transparent wrapper over `u16`,
        //         so this is always safe.
        unsafe { &*(bits as *const u16 as *const I8x2) }
    }

    /// Create a mutable reference to a [`I8x2`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u16) -> &mut I8x2 {
        // SAFETY: `I8x2` is a transparent wrapper over `u16`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u16 as *mut I8x2) }
    }

    /// Get a reference to the underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn as_bits(&self) -> &u16 {
        &self.0
    }

    /// Get a mutable reference to the underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn as_bits_mut(&mut self) -> &mut u16 {
        &mut self.0
    }

    /// Get the underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn to_bits(self) -> u16 {
        self.0
    }
}
impl I8x2 {
    /// The size of this vector in bits (16-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::BITS, u16::BITS);
    /// assert_eq!(I8x2::BITS, 16);
    ///
    /// ```
    pub const BITS: u32 = u16::BITS;

    /// The size of this vector's lanes in bits (8-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::LANE_BITS, i8::BITS);
    /// assert_eq!(I8x2::LANE_BITS, 8);
    ///
    /// ```
    pub const LANE_BITS: u32 = i8::BITS;

    /// The amount of [`i8`] lanes (2) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::LANES, 2);
    /// assert_eq!(I8x2::LANES, size_of::<I8x2>() / size_of::<i8>());
    ///
    /// ```
    pub const LANES: usize = 2;

    /// A [`I8x2`] with all lanes set to [`i8::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::MAX.to_array(), [127; 2]);
    ///
    /// ```
    pub const MAX: I8x2 = I8x2::splat(i8::MAX);

    /// A [`I8x2`] with all lanes set to [`i8::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::MIN.to_array(), [-128; 2]);
    ///
    /// ```
    pub const MIN: I8x2 = I8x2::splat(i8::MIN);

    /// A [`I8x2`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::LSB.to_array(), [0x01; 2]);
    ///
    /// ```
    pub const LSB: I8x2 = I8x2::splat(1 << 0);

    /// A [`I8x2`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::MSB.to_array(), [0x80_u8 as i8; 2]);
    ///
    /// ```
    pub const MSB: I8x2 = I8x2::splat(1 << (i8::BITS - 1));
}
/// A 32-bit SWAR vector containing 4 [`i8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u32`], but is
/// treated as a `[i8; 4]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(
    feature = "bytemuck",
    derive(::bytemuck::Zeroable, ::bytemuck::Pod, ::bytemuck::TransparentWrapper)
)]
#[cfg_attr(
    feature = "zerocopy",
    ::zerocopy::FromBytes,
    ::zerocopy::IntoBytes,
    ::zerocopy::KnownLayout,
    ::zerocopy::Immutable
)]
#[repr(transparent)]
pub struct I8x4(
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
    pub u32,
);

// We need to ensure that `I8x4` is the same size as `[i8; 4]`.
const _: () = {
    let vec = ::core::mem::size_of::<I8x4>();
    let lanes = ::core::mem::size_of::<[i8; 4]>();

    ::core::assert!(
        vec == lanes,
        "the size of `I8x4` must be equal to that of `[i8; 4]`"
    );
};

// We need to ensure that `I8x4` is sufficiently aligned for `[i8; 4]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<I8x4>();
    let lanes = ::core::mem::align_of::<[i8; 4]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `I8x4` is not sufficiently aligned for `[i8; 4]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl I8x4 {
    /// Create a new [`I8x4`] from an array of 4 [`i8`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [i8; 4]) -> I8x4 {
        // SAFETY: We know that `I8x4` and `[i8; 4]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[i8; 4] {
        // SAFETY: `I8x4` and `[i8; 4]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I8x4` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const I8x4 as *const [i8; 4]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [i8; 4] {
        // SAFETY: `I8x4` and `[i8; 4]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I8x4` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut I8x4 as *mut [i8; 4]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [i8; 4] {
        // SAFETY: We know that `I8x4` and `[i8; 4]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`I8x4`] with all 4 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: i8) -> I8x4 {
        I8x4::from_array([value; 4])
    }

    /// Create a new [`I8x4`] from its [`i8`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(a: i8, b: i8, c: i8, d: i8) -> I8x4 {
        I8x4::from_array([a, b, c, d])
    }

    /// Create a new [`I8x4`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u32) -> I8x4 {
        I8x4(bits)
    }

    /// Create a reference to a [`I8x4`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u32) -> &I8x4 {
        // SAFETY: `I8x4` is a transparent wrapper over `u32`,
        //         so this is always safe.
        unsafe { &*(bits as *const u32 as *const I8x4) }
    }

    /// Create a mutable reference to a [`I8x4`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u32) -> &mut I8x4 {
        // SAFETY: `I8x4` is a transparent wrapper over `u32`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u32 as *mut I8x4) }
    }

    /// Get a reference to the underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn as_bits(&self) -> &u32 {
        &self.0
    }

    /// Get a mutable reference to the underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn as_bits_mut(&mut self) -> &mut u32 {
        &mut self.0
    }

    /// Get the underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn to_bits(self) -> u32 {
        self.0
    }
}
impl I8x4 {
    /// The size of this vector in bits (32-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::BITS, u32::BITS);
    /// assert_eq!(I8x4::BITS, 32);
    ///
    /// ```
    pub const BITS: u32 = u32::BITS;

    /// The size of this vector's lanes in bits (8-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::LANE_BITS, i8::BITS);
    /// assert_eq!(I8x4::LANE_BITS, 8);
    ///
    /// ```
    pub const LANE_BITS: u32 = i8::BITS;

    /// The amount of [`i8`] lanes (4) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::LANES, 4);
    /// assert_eq!(I8x4::LANES, size_of::<I8x4>() / size_of::<i8>());
    ///
    /// ```
    pub const LANES: usize = 4;

    /// A [`I8x4`] with all lanes set to [`i8::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::MAX.to_array(), [127; 4]);
    ///
    /// ```
    pub const MAX: I8x4 = I8x4::splat(i8::MAX);

    /// A [`I8x4`] with all lanes set to [`i8::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::MIN.to_array(), [-128; 4]);
    ///
    /// ```
    pub const MIN: I8x4 = I8x4::splat(i8::MIN);

    /// A [`I8x4`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::LSB.to_array(), [0x01; 4]);
    ///
    /// ```
    pub const LSB: I8x4 = I8x4::splat(1 << 0);

    /// A [`I8x4`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::MSB.to_array(), [0x80_u8 as i8; 4]);
    ///
    /// ```
    pub const MSB: I8x4 = I8x4::splat(1 << (i8::BITS - 1));
}
/// A 64-bit SWAR vector containing 8 [`i8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u64`], but is
/// treated as a `[i8; 8]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(
    feature = "bytemuck",
    derive(::bytemuck::Zeroable, ::bytemuck::Pod, ::bytemuck::TransparentWrapper)
)]
#[cfg_attr(
    feature = "zerocopy",
    ::zerocopy::FromBytes,
    ::zerocopy::IntoBytes,
    ::zerocopy::KnownLayout,
    ::zerocopy::Immutable
)]
#[repr(transparent)]
pub struct I8x8(
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
    pub u64,
);

// We need to ensure that `I8x8` is the same size as `[i8; 8]`.
const _: () = {
    let vec = ::core::mem::size_of::<I8x8>();
    let lanes = ::core::mem::size_of::<[i8; 8]>();

    ::core::assert!(
        vec == lanes,
        "the size of `I8x8` must be equal to that of `[i8; 8]`"
    );
};

// We need to ensure that `I8x8` is sufficiently aligned for `[i8; 8]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<I8x8>();
    let lanes = ::core::mem::align_of::<[i8; 8]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `I8x8` is not sufficiently aligned for `[i8; 8]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl I8x8 {
    /// Create a new [`I8x8`] from an array of 8 [`i8`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [i8; 8]) -> I8x8 {
        // SAFETY: We know that `I8x8` and `[i8; 8]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[i8; 8] {
        // SAFETY: `I8x8` and `[i8; 8]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I8x8` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const I8x8 as *const [i8; 8]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [i8; 8] {
        // SAFETY: `I8x8` and `[i8; 8]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I8x8` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut I8x8 as *mut [i8; 8]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [i8; 8] {
        // SAFETY: We know that `I8x8` and `[i8; 8]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`I8x8`] with all 8 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: i8) -> I8x8 {
        I8x8::from_array([value; 8])
    }

    /// Create a new [`I8x8`] from its [`i8`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(a: i8, b: i8, c: i8, d: i8, e: i8, f: i8, g: i8, h: i8) -> I8x8 {
        I8x8::from_array([a, b, c, d, e, f, g, h])
    }

    /// Create a new [`I8x8`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u64) -> I8x8 {
        I8x8(bits)
    }

    /// Create a reference to a [`I8x8`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u64) -> &I8x8 {
        // SAFETY: `I8x8` is a transparent wrapper over `u64`,
        //         so this is always safe.
        unsafe { &*(bits as *const u64 as *const I8x8) }
    }

    /// Create a mutable reference to a [`I8x8`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u64) -> &mut I8x8 {
        // SAFETY: `I8x8` is a transparent wrapper over `u64`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u64 as *mut I8x8) }
    }

    /// Get a reference to the underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn as_bits(&self) -> &u64 {
        &self.0
    }

    /// Get a mutable reference to the underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn as_bits_mut(&mut self) -> &mut u64 {
        &mut self.0
    }

    /// Get the underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn to_bits(self) -> u64 {
        self.0
    }
}
impl I8x8 {
    /// The size of this vector in bits (64-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::BITS, u64::BITS);
    /// assert_eq!(I8x8::BITS, 64);
    ///
    /// ```
    pub const BITS: u32 = u64::BITS;

    /// The size of this vector's lanes in bits (8-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::LANE_BITS, i8::BITS);
    /// assert_eq!(I8x8::LANE_BITS, 8);
    ///
    /// ```
    pub const LANE_BITS: u32 = i8::BITS;

    /// The amount of [`i8`] lanes (8) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::LANES, 8);
    /// assert_eq!(I8x8::LANES, size_of::<I8x8>() / size_of::<i8>());
    ///
    /// ```
    pub const LANES: usize = 8;

    /// A [`I8x8`] with all lanes set to [`i8::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::MAX.to_array(), [127; 8]);
    ///
    /// ```
    pub const MAX: I8x8 = I8x8::splat(i8::MAX);

    /// A [`I8x8`] with all lanes set to [`i8::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::MIN.to_array(), [-128; 8]);
    ///
    /// ```
    pub const MIN: I8x8 = I8x8::splat(i8::MIN);

    /// A [`I8x8`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::LSB.to_array(), [0x01; 8]);
    ///
    /// ```
    pub const LSB: I8x8 = I8x8::splat(1 << 0);

    /// A [`I8x8`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::MSB.to_array(), [0x80_u8 as i8; 8]);
    ///
    /// ```
    pub const MSB: I8x8 = I8x8::splat(1 << (i8::BITS - 1));
}
/// A 128-bit SWAR vector containing 16 [`i8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u128`], but is
/// treated as a `[i8; 16]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(
    feature = "bytemuck",
    derive(::bytemuck::Zeroable, ::bytemuck::Pod, ::bytemuck::TransparentWrapper)
)]
#[cfg_attr(
    feature = "zerocopy",
    ::zerocopy::FromBytes,
    ::zerocopy::IntoBytes,
    ::zerocopy::KnownLayout,
    ::zerocopy::Immutable
)]
#[repr(transparent)]
pub struct I8x16(
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
    pub u128,
);

// We need to ensure that `I8x16` is the same size as `[i8; 16]`.
const _: () = {
    let vec = ::core::mem::size_of::<I8x16>();
    let lanes = ::core::mem::size_of::<[i8; 16]>();

    ::core::assert!(
        vec == lanes,
        "the size of `I8x16` must be equal to that of `[i8; 16]`"
    );
};

// We need to ensure that `I8x16` is sufficiently aligned for `[i8; 16]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<I8x16>();
    let lanes = ::core::mem::align_of::<[i8; 16]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `I8x16` is not sufficiently aligned for `[i8; 16]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl I8x16 {
    /// Create a new [`I8x16`] from an array of 16 [`i8`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [i8; 16]) -> I8x16 {
        // SAFETY: We know that `I8x16` and `[i8; 16]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[i8; 16] {
        // SAFETY: `I8x16` and `[i8; 16]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I8x16` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const I8x16 as *const [i8; 16]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [i8; 16] {
        // SAFETY: `I8x16` and `[i8; 16]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I8x16` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut I8x16 as *mut [i8; 16]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [i8; 16] {
        // SAFETY: We know that `I8x16` and `[i8; 16]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`I8x16`] with all 16 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: i8) -> I8x16 {
        I8x16::from_array([value; 16])
    }

    /// Create a new [`I8x16`] from its [`i8`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(
        a: i8,
        b: i8,
        c: i8,
        d: i8,
        e: i8,
        f: i8,
        g: i8,
        h: i8,
        i: i8,
        j: i8,
        k: i8,
        l: i8,
        m: i8,
        n: i8,
        o: i8,
        p: i8,
    ) -> I8x16 {
        I8x16::from_array([a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p])
    }

    /// Create a new [`I8x16`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u128) -> I8x16 {
        I8x16(bits)
    }

    /// Create a reference to a [`I8x16`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u128) -> &I8x16 {
        // SAFETY: `I8x16` is a transparent wrapper over `u128`,
        //         so this is always safe.
        unsafe { &*(bits as *const u128 as *const I8x16) }
    }

    /// Create a mutable reference to a [`I8x16`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u128) -> &mut I8x16 {
        // SAFETY: `I8x16` is a transparent wrapper over `u128`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u128 as *mut I8x16) }
    }

    /// Get a reference to the underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn as_bits(&self) -> &u128 {
        &self.0
    }

    /// Get a mutable reference to the underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn as_bits_mut(&mut self) -> &mut u128 {
        &mut self.0
    }

    /// Get the underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn to_bits(self) -> u128 {
        self.0
    }
}
impl I8x16 {
    /// The size of this vector in bits (128-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::BITS, u128::BITS);
    /// assert_eq!(I8x16::BITS, 128);
    ///
    /// ```
    pub const BITS: u32 = u128::BITS;

    /// The size of this vector's lanes in bits (8-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::LANE_BITS, i8::BITS);
    /// assert_eq!(I8x16::LANE_BITS, 8);
    ///
    /// ```
    pub const LANE_BITS: u32 = i8::BITS;

    /// The amount of [`i8`] lanes (16) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::LANES, 16);
    /// assert_eq!(I8x16::LANES, size_of::<I8x16>() / size_of::<i8>());
    ///
    /// ```
    pub const LANES: usize = 16;

    /// A [`I8x16`] with all lanes set to [`i8::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::MAX.to_array(), [127; 16]);
    ///
    /// ```
    pub const MAX: I8x16 = I8x16::splat(i8::MAX);

    /// A [`I8x16`] with all lanes set to [`i8::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::MIN.to_array(), [-128; 16]);
    ///
    /// ```
    pub const MIN: I8x16 = I8x16::splat(i8::MIN);

    /// A [`I8x16`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::LSB.to_array(), [0x01; 16]);
    ///
    /// ```
    pub const LSB: I8x16 = I8x16::splat(1 << 0);

    /// A [`I8x16`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::MSB.to_array(), [0x80_u8 as i8; 16]);
    ///
    /// ```
    pub const MSB: I8x16 = I8x16::splat(1 << (i8::BITS - 1));
}
