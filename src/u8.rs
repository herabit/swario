/// A 16-bit SWAR vector containing 2 [`u8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u16`], but is
/// treated as a `[u8; 2]`.
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
pub struct U8x2(
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

// We need to ensure that `U8x2` is the same size as `[u8; 2]`.
const _: () = {
    let vec = ::core::mem::size_of::<U8x2>();
    let lanes = ::core::mem::size_of::<[u8; 2]>();

    ::core::assert!(
        vec == lanes,
        "the size of `U8x2` must be equal to that of `[u8; 2]`"
    );
};

// We need to ensure that `U8x2` is sufficiently aligned for `[u8; 2]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<U8x2>();
    let lanes = ::core::mem::align_of::<[u8; 2]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `U8x2` is not sufficiently aligned for `[u8; 2]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl U8x2 {
    /// Create a new [`U8x2`] from an array of 2 [`u8`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [u8; 2]) -> U8x2 {
        // SAFETY: We know that `U8x2` and `[u8; 2]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[u8; 2] {
        // SAFETY: `U8x2` and `[u8; 2]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U8x2` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const U8x2 as *const [u8; 2]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [u8; 2] {
        // SAFETY: `U8x2` and `[u8; 2]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U8x2` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut U8x2 as *mut [u8; 2]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [u8; 2] {
        // SAFETY: We know that `U8x2` and `[u8; 2]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`U8x2`] with all 2 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: u8) -> U8x2 {
        U8x2::from_array([value; 2])
    }

    /// Create a new [`U8x2`] from its [`u8`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(a: u8, b: u8) -> U8x2 {
        U8x2::from_array([a, b])
    }

    /// Create a new [`U8x2`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u16) -> U8x2 {
        U8x2(bits)
    }

    /// Create a reference to a [`U8x2`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u16) -> &U8x2 {
        // SAFETY: `U8x2` is a transparent wrapper over `u16`,
        //         so this is always safe.
        unsafe { &*(bits as *const u16 as *const U8x2) }
    }

    /// Create a mutable reference to a [`U8x2`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u16) -> &mut U8x2 {
        // SAFETY: `U8x2` is a transparent wrapper over `u16`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u16 as *mut U8x2) }
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
impl U8x2 {
    /// The size of this vector in bits (16-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::BITS, u16::BITS);
    /// assert_eq!(U8x2::BITS, 16);
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
    /// assert_eq!(U8x2::LANE_BITS, u8::BITS);
    /// assert_eq!(U8x2::LANE_BITS, 8);
    ///
    /// ```
    pub const LANE_BITS: u32 = u8::BITS;

    /// The amount of [`u8`] lanes (2) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::LANES, 2);
    /// assert_eq!(U8x2::LANES, size_of::<U8x2>() / size_of::<u8>());
    ///
    /// ```
    pub const LANES: usize = 2;

    /// A [`U8x2`] with all lanes set to [`u8::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::MAX.to_array(), [255; 2]);
    ///
    /// ```
    pub const MAX: U8x2 = U8x2::splat(u8::MAX);

    /// A [`U8x2`] with all lanes set to [`u8::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::MIN.to_array(), [0; 2]);
    ///
    /// ```
    pub const MIN: U8x2 = U8x2::splat(u8::MIN);

    /// A [`U8x2`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::LSB.to_array(), [0x01; 2]);
    ///
    /// ```
    pub const LSB: U8x2 = U8x2::splat(1 << 0);

    /// A [`U8x2`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::MSB.to_array(), [0x80; 2]);
    ///
    /// ```
    pub const MSB: U8x2 = U8x2::splat(1 << (u8::BITS - 1));
}
/// A 32-bit SWAR vector containing 4 [`u8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u32`], but is
/// treated as a `[u8; 4]`.
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
pub struct U8x4(
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

// We need to ensure that `U8x4` is the same size as `[u8; 4]`.
const _: () = {
    let vec = ::core::mem::size_of::<U8x4>();
    let lanes = ::core::mem::size_of::<[u8; 4]>();

    ::core::assert!(
        vec == lanes,
        "the size of `U8x4` must be equal to that of `[u8; 4]`"
    );
};

// We need to ensure that `U8x4` is sufficiently aligned for `[u8; 4]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<U8x4>();
    let lanes = ::core::mem::align_of::<[u8; 4]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `U8x4` is not sufficiently aligned for `[u8; 4]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl U8x4 {
    /// Create a new [`U8x4`] from an array of 4 [`u8`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [u8; 4]) -> U8x4 {
        // SAFETY: We know that `U8x4` and `[u8; 4]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[u8; 4] {
        // SAFETY: `U8x4` and `[u8; 4]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U8x4` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const U8x4 as *const [u8; 4]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [u8; 4] {
        // SAFETY: `U8x4` and `[u8; 4]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U8x4` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut U8x4 as *mut [u8; 4]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [u8; 4] {
        // SAFETY: We know that `U8x4` and `[u8; 4]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`U8x4`] with all 4 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: u8) -> U8x4 {
        U8x4::from_array([value; 4])
    }

    /// Create a new [`U8x4`] from its [`u8`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(a: u8, b: u8, c: u8, d: u8) -> U8x4 {
        U8x4::from_array([a, b, c, d])
    }

    /// Create a new [`U8x4`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u32) -> U8x4 {
        U8x4(bits)
    }

    /// Create a reference to a [`U8x4`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u32) -> &U8x4 {
        // SAFETY: `U8x4` is a transparent wrapper over `u32`,
        //         so this is always safe.
        unsafe { &*(bits as *const u32 as *const U8x4) }
    }

    /// Create a mutable reference to a [`U8x4`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u32) -> &mut U8x4 {
        // SAFETY: `U8x4` is a transparent wrapper over `u32`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u32 as *mut U8x4) }
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
impl U8x4 {
    /// The size of this vector in bits (32-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::BITS, u32::BITS);
    /// assert_eq!(U8x4::BITS, 32);
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
    /// assert_eq!(U8x4::LANE_BITS, u8::BITS);
    /// assert_eq!(U8x4::LANE_BITS, 8);
    ///
    /// ```
    pub const LANE_BITS: u32 = u8::BITS;

    /// The amount of [`u8`] lanes (4) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::LANES, 4);
    /// assert_eq!(U8x4::LANES, size_of::<U8x4>() / size_of::<u8>());
    ///
    /// ```
    pub const LANES: usize = 4;

    /// A [`U8x4`] with all lanes set to [`u8::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::MAX.to_array(), [255; 4]);
    ///
    /// ```
    pub const MAX: U8x4 = U8x4::splat(u8::MAX);

    /// A [`U8x4`] with all lanes set to [`u8::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::MIN.to_array(), [0; 4]);
    ///
    /// ```
    pub const MIN: U8x4 = U8x4::splat(u8::MIN);

    /// A [`U8x4`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::LSB.to_array(), [0x01; 4]);
    ///
    /// ```
    pub const LSB: U8x4 = U8x4::splat(1 << 0);

    /// A [`U8x4`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::MSB.to_array(), [0x80; 4]);
    ///
    /// ```
    pub const MSB: U8x4 = U8x4::splat(1 << (u8::BITS - 1));
}
/// A 64-bit SWAR vector containing 8 [`u8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u64`], but is
/// treated as a `[u8; 8]`.
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
pub struct U8x8(
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

// We need to ensure that `U8x8` is the same size as `[u8; 8]`.
const _: () = {
    let vec = ::core::mem::size_of::<U8x8>();
    let lanes = ::core::mem::size_of::<[u8; 8]>();

    ::core::assert!(
        vec == lanes,
        "the size of `U8x8` must be equal to that of `[u8; 8]`"
    );
};

// We need to ensure that `U8x8` is sufficiently aligned for `[u8; 8]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<U8x8>();
    let lanes = ::core::mem::align_of::<[u8; 8]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `U8x8` is not sufficiently aligned for `[u8; 8]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl U8x8 {
    /// Create a new [`U8x8`] from an array of 8 [`u8`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [u8; 8]) -> U8x8 {
        // SAFETY: We know that `U8x8` and `[u8; 8]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[u8; 8] {
        // SAFETY: `U8x8` and `[u8; 8]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U8x8` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const U8x8 as *const [u8; 8]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [u8; 8] {
        // SAFETY: `U8x8` and `[u8; 8]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U8x8` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut U8x8 as *mut [u8; 8]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [u8; 8] {
        // SAFETY: We know that `U8x8` and `[u8; 8]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`U8x8`] with all 8 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: u8) -> U8x8 {
        U8x8::from_array([value; 8])
    }

    /// Create a new [`U8x8`] from its [`u8`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(a: u8, b: u8, c: u8, d: u8, e: u8, f: u8, g: u8, h: u8) -> U8x8 {
        U8x8::from_array([a, b, c, d, e, f, g, h])
    }

    /// Create a new [`U8x8`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u64) -> U8x8 {
        U8x8(bits)
    }

    /// Create a reference to a [`U8x8`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u64) -> &U8x8 {
        // SAFETY: `U8x8` is a transparent wrapper over `u64`,
        //         so this is always safe.
        unsafe { &*(bits as *const u64 as *const U8x8) }
    }

    /// Create a mutable reference to a [`U8x8`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u64) -> &mut U8x8 {
        // SAFETY: `U8x8` is a transparent wrapper over `u64`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u64 as *mut U8x8) }
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
impl U8x8 {
    /// The size of this vector in bits (64-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::BITS, u64::BITS);
    /// assert_eq!(U8x8::BITS, 64);
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
    /// assert_eq!(U8x8::LANE_BITS, u8::BITS);
    /// assert_eq!(U8x8::LANE_BITS, 8);
    ///
    /// ```
    pub const LANE_BITS: u32 = u8::BITS;

    /// The amount of [`u8`] lanes (8) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::LANES, 8);
    /// assert_eq!(U8x8::LANES, size_of::<U8x8>() / size_of::<u8>());
    ///
    /// ```
    pub const LANES: usize = 8;

    /// A [`U8x8`] with all lanes set to [`u8::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::MAX.to_array(), [255; 8]);
    ///
    /// ```
    pub const MAX: U8x8 = U8x8::splat(u8::MAX);

    /// A [`U8x8`] with all lanes set to [`u8::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::MIN.to_array(), [0; 8]);
    ///
    /// ```
    pub const MIN: U8x8 = U8x8::splat(u8::MIN);

    /// A [`U8x8`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::LSB.to_array(), [0x01; 8]);
    ///
    /// ```
    pub const LSB: U8x8 = U8x8::splat(1 << 0);

    /// A [`U8x8`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::MSB.to_array(), [0x80; 8]);
    ///
    /// ```
    pub const MSB: U8x8 = U8x8::splat(1 << (u8::BITS - 1));
}
/// A 128-bit SWAR vector containing 16 [`u8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u128`], but is
/// treated as a `[u8; 16]`.
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
pub struct U8x16(
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

// We need to ensure that `U8x16` is the same size as `[u8; 16]`.
const _: () = {
    let vec = ::core::mem::size_of::<U8x16>();
    let lanes = ::core::mem::size_of::<[u8; 16]>();

    ::core::assert!(
        vec == lanes,
        "the size of `U8x16` must be equal to that of `[u8; 16]`"
    );
};

// We need to ensure that `U8x16` is sufficiently aligned for `[u8; 16]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<U8x16>();
    let lanes = ::core::mem::align_of::<[u8; 16]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `U8x16` is not sufficiently aligned for `[u8; 16]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl U8x16 {
    /// Create a new [`U8x16`] from an array of 16 [`u8`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [u8; 16]) -> U8x16 {
        // SAFETY: We know that `U8x16` and `[u8; 16]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[u8; 16] {
        // SAFETY: `U8x16` and `[u8; 16]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U8x16` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const U8x16 as *const [u8; 16]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [u8; 16] {
        // SAFETY: `U8x16` and `[u8; 16]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U8x16` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut U8x16 as *mut [u8; 16]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [u8; 16] {
        // SAFETY: We know that `U8x16` and `[u8; 16]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`U8x16`] with all 16 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: u8) -> U8x16 {
        U8x16::from_array([value; 16])
    }

    /// Create a new [`U8x16`] from its [`u8`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(
        a: u8,
        b: u8,
        c: u8,
        d: u8,
        e: u8,
        f: u8,
        g: u8,
        h: u8,
        i: u8,
        j: u8,
        k: u8,
        l: u8,
        m: u8,
        n: u8,
        o: u8,
        p: u8,
    ) -> U8x16 {
        U8x16::from_array([a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p])
    }

    /// Create a new [`U8x16`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u128) -> U8x16 {
        U8x16(bits)
    }

    /// Create a reference to a [`U8x16`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u128) -> &U8x16 {
        // SAFETY: `U8x16` is a transparent wrapper over `u128`,
        //         so this is always safe.
        unsafe { &*(bits as *const u128 as *const U8x16) }
    }

    /// Create a mutable reference to a [`U8x16`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u128) -> &mut U8x16 {
        // SAFETY: `U8x16` is a transparent wrapper over `u128`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u128 as *mut U8x16) }
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
impl U8x16 {
    /// The size of this vector in bits (128-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::BITS, u128::BITS);
    /// assert_eq!(U8x16::BITS, 128);
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
    /// assert_eq!(U8x16::LANE_BITS, u8::BITS);
    /// assert_eq!(U8x16::LANE_BITS, 8);
    ///
    /// ```
    pub const LANE_BITS: u32 = u8::BITS;

    /// The amount of [`u8`] lanes (16) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::LANES, 16);
    /// assert_eq!(U8x16::LANES, size_of::<U8x16>() / size_of::<u8>());
    ///
    /// ```
    pub const LANES: usize = 16;

    /// A [`U8x16`] with all lanes set to [`u8::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::MAX.to_array(), [255; 16]);
    ///
    /// ```
    pub const MAX: U8x16 = U8x16::splat(u8::MAX);

    /// A [`U8x16`] with all lanes set to [`u8::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::MIN.to_array(), [0; 16]);
    ///
    /// ```
    pub const MIN: U8x16 = U8x16::splat(u8::MIN);

    /// A [`U8x16`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::LSB.to_array(), [0x01; 16]);
    ///
    /// ```
    pub const LSB: U8x16 = U8x16::splat(1 << 0);

    /// A [`U8x16`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::MSB.to_array(), [0x80; 16]);
    ///
    /// ```
    pub const MSB: U8x16 = U8x16::splat(1 << (u8::BITS - 1));
}
