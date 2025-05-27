/// A 32-bit SWAR vector containing 2 [`u16`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u32`], but is
/// treated as a `[u16; 2]`.
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
pub struct U16x2(
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

// We need to ensure that `U16x2` is the same size as `[u16; 2]`.
const _: () = {
    let vec = ::core::mem::size_of::<U16x2>();
    let lanes = ::core::mem::size_of::<[u16; 2]>();

    ::core::assert!(
        vec == lanes,
        "the size of `U16x2` must be equal to that of `[u16; 2]`"
    );
};

// We need to ensure that `U16x2` is sufficiently aligned for `[u16; 2]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<U16x2>();
    let lanes = ::core::mem::align_of::<[u16; 2]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `U16x2` is not sufficiently aligned for `[u16; 2]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl U16x2 {
    /// Create a new [`U16x2`] from an array of 2 [`u16`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [u16; 2]) -> U16x2 {
        // SAFETY: We know that `U16x2` and `[u16; 2]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[u16; 2] {
        // SAFETY: `U16x2` and `[u16; 2]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U16x2` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const U16x2 as *const [u16; 2]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [u16; 2] {
        // SAFETY: `U16x2` and `[u16; 2]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U16x2` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut U16x2 as *mut [u16; 2]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [u16; 2] {
        // SAFETY: We know that `U16x2` and `[u16; 2]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`U16x2`] with all 2 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: u16) -> U16x2 {
        U16x2::from_array([value; 2])
    }

    /// Create a new [`U16x2`] from its [`u16`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(a: u16, b: u16) -> U16x2 {
        U16x2::from_array([a, b])
    }

    /// Create a new [`U16x2`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u32) -> U16x2 {
        U16x2(bits)
    }

    /// Create a reference to a [`U16x2`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u32) -> &U16x2 {
        // SAFETY: `U16x2` is a transparent wrapper over `u32`,
        //         so this is always safe.
        unsafe { &*(bits as *const u32 as *const U16x2) }
    }

    /// Create a mutable reference to a [`U16x2`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u32) -> &mut U16x2 {
        // SAFETY: `U16x2` is a transparent wrapper over `u32`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u32 as *mut U16x2) }
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
impl U16x2 {
    /// The size of this vector in bits (32-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::BITS, u32::BITS);
    /// assert_eq!(U16x2::BITS, 32);
    ///
    /// ```
    pub const BITS: u32 = u32::BITS;

    /// The size of this vector's lanes in bits (16-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::LANE_BITS, u16::BITS);
    /// assert_eq!(U16x2::LANE_BITS, 16);
    ///
    /// ```
    pub const LANE_BITS: u32 = u16::BITS;

    /// The amount of [`u16`] lanes (2) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::LANES, 2);
    /// assert_eq!(U16x2::LANES, size_of::<U16x2>() / size_of::<u16>());
    ///
    /// ```
    pub const LANES: usize = 2;

    /// A [`U16x2`] with all lanes set to [`u16::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::MAX.to_array(), [65535; 2]);
    ///
    /// ```
    pub const MAX: U16x2 = U16x2::splat(u16::MAX);

    /// A [`U16x2`] with all lanes set to [`u16::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::MIN.to_array(), [0; 2]);
    ///
    /// ```
    pub const MIN: U16x2 = U16x2::splat(u16::MIN);

    /// A [`U16x2`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::LSB.to_array(), [0x0001; 2]);
    ///
    /// ```
    pub const LSB: U16x2 = U16x2::splat(1 << 0);

    /// A [`U16x2`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::MSB.to_array(), [0x8000; 2]);
    ///
    /// ```
    pub const MSB: U16x2 = U16x2::splat(1 << (u16::BITS - 1));
}
/// A 64-bit SWAR vector containing 4 [`u16`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u64`], but is
/// treated as a `[u16; 4]`.
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
pub struct U16x4(
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

// We need to ensure that `U16x4` is the same size as `[u16; 4]`.
const _: () = {
    let vec = ::core::mem::size_of::<U16x4>();
    let lanes = ::core::mem::size_of::<[u16; 4]>();

    ::core::assert!(
        vec == lanes,
        "the size of `U16x4` must be equal to that of `[u16; 4]`"
    );
};

// We need to ensure that `U16x4` is sufficiently aligned for `[u16; 4]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<U16x4>();
    let lanes = ::core::mem::align_of::<[u16; 4]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `U16x4` is not sufficiently aligned for `[u16; 4]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl U16x4 {
    /// Create a new [`U16x4`] from an array of 4 [`u16`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [u16; 4]) -> U16x4 {
        // SAFETY: We know that `U16x4` and `[u16; 4]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[u16; 4] {
        // SAFETY: `U16x4` and `[u16; 4]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U16x4` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const U16x4 as *const [u16; 4]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [u16; 4] {
        // SAFETY: `U16x4` and `[u16; 4]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U16x4` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut U16x4 as *mut [u16; 4]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [u16; 4] {
        // SAFETY: We know that `U16x4` and `[u16; 4]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`U16x4`] with all 4 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: u16) -> U16x4 {
        U16x4::from_array([value; 4])
    }

    /// Create a new [`U16x4`] from its [`u16`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(a: u16, b: u16, c: u16, d: u16) -> U16x4 {
        U16x4::from_array([a, b, c, d])
    }

    /// Create a new [`U16x4`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u64) -> U16x4 {
        U16x4(bits)
    }

    /// Create a reference to a [`U16x4`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u64) -> &U16x4 {
        // SAFETY: `U16x4` is a transparent wrapper over `u64`,
        //         so this is always safe.
        unsafe { &*(bits as *const u64 as *const U16x4) }
    }

    /// Create a mutable reference to a [`U16x4`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u64) -> &mut U16x4 {
        // SAFETY: `U16x4` is a transparent wrapper over `u64`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u64 as *mut U16x4) }
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
impl U16x4 {
    /// The size of this vector in bits (64-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::BITS, u64::BITS);
    /// assert_eq!(U16x4::BITS, 64);
    ///
    /// ```
    pub const BITS: u32 = u64::BITS;

    /// The size of this vector's lanes in bits (16-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::LANE_BITS, u16::BITS);
    /// assert_eq!(U16x4::LANE_BITS, 16);
    ///
    /// ```
    pub const LANE_BITS: u32 = u16::BITS;

    /// The amount of [`u16`] lanes (4) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::LANES, 4);
    /// assert_eq!(U16x4::LANES, size_of::<U16x4>() / size_of::<u16>());
    ///
    /// ```
    pub const LANES: usize = 4;

    /// A [`U16x4`] with all lanes set to [`u16::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::MAX.to_array(), [65535; 4]);
    ///
    /// ```
    pub const MAX: U16x4 = U16x4::splat(u16::MAX);

    /// A [`U16x4`] with all lanes set to [`u16::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::MIN.to_array(), [0; 4]);
    ///
    /// ```
    pub const MIN: U16x4 = U16x4::splat(u16::MIN);

    /// A [`U16x4`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::LSB.to_array(), [0x0001; 4]);
    ///
    /// ```
    pub const LSB: U16x4 = U16x4::splat(1 << 0);

    /// A [`U16x4`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::MSB.to_array(), [0x8000; 4]);
    ///
    /// ```
    pub const MSB: U16x4 = U16x4::splat(1 << (u16::BITS - 1));
}
/// A 128-bit SWAR vector containing 8 [`u16`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u128`], but is
/// treated as a `[u16; 8]`.
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
pub struct U16x8(
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

// We need to ensure that `U16x8` is the same size as `[u16; 8]`.
const _: () = {
    let vec = ::core::mem::size_of::<U16x8>();
    let lanes = ::core::mem::size_of::<[u16; 8]>();

    ::core::assert!(
        vec == lanes,
        "the size of `U16x8` must be equal to that of `[u16; 8]`"
    );
};

// We need to ensure that `U16x8` is sufficiently aligned for `[u16; 8]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<U16x8>();
    let lanes = ::core::mem::align_of::<[u16; 8]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `U16x8` is not sufficiently aligned for `[u16; 8]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl U16x8 {
    /// Create a new [`U16x8`] from an array of 8 [`u16`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [u16; 8]) -> U16x8 {
        // SAFETY: We know that `U16x8` and `[u16; 8]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[u16; 8] {
        // SAFETY: `U16x8` and `[u16; 8]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U16x8` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const U16x8 as *const [u16; 8]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [u16; 8] {
        // SAFETY: `U16x8` and `[u16; 8]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U16x8` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut U16x8 as *mut [u16; 8]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [u16; 8] {
        // SAFETY: We know that `U16x8` and `[u16; 8]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`U16x8`] with all 8 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: u16) -> U16x8 {
        U16x8::from_array([value; 8])
    }

    /// Create a new [`U16x8`] from its [`u16`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(a: u16, b: u16, c: u16, d: u16, e: u16, f: u16, g: u16, h: u16) -> U16x8 {
        U16x8::from_array([a, b, c, d, e, f, g, h])
    }

    /// Create a new [`U16x8`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u128) -> U16x8 {
        U16x8(bits)
    }

    /// Create a reference to a [`U16x8`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u128) -> &U16x8 {
        // SAFETY: `U16x8` is a transparent wrapper over `u128`,
        //         so this is always safe.
        unsafe { &*(bits as *const u128 as *const U16x8) }
    }

    /// Create a mutable reference to a [`U16x8`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u128) -> &mut U16x8 {
        // SAFETY: `U16x8` is a transparent wrapper over `u128`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u128 as *mut U16x8) }
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
impl U16x8 {
    /// The size of this vector in bits (128-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::BITS, u128::BITS);
    /// assert_eq!(U16x8::BITS, 128);
    ///
    /// ```
    pub const BITS: u32 = u128::BITS;

    /// The size of this vector's lanes in bits (16-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::LANE_BITS, u16::BITS);
    /// assert_eq!(U16x8::LANE_BITS, 16);
    ///
    /// ```
    pub const LANE_BITS: u32 = u16::BITS;

    /// The amount of [`u16`] lanes (8) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::LANES, 8);
    /// assert_eq!(U16x8::LANES, size_of::<U16x8>() / size_of::<u16>());
    ///
    /// ```
    pub const LANES: usize = 8;

    /// A [`U16x8`] with all lanes set to [`u16::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::MAX.to_array(), [65535; 8]);
    ///
    /// ```
    pub const MAX: U16x8 = U16x8::splat(u16::MAX);

    /// A [`U16x8`] with all lanes set to [`u16::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::MIN.to_array(), [0; 8]);
    ///
    /// ```
    pub const MIN: U16x8 = U16x8::splat(u16::MIN);

    /// A [`U16x8`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::LSB.to_array(), [0x0001; 8]);
    ///
    /// ```
    pub const LSB: U16x8 = U16x8::splat(1 << 0);

    /// A [`U16x8`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::MSB.to_array(), [0x8000; 8]);
    ///
    /// ```
    pub const MSB: U16x8 = U16x8::splat(1 << (u16::BITS - 1));
}
