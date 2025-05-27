/// A 64-bit SWAR vector containing 2 [`i32`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u64`], but is
/// treated as a `[i32; 2]`.
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
pub struct I32x2(
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

// We need to ensure that `I32x2` is the same size as `[i32; 2]`.
const _: () = {
    let vec = ::core::mem::size_of::<I32x2>();
    let lanes = ::core::mem::size_of::<[i32; 2]>();

    ::core::assert!(
        vec == lanes,
        "the size of `I32x2` must be equal to that of `[i32; 2]`"
    );
};

// We need to ensure that `I32x2` is sufficiently aligned for `[i32; 2]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<I32x2>();
    let lanes = ::core::mem::align_of::<[i32; 2]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `I32x2` is not sufficiently aligned for `[i32; 2]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl I32x2 {
    /// Create a new [`I32x2`] from an array of 2 [`i32`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [i32; 2]) -> I32x2 {
        // SAFETY: We know that `I32x2` and `[i32; 2]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[i32; 2] {
        // SAFETY: `I32x2` and `[i32; 2]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I32x2` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const I32x2 as *const [i32; 2]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [i32; 2] {
        // SAFETY: `I32x2` and `[i32; 2]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I32x2` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut I32x2 as *mut [i32; 2]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [i32; 2] {
        // SAFETY: We know that `I32x2` and `[i32; 2]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`I32x2`] with all 2 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: i32) -> I32x2 {
        I32x2::from_array([value; 2])
    }

    /// Create a new [`I32x2`] from its [`i32`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(a: i32, b: i32) -> I32x2 {
        I32x2::from_array([a, b])
    }

    /// Create a new [`I32x2`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u64) -> I32x2 {
        I32x2(bits)
    }

    /// Create a reference to a [`I32x2`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u64) -> &I32x2 {
        // SAFETY: `I32x2` is a transparent wrapper over `u64`,
        //         so this is always safe.
        unsafe { &*(bits as *const u64 as *const I32x2) }
    }

    /// Create a mutable reference to a [`I32x2`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u64) -> &mut I32x2 {
        // SAFETY: `I32x2` is a transparent wrapper over `u64`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u64 as *mut I32x2) }
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
impl I32x2 {
    /// The size of this vector in bits (64-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::BITS, u64::BITS);
    /// assert_eq!(I32x2::BITS, 64);
    ///
    /// ```
    pub const BITS: u32 = u64::BITS;

    /// The size of this vector's lanes in bits (32-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::LANE_BITS, i32::BITS);
    /// assert_eq!(I32x2::LANE_BITS, 32);
    ///
    /// ```
    pub const LANE_BITS: u32 = i32::BITS;

    /// The amount of [`i32`] lanes (2) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::LANES, 2);
    /// assert_eq!(I32x2::LANES, size_of::<I32x2>() / size_of::<i32>());
    ///
    /// ```
    pub const LANES: usize = 2;

    /// A [`I32x2`] with all lanes set to [`i32::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::MAX.to_array(), [2147483647; 2]);
    ///
    /// ```
    pub const MAX: I32x2 = I32x2::splat(i32::MAX);

    /// A [`I32x2`] with all lanes set to [`i32::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::MIN.to_array(), [-2147483648; 2]);
    ///
    /// ```
    pub const MIN: I32x2 = I32x2::splat(i32::MIN);

    /// A [`I32x2`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::LSB.to_array(), [0x00000001; 2]);
    ///
    /// ```
    pub const LSB: I32x2 = I32x2::splat(1 << 0);

    /// A [`I32x2`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::MSB.to_array(), [0x80000000_u32 as i32; 2]);
    ///
    /// ```
    pub const MSB: I32x2 = I32x2::splat(1 << (i32::BITS - 1));
}
/// A 128-bit SWAR vector containing 4 [`i32`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u128`], but is
/// treated as a `[i32; 4]`.
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
pub struct I32x4(
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

// We need to ensure that `I32x4` is the same size as `[i32; 4]`.
const _: () = {
    let vec = ::core::mem::size_of::<I32x4>();
    let lanes = ::core::mem::size_of::<[i32; 4]>();

    ::core::assert!(
        vec == lanes,
        "the size of `I32x4` must be equal to that of `[i32; 4]`"
    );
};

// We need to ensure that `I32x4` is sufficiently aligned for `[i32; 4]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<I32x4>();
    let lanes = ::core::mem::align_of::<[i32; 4]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `I32x4` is not sufficiently aligned for `[i32; 4]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl I32x4 {
    /// Create a new [`I32x4`] from an array of 4 [`i32`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [i32; 4]) -> I32x4 {
        // SAFETY: We know that `I32x4` and `[i32; 4]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[i32; 4] {
        // SAFETY: `I32x4` and `[i32; 4]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I32x4` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const I32x4 as *const [i32; 4]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [i32; 4] {
        // SAFETY: `I32x4` and `[i32; 4]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I32x4` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut I32x4 as *mut [i32; 4]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [i32; 4] {
        // SAFETY: We know that `I32x4` and `[i32; 4]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`I32x4`] with all 4 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: i32) -> I32x4 {
        I32x4::from_array([value; 4])
    }

    /// Create a new [`I32x4`] from its [`i32`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(a: i32, b: i32, c: i32, d: i32) -> I32x4 {
        I32x4::from_array([a, b, c, d])
    }

    /// Create a new [`I32x4`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u128) -> I32x4 {
        I32x4(bits)
    }

    /// Create a reference to a [`I32x4`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u128) -> &I32x4 {
        // SAFETY: `I32x4` is a transparent wrapper over `u128`,
        //         so this is always safe.
        unsafe { &*(bits as *const u128 as *const I32x4) }
    }

    /// Create a mutable reference to a [`I32x4`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u128) -> &mut I32x4 {
        // SAFETY: `I32x4` is a transparent wrapper over `u128`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u128 as *mut I32x4) }
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
impl I32x4 {
    /// The size of this vector in bits (128-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::BITS, u128::BITS);
    /// assert_eq!(I32x4::BITS, 128);
    ///
    /// ```
    pub const BITS: u32 = u128::BITS;

    /// The size of this vector's lanes in bits (32-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::LANE_BITS, i32::BITS);
    /// assert_eq!(I32x4::LANE_BITS, 32);
    ///
    /// ```
    pub const LANE_BITS: u32 = i32::BITS;

    /// The amount of [`i32`] lanes (4) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::LANES, 4);
    /// assert_eq!(I32x4::LANES, size_of::<I32x4>() / size_of::<i32>());
    ///
    /// ```
    pub const LANES: usize = 4;

    /// A [`I32x4`] with all lanes set to [`i32::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::MAX.to_array(), [2147483647; 4]);
    ///
    /// ```
    pub const MAX: I32x4 = I32x4::splat(i32::MAX);

    /// A [`I32x4`] with all lanes set to [`i32::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::MIN.to_array(), [-2147483648; 4]);
    ///
    /// ```
    pub const MIN: I32x4 = I32x4::splat(i32::MIN);

    /// A [`I32x4`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::LSB.to_array(), [0x00000001; 4]);
    ///
    /// ```
    pub const LSB: I32x4 = I32x4::splat(1 << 0);

    /// A [`I32x4`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::MSB.to_array(), [0x80000000_u32 as i32; 4]);
    ///
    /// ```
    pub const MSB: I32x4 = I32x4::splat(1 << (i32::BITS - 1));
}
