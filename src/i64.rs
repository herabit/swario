/// A 128-bit SWAR vector containing 2 [`i64`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u128`], but is
/// treated as a `[i64; 2]`.
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
pub struct I64x2(
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

// We need to ensure that `I64x2` is the same size as `[i64; 2]`.
const _: () = {
    let vec = ::core::mem::size_of::<I64x2>();
    let lanes = ::core::mem::size_of::<[i64; 2]>();

    ::core::assert!(
        vec == lanes,
        "the size of `I64x2` must be equal to that of `[i64; 2]`"
    );
};

// We need to ensure that `I64x2` is sufficiently aligned for `[i64; 2]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<I64x2>();
    let lanes = ::core::mem::align_of::<[i64; 2]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `I64x2` is not sufficiently aligned for `[i64; 2]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl I64x2 {
    /// Create a new [`I64x2`] from an array of 2 [`i64`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [i64; 2]) -> I64x2 {
        // SAFETY: We know that `I64x2` and `[i64; 2]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[i64; 2] {
        // SAFETY: `I64x2` and `[i64; 2]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I64x2` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const I64x2 as *const [i64; 2]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [i64; 2] {
        // SAFETY: `I64x2` and `[i64; 2]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `I64x2` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut I64x2 as *mut [i64; 2]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [i64; 2] {
        // SAFETY: We know that `I64x2` and `[i64; 2]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`I64x2`] with all 2 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: i64) -> I64x2 {
        I64x2::from_array([value; 2])
    }

    /// Create a new [`I64x2`] from its [`i64`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(a: i64, b: i64) -> I64x2 {
        I64x2::from_array([a, b])
    }

    /// Create a new [`I64x2`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u128) -> I64x2 {
        I64x2(bits)
    }

    /// Create a reference to a [`I64x2`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u128) -> &I64x2 {
        // SAFETY: `I64x2` is a transparent wrapper over `u128`,
        //         so this is always safe.
        unsafe { &*(bits as *const u128 as *const I64x2) }
    }

    /// Create a mutable reference to a [`I64x2`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u128) -> &mut I64x2 {
        // SAFETY: `I64x2` is a transparent wrapper over `u128`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u128 as *mut I64x2) }
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
impl I64x2 {
    /// The size of this vector in bits (128-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I64x2::BITS, u128::BITS);
    /// assert_eq!(I64x2::BITS, 128);
    ///
    /// ```
    pub const BITS: u32 = u128::BITS;

    /// The size of this vector's lanes in bits (64-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I64x2::LANE_BITS, i64::BITS);
    /// assert_eq!(I64x2::LANE_BITS, 64);
    ///
    /// ```
    pub const LANE_BITS: u32 = i64::BITS;

    /// The amount of [`i64`] lanes (2) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I64x2::LANES, 2);
    /// assert_eq!(I64x2::LANES, size_of::<I64x2>() / size_of::<i64>());
    ///
    /// ```
    pub const LANES: usize = 2;

    /// A [`I64x2`] with all lanes set to [`i64::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I64x2::MAX.to_array(), [9223372036854775807; 2]);
    ///
    /// ```
    pub const MAX: I64x2 = I64x2::splat(i64::MAX);

    /// A [`I64x2`] with all lanes set to [`i64::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I64x2::MIN.to_array(), [-9223372036854775808; 2]);
    ///
    /// ```
    pub const MIN: I64x2 = I64x2::splat(i64::MIN);

    /// A [`I64x2`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I64x2::LSB.to_array(), [0x0000000000000001; 2]);
    ///
    /// ```
    pub const LSB: I64x2 = I64x2::splat(1 << 0);

    /// A [`I64x2`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I64x2::MSB.to_array(), [0x8000000000000000_u64 as i64; 2]);
    ///
    /// ```
    pub const MSB: I64x2 = I64x2::splat(1 << (i64::BITS - 1));
}
