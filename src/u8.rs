/// A 16-bit SWAR vector containing 2 [`u8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u16`], but is
/// treated as a `[u8; 2]`.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(
    feature = "bytemuck",
    derive(::bytemuck::Zeroable, ::bytemuck::Pod, ::bytemuck::TransparentWrapper)
)]
#[cfg_attr(
    feature = "zerocopy",
    derive(
        ::zerocopy::FromBytes,
        ::zerocopy::IntoBytes,
        ::zerocopy::KnownLayout,
        ::zerocopy::Immutable
    )
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

impl ::core::fmt::Debug for U8x2 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
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
    /// assert_eq!(U8x2::MAX, U8x2::splat(255));
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
    /// assert_eq!(U8x2::MIN, U8x2::splat(0));
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
    /// assert_eq!(U8x2::LSB, U8x2::splat(0x01_u8));
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
    /// assert_eq!(U8x2::MSB, U8x2::splat(0x80_u8));
    ///
    /// ```
    pub const MSB: U8x2 = U8x2::splat(1 << (u8::BITS - 1));

    /// A [`U8x2`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::ZERO, U8x2::splat(0));
    ///
    /// ```
    pub const ZERO: U8x2 = U8x2::splat(0);

    /// A [`U8x2`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::ONE, U8x2::splat(1));
    ///
    /// ```
    pub const ONE: U8x2 = U8x2::splat(1);
}
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
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x2::from_array([0x00, 0x01]);
    /// let after = U8x2::from_array([0x01, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> U8x2 {
        let n_bits = u8::BITS * (n % U8x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x2(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U8x2(self.0.rotate_left(n_bits))
        }
    }

    /// Rotates the vector by `n` lanes to the left.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x2::from_array([0x00, 0x01]);
    /// let after = U8x2::from_array([0x01, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> U8x2 {
        let n_bits = u8::BITS * (n % U8x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x2(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U8x2(self.0.rotate_right(n_bits))
        }
    }
}
impl U8x2 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x2::from_array([0x0A, 0x0B]);
    /// let after = U8x2::from_array([0x00, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> U8x2 {
        let n_bits = u8::BITS * (n % U8x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x2(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            U8x2(self.0 << n_bits)
        }
    }

    /// Shifts the vector by `n` lanes to the left.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x2::from_array([0x0A, 0x0B]);
    /// let after = U8x2::from_array([0x0B, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> U8x2 {
        let n_bits = u8::BITS * (n % U8x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x2(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            U8x2(self.0 >> n_bits)
        }
    }
}
impl U8x2 {
    /// Performs a bitwise NOT on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::splat(0x00).not(), U8x2::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> U8x2 {
        U8x2(!self.0)
    }

    /// Performs a bitwise OR on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::splat(0b01).or(U8x2::splat(0b10)), U8x2::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: U8x2) -> U8x2 {
        U8x2(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::splat(0b1101).and(U8x2::splat(0b0111)), U8x2::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: U8x2) -> U8x2 {
        U8x2(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::splat(0b1101).xor(U8x2::splat(0b0111)), U8x2::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: U8x2) -> U8x2 {
        U8x2(self.0 ^ rhs.0)
    }
}
impl U8x2 {
    /// Performs an unchecked left shift on every [`u8`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> U8x2 {
        // SAFETY: The caller ensures `n < 8`.
        unsafe { ::core::hint::assert_unchecked(n < u8::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask = !(0x8080_u16 >> u8::BITS - 1 - n).wrapping_sub(0x0101_u16);

        // Calculate the left shift.
        let shifted = self.0 << n;

        U8x2(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`u8`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> U8x2 {
        // SAFETY: The caller ensures `n < 8`.
        unsafe { ::core::hint::assert_unchecked(n < u8::BITS) };

        // Calculate the mask for the bits we want to keep.
        //
        // TODO: Figure out a way that is as quick as the mask calculation for `shl`.
        //
        //       According to LLVM-MCA, on Zen4 this seems to put undue stress on the ALU
        //       when doing the wrapping subtraction.
        //
        //       There *may* be a way around this, but I am unaware of how. Until I figure
        //       that out, this seems to be the fastest way of calculating the mask.
        let mask = (0x0202_u16 << u8::BITS - 1 - n).wrapping_sub(0x0101_u16);

        // Perform a logical right shift.
        U8x2((self.0 >> n) & mask)
    }

    /// Performs a wrapping left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::splat(0b01).wrapping_shl(1), U8x2::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> U8x2 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (u8::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::splat(0b10).wrapping_shr(1), U8x2::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> U8x2 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (u8::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::splat(0b001).overflowing_shl(2), (U8x2::splat(0b100), false));
    /// assert_eq!(U8x2::splat(0b001).overflowing_shl(8), (U8x2::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (U8x2, bool) {
        (self.wrapping_shl(n), n >= u8::BITS)
    }

    /// Performs an overflowing right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::splat(0b100).overflowing_shr(2), (U8x2::splat(0b001), false));
    /// assert_eq!(U8x2::splat(0b100).overflowing_shr(8), (U8x2::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (U8x2, bool) {
        (self.wrapping_shr(n), n >= u8::BITS)
    }

    /// Performs a checked left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::splat(0b001).checked_shl(2), Some(U8x2::splat(0b100)));
    /// assert_eq!(U8x2::splat(0b001).checked_shl(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<U8x2> {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::splat(0b100).checked_shr(2), Some(U8x2::splat(0b001)));
    /// assert_eq!(U8x2::splat(0b100).checked_shr(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<U8x2> {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::splat(0b001).unbounded_shl(2), U8x2::splat(0b100));
    /// assert_eq!(U8x2::splat(0b001).unbounded_shl(8), U8x2::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> U8x2 {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            U8x2::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x2::splat(0b100).unbounded_shr(2), U8x2::splat(0b001));
    /// assert_eq!(U8x2::splat(0b100).unbounded_shr(8), U8x2::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> U8x2 {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            U8x2::splat(0)
        }
    }
}
/// A 32-bit SWAR vector containing 4 [`u8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u32`], but is
/// treated as a `[u8; 4]`.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(
    feature = "bytemuck",
    derive(::bytemuck::Zeroable, ::bytemuck::Pod, ::bytemuck::TransparentWrapper)
)]
#[cfg_attr(
    feature = "zerocopy",
    derive(
        ::zerocopy::FromBytes,
        ::zerocopy::IntoBytes,
        ::zerocopy::KnownLayout,
        ::zerocopy::Immutable
    )
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

impl ::core::fmt::Debug for U8x4 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
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
    /// assert_eq!(U8x4::MAX, U8x4::splat(255));
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
    /// assert_eq!(U8x4::MIN, U8x4::splat(0));
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
    /// assert_eq!(U8x4::LSB, U8x4::splat(0x01_u8));
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
    /// assert_eq!(U8x4::MSB, U8x4::splat(0x80_u8));
    ///
    /// ```
    pub const MSB: U8x4 = U8x4::splat(1 << (u8::BITS - 1));

    /// A [`U8x4`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::ZERO, U8x4::splat(0));
    ///
    /// ```
    pub const ZERO: U8x4 = U8x4::splat(0);

    /// A [`U8x4`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::ONE, U8x4::splat(1));
    ///
    /// ```
    pub const ONE: U8x4 = U8x4::splat(1);
}
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
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x4::from_array([0x00, 0x01, 0x02, 0x03]);
    /// let after = U8x4::from_array([0x03, 0x00, 0x01, 0x02]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> U8x4 {
        let n_bits = u8::BITS * (n % U8x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x4(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U8x4(self.0.rotate_left(n_bits))
        }
    }

    /// Rotates the vector by `n` lanes to the left.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x4::from_array([0x00, 0x01, 0x02, 0x03]);
    /// let after = U8x4::from_array([0x01, 0x02, 0x03, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> U8x4 {
        let n_bits = u8::BITS * (n % U8x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x4(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U8x4(self.0.rotate_right(n_bits))
        }
    }
}
impl U8x4 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x4::from_array([0x0A, 0x0A, 0x0B, 0x0B]);
    /// let after = U8x4::from_array([0x00, 0x00, 0x0A, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(2), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> U8x4 {
        let n_bits = u8::BITS * (n % U8x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x4(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            U8x4(self.0 << n_bits)
        }
    }

    /// Shifts the vector by `n` lanes to the left.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x4::from_array([0x0A, 0x0A, 0x0B, 0x0B]);
    /// let after = U8x4::from_array([0x0B, 0x0B, 0x00, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(2), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> U8x4 {
        let n_bits = u8::BITS * (n % U8x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x4(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            U8x4(self.0 >> n_bits)
        }
    }
}
impl U8x4 {
    /// Performs a bitwise NOT on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::splat(0x00).not(), U8x4::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> U8x4 {
        U8x4(!self.0)
    }

    /// Performs a bitwise OR on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::splat(0b01).or(U8x4::splat(0b10)), U8x4::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: U8x4) -> U8x4 {
        U8x4(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::splat(0b1101).and(U8x4::splat(0b0111)), U8x4::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: U8x4) -> U8x4 {
        U8x4(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::splat(0b1101).xor(U8x4::splat(0b0111)), U8x4::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: U8x4) -> U8x4 {
        U8x4(self.0 ^ rhs.0)
    }
}
impl U8x4 {
    /// Performs an unchecked left shift on every [`u8`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> U8x4 {
        // SAFETY: The caller ensures `n < 8`.
        unsafe { ::core::hint::assert_unchecked(n < u8::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask = !(0x80808080_u32 >> u8::BITS - 1 - n).wrapping_sub(0x01010101_u32);

        // Calculate the left shift.
        let shifted = self.0 << n;

        U8x4(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`u8`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> U8x4 {
        // SAFETY: The caller ensures `n < 8`.
        unsafe { ::core::hint::assert_unchecked(n < u8::BITS) };

        // Calculate the mask for the bits we want to keep.
        //
        // TODO: Figure out a way that is as quick as the mask calculation for `shl`.
        //
        //       According to LLVM-MCA, on Zen4 this seems to put undue stress on the ALU
        //       when doing the wrapping subtraction.
        //
        //       There *may* be a way around this, but I am unaware of how. Until I figure
        //       that out, this seems to be the fastest way of calculating the mask.
        let mask = (0x02020202_u32 << u8::BITS - 1 - n).wrapping_sub(0x01010101_u32);

        // Perform a logical right shift.
        U8x4((self.0 >> n) & mask)
    }

    /// Performs a wrapping left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::splat(0b01).wrapping_shl(1), U8x4::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> U8x4 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (u8::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::splat(0b10).wrapping_shr(1), U8x4::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> U8x4 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (u8::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::splat(0b001).overflowing_shl(2), (U8x4::splat(0b100), false));
    /// assert_eq!(U8x4::splat(0b001).overflowing_shl(8), (U8x4::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (U8x4, bool) {
        (self.wrapping_shl(n), n >= u8::BITS)
    }

    /// Performs an overflowing right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::splat(0b100).overflowing_shr(2), (U8x4::splat(0b001), false));
    /// assert_eq!(U8x4::splat(0b100).overflowing_shr(8), (U8x4::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (U8x4, bool) {
        (self.wrapping_shr(n), n >= u8::BITS)
    }

    /// Performs a checked left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::splat(0b001).checked_shl(2), Some(U8x4::splat(0b100)));
    /// assert_eq!(U8x4::splat(0b001).checked_shl(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<U8x4> {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::splat(0b100).checked_shr(2), Some(U8x4::splat(0b001)));
    /// assert_eq!(U8x4::splat(0b100).checked_shr(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<U8x4> {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::splat(0b001).unbounded_shl(2), U8x4::splat(0b100));
    /// assert_eq!(U8x4::splat(0b001).unbounded_shl(8), U8x4::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> U8x4 {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            U8x4::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x4::splat(0b100).unbounded_shr(2), U8x4::splat(0b001));
    /// assert_eq!(U8x4::splat(0b100).unbounded_shr(8), U8x4::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> U8x4 {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            U8x4::splat(0)
        }
    }
}
/// A 64-bit SWAR vector containing 8 [`u8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u64`], but is
/// treated as a `[u8; 8]`.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(
    feature = "bytemuck",
    derive(::bytemuck::Zeroable, ::bytemuck::Pod, ::bytemuck::TransparentWrapper)
)]
#[cfg_attr(
    feature = "zerocopy",
    derive(
        ::zerocopy::FromBytes,
        ::zerocopy::IntoBytes,
        ::zerocopy::KnownLayout,
        ::zerocopy::Immutable
    )
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

impl ::core::fmt::Debug for U8x8 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
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
    /// assert_eq!(U8x8::MAX, U8x8::splat(255));
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
    /// assert_eq!(U8x8::MIN, U8x8::splat(0));
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
    /// assert_eq!(U8x8::LSB, U8x8::splat(0x01_u8));
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
    /// assert_eq!(U8x8::MSB, U8x8::splat(0x80_u8));
    ///
    /// ```
    pub const MSB: U8x8 = U8x8::splat(1 << (u8::BITS - 1));

    /// A [`U8x8`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::ZERO, U8x8::splat(0));
    ///
    /// ```
    pub const ZERO: U8x8 = U8x8::splat(0);

    /// A [`U8x8`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::ONE, U8x8::splat(1));
    ///
    /// ```
    pub const ONE: U8x8 = U8x8::splat(1);
}
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
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x8::from_array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]);
    /// let after = U8x8::from_array([0x07, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> U8x8 {
        let n_bits = u8::BITS * (n % U8x8::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x8(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U8x8(self.0.rotate_left(n_bits))
        }
    }

    /// Rotates the vector by `n` lanes to the left.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x8::from_array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]);
    /// let after = U8x8::from_array([0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> U8x8 {
        let n_bits = u8::BITS * (n % U8x8::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x8(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U8x8(self.0.rotate_right(n_bits))
        }
    }
}
impl U8x8 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x8::from_array([0x0A, 0x0A, 0x0A, 0x0A, 0x0B, 0x0B, 0x0B, 0x0B]);
    /// let after = U8x8::from_array([0x00, 0x00, 0x00, 0x00, 0x0A, 0x0A, 0x0A, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(4), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> U8x8 {
        let n_bits = u8::BITS * (n % U8x8::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x8(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            U8x8(self.0 << n_bits)
        }
    }

    /// Shifts the vector by `n` lanes to the left.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x8::from_array([0x0A, 0x0A, 0x0A, 0x0A, 0x0B, 0x0B, 0x0B, 0x0B]);
    /// let after = U8x8::from_array([0x0B, 0x0B, 0x0B, 0x0B, 0x00, 0x00, 0x00, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(4), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> U8x8 {
        let n_bits = u8::BITS * (n % U8x8::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x8(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            U8x8(self.0 >> n_bits)
        }
    }
}
impl U8x8 {
    /// Performs a bitwise NOT on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::splat(0x00).not(), U8x8::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> U8x8 {
        U8x8(!self.0)
    }

    /// Performs a bitwise OR on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::splat(0b01).or(U8x8::splat(0b10)), U8x8::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: U8x8) -> U8x8 {
        U8x8(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::splat(0b1101).and(U8x8::splat(0b0111)), U8x8::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: U8x8) -> U8x8 {
        U8x8(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::splat(0b1101).xor(U8x8::splat(0b0111)), U8x8::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: U8x8) -> U8x8 {
        U8x8(self.0 ^ rhs.0)
    }
}
impl U8x8 {
    /// Performs an unchecked left shift on every [`u8`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> U8x8 {
        // SAFETY: The caller ensures `n < 8`.
        unsafe { ::core::hint::assert_unchecked(n < u8::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask =
            !(0x8080808080808080_u64 >> u8::BITS - 1 - n).wrapping_sub(0x0101010101010101_u64);

        // Calculate the left shift.
        let shifted = self.0 << n;

        U8x8(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`u8`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> U8x8 {
        // SAFETY: The caller ensures `n < 8`.
        unsafe { ::core::hint::assert_unchecked(n < u8::BITS) };

        // Calculate the mask for the bits we want to keep.
        //
        // TODO: Figure out a way that is as quick as the mask calculation for `shl`.
        //
        //       According to LLVM-MCA, on Zen4 this seems to put undue stress on the ALU
        //       when doing the wrapping subtraction.
        //
        //       There *may* be a way around this, but I am unaware of how. Until I figure
        //       that out, this seems to be the fastest way of calculating the mask.
        let mask =
            (0x0202020202020202_u64 << u8::BITS - 1 - n).wrapping_sub(0x0101010101010101_u64);

        // Perform a logical right shift.
        U8x8((self.0 >> n) & mask)
    }

    /// Performs a wrapping left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::splat(0b01).wrapping_shl(1), U8x8::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> U8x8 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (u8::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::splat(0b10).wrapping_shr(1), U8x8::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> U8x8 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (u8::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::splat(0b001).overflowing_shl(2), (U8x8::splat(0b100), false));
    /// assert_eq!(U8x8::splat(0b001).overflowing_shl(8), (U8x8::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (U8x8, bool) {
        (self.wrapping_shl(n), n >= u8::BITS)
    }

    /// Performs an overflowing right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::splat(0b100).overflowing_shr(2), (U8x8::splat(0b001), false));
    /// assert_eq!(U8x8::splat(0b100).overflowing_shr(8), (U8x8::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (U8x8, bool) {
        (self.wrapping_shr(n), n >= u8::BITS)
    }

    /// Performs a checked left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::splat(0b001).checked_shl(2), Some(U8x8::splat(0b100)));
    /// assert_eq!(U8x8::splat(0b001).checked_shl(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<U8x8> {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::splat(0b100).checked_shr(2), Some(U8x8::splat(0b001)));
    /// assert_eq!(U8x8::splat(0b100).checked_shr(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<U8x8> {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::splat(0b001).unbounded_shl(2), U8x8::splat(0b100));
    /// assert_eq!(U8x8::splat(0b001).unbounded_shl(8), U8x8::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> U8x8 {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            U8x8::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x8::splat(0b100).unbounded_shr(2), U8x8::splat(0b001));
    /// assert_eq!(U8x8::splat(0b100).unbounded_shr(8), U8x8::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> U8x8 {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            U8x8::splat(0)
        }
    }
}
/// A 128-bit SWAR vector containing 16 [`u8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u128`], but is
/// treated as a `[u8; 16]`.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(
    feature = "bytemuck",
    derive(::bytemuck::Zeroable, ::bytemuck::Pod, ::bytemuck::TransparentWrapper)
)]
#[cfg_attr(
    feature = "zerocopy",
    derive(
        ::zerocopy::FromBytes,
        ::zerocopy::IntoBytes,
        ::zerocopy::KnownLayout,
        ::zerocopy::Immutable
    )
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

impl ::core::fmt::Debug for U8x16 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
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
    /// assert_eq!(U8x16::MAX, U8x16::splat(255));
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
    /// assert_eq!(U8x16::MIN, U8x16::splat(0));
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
    /// assert_eq!(U8x16::LSB, U8x16::splat(0x01_u8));
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
    /// assert_eq!(U8x16::MSB, U8x16::splat(0x80_u8));
    ///
    /// ```
    pub const MSB: U8x16 = U8x16::splat(1 << (u8::BITS - 1));

    /// A [`U8x16`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::ZERO, U8x16::splat(0));
    ///
    /// ```
    pub const ZERO: U8x16 = U8x16::splat(0);

    /// A [`U8x16`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::ONE, U8x16::splat(1));
    ///
    /// ```
    pub const ONE: U8x16 = U8x16::splat(1);
}
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
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x16::from_array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F]);
    /// let after = U8x16::from_array([0x0F, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> U8x16 {
        let n_bits = u8::BITS * (n % U8x16::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x16(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U8x16(self.0.rotate_left(n_bits))
        }
    }

    /// Rotates the vector by `n` lanes to the left.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x16::from_array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F]);
    /// let after = U8x16::from_array([0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> U8x16 {
        let n_bits = u8::BITS * (n % U8x16::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x16(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U8x16(self.0.rotate_right(n_bits))
        }
    }
}
impl U8x16 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x16::from_array([0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B]);
    /// let after = U8x16::from_array([0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(8), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> U8x16 {
        let n_bits = u8::BITS * (n % U8x16::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x16(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            U8x16(self.0 << n_bits)
        }
    }

    /// Shifts the vector by `n` lanes to the left.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U8x16::from_array([0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B]);
    /// let after = U8x16::from_array([0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(8), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> U8x16 {
        let n_bits = u8::BITS * (n % U8x16::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U8x16(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            U8x16(self.0 >> n_bits)
        }
    }
}
impl U8x16 {
    /// Performs a bitwise NOT on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::splat(0x00).not(), U8x16::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> U8x16 {
        U8x16(!self.0)
    }

    /// Performs a bitwise OR on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::splat(0b01).or(U8x16::splat(0b10)), U8x16::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: U8x16) -> U8x16 {
        U8x16(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::splat(0b1101).and(U8x16::splat(0b0111)), U8x16::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: U8x16) -> U8x16 {
        U8x16(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::splat(0b1101).xor(U8x16::splat(0b0111)), U8x16::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: U8x16) -> U8x16 {
        U8x16(self.0 ^ rhs.0)
    }
}
impl U8x16 {
    /// Performs an unchecked left shift on every [`u8`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> U8x16 {
        // SAFETY: The caller ensures `n < 8`.
        unsafe { ::core::hint::assert_unchecked(n < u8::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask = !(0x80808080808080808080808080808080_u128 >> u8::BITS - 1 - n)
            .wrapping_sub(0x01010101010101010101010101010101_u128);

        // Calculate the left shift.
        let shifted = self.0 << n;

        U8x16(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`u8`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> U8x16 {
        // SAFETY: The caller ensures `n < 8`.
        unsafe { ::core::hint::assert_unchecked(n < u8::BITS) };

        // Calculate the mask for the bits we want to keep.
        //
        // TODO: Figure out a way that is as quick as the mask calculation for `shl`.
        //
        //       According to LLVM-MCA, on Zen4 this seems to put undue stress on the ALU
        //       when doing the wrapping subtraction.
        //
        //       There *may* be a way around this, but I am unaware of how. Until I figure
        //       that out, this seems to be the fastest way of calculating the mask.
        let mask = (0x02020202020202020202020202020202_u128 << u8::BITS - 1 - n)
            .wrapping_sub(0x01010101010101010101010101010101_u128);

        // Perform a logical right shift.
        U8x16((self.0 >> n) & mask)
    }

    /// Performs a wrapping left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::splat(0b01).wrapping_shl(1), U8x16::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> U8x16 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (u8::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::splat(0b10).wrapping_shr(1), U8x16::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> U8x16 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (u8::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::splat(0b001).overflowing_shl(2), (U8x16::splat(0b100), false));
    /// assert_eq!(U8x16::splat(0b001).overflowing_shl(8), (U8x16::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (U8x16, bool) {
        (self.wrapping_shl(n), n >= u8::BITS)
    }

    /// Performs an overflowing right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::splat(0b100).overflowing_shr(2), (U8x16::splat(0b001), false));
    /// assert_eq!(U8x16::splat(0b100).overflowing_shr(8), (U8x16::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (U8x16, bool) {
        (self.wrapping_shr(n), n >= u8::BITS)
    }

    /// Performs a checked left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::splat(0b001).checked_shl(2), Some(U8x16::splat(0b100)));
    /// assert_eq!(U8x16::splat(0b001).checked_shl(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<U8x16> {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::splat(0b100).checked_shr(2), Some(U8x16::splat(0b001)));
    /// assert_eq!(U8x16::splat(0b100).checked_shr(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<U8x16> {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::splat(0b001).unbounded_shl(2), U8x16::splat(0b100));
    /// assert_eq!(U8x16::splat(0b001).unbounded_shl(8), U8x16::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> U8x16 {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            U8x16::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`u8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U8x16::splat(0b100).unbounded_shr(2), U8x16::splat(0b001));
    /// assert_eq!(U8x16::splat(0b100).unbounded_shr(8), U8x16::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> U8x16 {
        if n < u8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            U8x16::splat(0)
        }
    }
}
