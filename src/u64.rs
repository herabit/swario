/// A 128-bit SWAR vector containing 2 [`u64`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u128`], but is
/// treated as a `[u64; 2]`.
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
pub struct U64x2(
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

// We need to ensure that `U64x2` is the same size as `[u64; 2]`.
const _: () = {
    let vec = ::core::mem::size_of::<U64x2>();
    let lanes = ::core::mem::size_of::<[u64; 2]>();

    ::core::assert!(
        vec == lanes,
        "the size of `U64x2` must be equal to that of `[u64; 2]`"
    );
};

// We need to ensure that `U64x2` is sufficiently aligned for `[u64; 2]`.
//
// It almost certainly is, however it's still good to catch platforms that, for whatever
// reason decided to do the insane.
const _: () = {
    let vec = ::core::mem::align_of::<U64x2>();
    let lanes = ::core::mem::align_of::<[u64; 2]>();

    ::core::assert!(
        vec >= lanes,
        "the alignment of `U64x2` is not sufficiently aligned for `[u64; 2]`.\n\nThis indicates that the platform you're trying to compile for is esoteric to the point that it is simply just not worth supporting."
    );
};

impl ::core::fmt::Debug for U64x2 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
    }
}

impl U64x2 {
    /// The size of this vector in bits (128-bit).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::BITS, u128::BITS);
    /// assert_eq!(U64x2::BITS, 128);
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
    /// assert_eq!(U64x2::LANE_BITS, u64::BITS);
    /// assert_eq!(U64x2::LANE_BITS, 64);
    ///
    /// ```
    pub const LANE_BITS: u32 = u64::BITS;

    /// The amount of [`u64`] lanes (2) this vector contains.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::LANES, 2);
    /// assert_eq!(U64x2::LANES, size_of::<U64x2>() / size_of::<u64>());
    ///
    /// ```
    pub const LANES: usize = 2;

    /// A [`U64x2`] with all lanes set to [`u64::MAX`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::MAX, U64x2::splat(18446744073709551615));
    ///
    /// ```
    pub const MAX: U64x2 = U64x2::splat(u64::MAX);

    /// A [`U64x2`] with all lanes set to [`u64::MIN`].
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::MIN, U64x2::splat(0));
    ///
    /// ```
    pub const MIN: U64x2 = U64x2::splat(u64::MIN);

    /// A [`U64x2`] with all lanes set to their least significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::LSB, U64x2::splat(0x0000000000000001_u64));
    ///
    /// ```
    pub const LSB: U64x2 = U64x2::splat(1 << 0);

    /// A [`U64x2`] with all lanes set to their most significant bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::MSB, U64x2::splat(0x8000000000000000_u64));
    ///
    /// ```
    pub const MSB: U64x2 = U64x2::splat(1 << (u64::BITS - 1));

    /// A [`U64x2`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::ZERO, U64x2::splat(0));
    ///
    /// ```
    pub const ZERO: U64x2 = U64x2::splat(0);

    /// A [`U64x2`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::ONE, U64x2::splat(1));
    ///
    /// ```
    pub const ONE: U64x2 = U64x2::splat(1);
}
impl U64x2 {
    /// Create a new [`U64x2`] from an array of 2 [`u64`]s.
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [u64; 2]) -> U64x2 {
        // SAFETY: We know that `U64x2` and `[u64; 2]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(arr) }
    }

    /// Get a reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array(&self) -> &[u64; 2] {
        // SAFETY: `U64x2` and `[u64; 2]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U64x2` is not sufficiently
        //         aligned, somehow.
        unsafe { &*(self as *const U64x2 as *const [u64; 2]) }
    }

    /// Get a mutable reference to the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn as_array_mut(&mut self) -> &mut [u64; 2] {
        // SAFETY: `U64x2` and `[u64; 2]` are POD,
        //         and have the same size, and we cause a
        //         compile-time error if `U64x2` is not sufficiently
        //         aligned, somehow.
        unsafe { &mut *(self as *mut U64x2 as *mut [u64; 2]) }
    }

    /// Get the underlying lanes as an array.
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [u64; 2] {
        // SAFETY: We know that `U64x2` and `[u64; 2]` are POD,
        //         and have the same size.
        unsafe { ::core::mem::transmute(self) }
    }

    /// Create a new [`U64x2`] with all 2 lanes set to `value`.
    #[inline(always)]
    #[must_use]
    pub const fn splat(value: u64) -> U64x2 {
        U64x2::from_array([value; 2])
    }

    /// Create a new [`U64x2`] from its [`u64`] lanes.
    #[inline(always)]
    #[must_use]
    pub const fn new(a: u64, b: u64) -> U64x2 {
        U64x2::from_array([a, b])
    }

    /// Create a new [`U64x2`] from its underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits(bits: u128) -> U64x2 {
        U64x2(bits)
    }

    /// Create a reference to a [`U64x2`] from a reference to its underlying
    /// bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_ref(bits: &u128) -> &U64x2 {
        // SAFETY: `U64x2` is a transparent wrapper over `u128`,
        //         so this is always safe.
        unsafe { &*(bits as *const u128 as *const U64x2) }
    }

    /// Create a mutable reference to a [`U64x2`] from a mutable reference to its
    /// underlying bit representation.
    #[inline(always)]
    #[must_use]
    pub const fn from_bits_mut(bits: &mut u128) -> &mut U64x2 {
        // SAFETY: `U64x2` is a transparent wrapper over `u128`,
        //         so this is always safe.
        unsafe { &mut *(bits as *mut u128 as *mut U64x2) }
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
impl U64x2 {
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U64x2::from_array([0x00, 0x01]);
    /// let after = U64x2::from_array([0x01, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> U64x2 {
        let n_bits = u64::BITS * (n % U64x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U64x2(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U64x2(self.0.rotate_left(n_bits))
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
    /// let before = U64x2::from_array([0x00, 0x01]);
    /// let after = U64x2::from_array([0x01, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> U64x2 {
        let n_bits = u64::BITS * (n % U64x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U64x2(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U64x2(self.0.rotate_right(n_bits))
        }
    }
}
impl U64x2 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U64x2::from_array([0x0A, 0x0B]);
    /// let after = U64x2::from_array([0x00, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> U64x2 {
        let n_bits = u64::BITS * (n % U64x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U64x2(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            U64x2(self.0 << n_bits)
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
    /// let before = U64x2::from_array([0x0A, 0x0B]);
    /// let after = U64x2::from_array([0x0B, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> U64x2 {
        let n_bits = u64::BITS * (n % U64x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U64x2(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            U64x2(self.0 >> n_bits)
        }
    }
}
impl U64x2 {
    /// Performs a bitwise NOT on each [`u64`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::splat(0x00).not(), U64x2::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> U64x2 {
        U64x2(!self.0)
    }

    /// Performs a bitwise OR on each [`u64`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::splat(0b01).or(U64x2::splat(0b10)), U64x2::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: U64x2) -> U64x2 {
        U64x2(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`u64`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::splat(0b1101).and(U64x2::splat(0b0111)), U64x2::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: U64x2) -> U64x2 {
        U64x2(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`u64`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::splat(0b1101).xor(U64x2::splat(0b0111)), U64x2::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: U64x2) -> U64x2 {
        U64x2(self.0 ^ rhs.0)
    }
}
impl U64x2 {
    /// Performs an unchecked left shift on every [`u64`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 64`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> U64x2 {
        // SAFETY: The caller ensures `n < 64`.
        unsafe { ::core::hint::assert_unchecked(n < u64::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask = !(0x80000000000000008000000000000000_u128 >> u64::BITS - 1 - n)
            .wrapping_sub(0x00000000000000010000000000000001_u128);

        // Calculate the left shift.
        let shifted = self.0 << n;

        U64x2(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`u64`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 64`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> U64x2 {
        // SAFETY: The caller ensures `n < 64`.
        unsafe { ::core::hint::assert_unchecked(n < u64::BITS) };

        // Calculate the mask for the bits we want to keep.
        //
        // TODO: Figure out a way that is as quick as the mask calculation for `shl`.
        //
        //       According to LLVM-MCA, on Zen4 this seems to put undue stress on the ALU
        //       when doing the wrapping subtraction.
        //
        //       There *may* be a way around this, but I am unaware of how. Until I figure
        //       that out, this seems to be the fastest way of calculating the mask.
        let mask = (0x00000000000000020000000000000002_u128 << u64::BITS - 1 - n)
            .wrapping_sub(0x00000000000000010000000000000001_u128);

        // Perform a logical right shift.
        U64x2((self.0 >> n) & mask)
    }

    /// Performs a wrapping left shift on every [`u64`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::splat(0b01).wrapping_shl(1), U64x2::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> U64x2 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (u64::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`u64`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::splat(0b10).wrapping_shr(1), U64x2::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> U64x2 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (u64::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`u64`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::splat(0b001).overflowing_shl(2), (U64x2::splat(0b100), false));
    /// assert_eq!(U64x2::splat(0b001).overflowing_shl(64), (U64x2::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (U64x2, bool) {
        (self.wrapping_shl(n), n >= u64::BITS)
    }

    /// Performs an overflowing right shift on every [`u64`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::splat(0b100).overflowing_shr(2), (U64x2::splat(0b001), false));
    /// assert_eq!(U64x2::splat(0b100).overflowing_shr(64), (U64x2::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (U64x2, bool) {
        (self.wrapping_shr(n), n >= u64::BITS)
    }

    /// Performs a checked left shift on every [`u64`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::splat(0b001).checked_shl(2), Some(U64x2::splat(0b100)));
    /// assert_eq!(U64x2::splat(0b001).checked_shl(64), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<U64x2> {
        if n < u64::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`u64`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::splat(0b100).checked_shr(2), Some(U64x2::splat(0b001)));
    /// assert_eq!(U64x2::splat(0b100).checked_shr(64), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<U64x2> {
        if n < u64::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`u64`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::splat(0b001).unbounded_shl(2), U64x2::splat(0b100));
    /// assert_eq!(U64x2::splat(0b001).unbounded_shl(64), U64x2::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> U64x2 {
        if n < u64::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            U64x2::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`u64`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U64x2::splat(0b100).unbounded_shr(2), U64x2::splat(0b001));
    /// assert_eq!(U64x2::splat(0b100).unbounded_shr(64), U64x2::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> U64x2 {
        if n < u64::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            U64x2::splat(0)
        }
    }
}
