/// A 32-bit SWAR vector containing 2 [`u16`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u32`], but is
/// treated as a `[u16; 2]`.
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

impl ::core::fmt::Debug for U16x2 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
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
    /// assert_eq!(U16x2::MAX, U16x2::splat(65535));
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
    /// assert_eq!(U16x2::MIN, U16x2::splat(0));
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
    /// assert_eq!(U16x2::LSB, U16x2::splat(0x0001_u16));
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
    /// assert_eq!(U16x2::MSB, U16x2::splat(0x8000_u16));
    ///
    /// ```
    pub const MSB: U16x2 = U16x2::splat(1 << (u16::BITS - 1));

    /// A [`U16x2`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::ZERO, U16x2::splat(0));
    ///
    /// ```
    pub const ZERO: U16x2 = U16x2::splat(0);

    /// A [`U16x2`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::ONE, U16x2::splat(1));
    ///
    /// ```
    pub const ONE: U16x2 = U16x2::splat(1);
}
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
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U16x2::from_array([0x00, 0x01]);
    /// let after = U16x2::from_array([0x01, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> U16x2 {
        let n_bits = u16::BITS * (n % U16x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U16x2(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U16x2(self.0.rotate_left(n_bits))
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
    /// let before = U16x2::from_array([0x00, 0x01]);
    /// let after = U16x2::from_array([0x01, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> U16x2 {
        let n_bits = u16::BITS * (n % U16x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U16x2(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U16x2(self.0.rotate_right(n_bits))
        }
    }
}
impl U16x2 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U16x2::from_array([0x0A, 0x0B]);
    /// let after = U16x2::from_array([0x00, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> U16x2 {
        let n_bits = u16::BITS * (n % U16x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U16x2(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            U16x2(self.0 << n_bits)
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
    /// let before = U16x2::from_array([0x0A, 0x0B]);
    /// let after = U16x2::from_array([0x0B, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> U16x2 {
        let n_bits = u16::BITS * (n % U16x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U16x2(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            U16x2(self.0 >> n_bits)
        }
    }
}
impl U16x2 {
    /// Performs a bitwise NOT on each [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::splat(0x00).not(), U16x2::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> U16x2 {
        U16x2(!self.0)
    }

    /// Performs a bitwise OR on each [`u16`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::splat(0b01).or(U16x2::splat(0b10)), U16x2::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: U16x2) -> U16x2 {
        U16x2(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`u16`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::splat(0b1101).and(U16x2::splat(0b0111)), U16x2::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: U16x2) -> U16x2 {
        U16x2(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`u16`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::splat(0b1101).xor(U16x2::splat(0b0111)), U16x2::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: U16x2) -> U16x2 {
        U16x2(self.0 ^ rhs.0)
    }
}
impl U16x2 {
    /// Performs an unchecked left shift on every [`u16`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 16`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> U16x2 {
        // SAFETY: The caller ensures `n < 16`.
        unsafe { ::core::hint::assert_unchecked(n < u16::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask = !(0x80008000_u32 >> u16::BITS - 1 - n).wrapping_sub(0x00010001_u32);

        // Calculate the left shift.
        let shifted = self.0 << n;

        U16x2(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`u16`] lane by `n` bits.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 16`.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> U16x2 {
        // NOTE: `n` is a [`u32`] mainly to maintain parity with the Rust standard library. All of the
        //       right shift methods on [`u16`]s accept a [`u32`] as an argument.
        //
        //       Even though we know that `n` could definitely fit within a byte, this is just easier
        //       for consumers of the library. API consistency.

        // SAFETY: The caller ensures `n < 16`. This permits the omission of
        //         UB checks in debug builds (given the code is compiled with `opt-level > 0`),
        //         as well as permits surrounding code to be optimized further by giving the
        //         compiler *more* information.
        //
        //         One such example is the following mask calculation, if the compiler knows that `u16::BITS - n` never
        //         will over/underflow, it permits the omission of Rust's automatically inserted debug checks for the subtraction
        //         `u16::BITS - 1 - n`. In release builds, Rust will always default to wrapping subtraction, but due to this
        //         utilization of LLVM's `assume` intrinsic (which `assert_unchecked` lowers to), we're telling the compiler that,
        //         it is impossible for `n >= u16::BITS` to ever be true.
        //
        //         This is a micro-optimization. While on `x86_64` on Zen 4, on release builds, the difference is negligible, we're
        //         able to give the compiler *more* information that it previously would not have, given the caller upholds the contract.
        unsafe { ::core::hint::assert_unchecked(n < u16::BITS) };

        // Calculate the mask for the bits we want to keep.
        //
        // TODO: Figure out a way that is as quick as the mask calculation for `shl`.
        //
        //       According to LLVM-MCA, on Zen 4 this seems to put undue stress on the ALU
        //       when doing the wrapping subtraction.
        //
        //       There *may* be a way around this, but I am unaware of how. Until I figure
        //       that out, this seems to be the fastest way of calculating the mask.
        let mask = (0x00020002_u32 << u16::BITS - 1 - n).wrapping_sub(0x00010001_u32);

        // Perform a logical right shift.
        U16x2((self.0 >> n) & mask)
    }

    /// Performs a wrapping left shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::splat(0b01).wrapping_shl(1), U16x2::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> U16x2 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (u16::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::splat(0b10).wrapping_shr(1), U16x2::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> U16x2 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (u16::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::splat(0b001).overflowing_shl(2), (U16x2::splat(0b100), false));
    /// assert_eq!(U16x2::splat(0b001).overflowing_shl(16), (U16x2::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (U16x2, bool) {
        (self.wrapping_shl(n), n >= u16::BITS)
    }

    /// Performs an overflowing right shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::splat(0b100).overflowing_shr(2), (U16x2::splat(0b001), false));
    /// assert_eq!(U16x2::splat(0b100).overflowing_shr(16), (U16x2::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (U16x2, bool) {
        (self.wrapping_shr(n), n >= u16::BITS)
    }

    /// Performs a checked left shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::splat(0b001).checked_shl(2), Some(U16x2::splat(0b100)));
    /// assert_eq!(U16x2::splat(0b001).checked_shl(16), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<U16x2> {
        if n < u16::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::splat(0b100).checked_shr(2), Some(U16x2::splat(0b001)));
    /// assert_eq!(U16x2::splat(0b100).checked_shr(16), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<U16x2> {
        if n < u16::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::splat(0b001).unbounded_shl(2), U16x2::splat(0b100));
    /// assert_eq!(U16x2::splat(0b001).unbounded_shl(16), U16x2::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> U16x2 {
        if n < u16::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            U16x2::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x2::splat(0b100).unbounded_shr(2), U16x2::splat(0b001));
    /// assert_eq!(U16x2::splat(0b100).unbounded_shr(16), U16x2::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> U16x2 {
        if n < u16::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            U16x2::splat(0)
        }
    }
}

impl U16x2 {
    /// Computes a bitwise AND reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_and(self) -> u16 {
        // Get the two lanes in two separate u32s, and ensure that
        // each lane's bits fits within the low 16-bits.
        let a = self.0 & 0x0000FFFF_u32;
        let b = (self.0 >> u16::BITS) & 0x0000FFFF_u32;

        // Compute the result, and cast to a scalar.
        ((a & b) as u16) as u16
    }

    /// Computes a bitwise OR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_or(self) -> u16 {
        // Get the two lanes in two separate u32s, and ensure that
        // each lane's bits fits within the low 16-bits.
        let a = self.0 & 0x0000FFFF_u32;
        let b = (self.0 >> u16::BITS) & 0x0000FFFF_u32;

        // Compute the result, and cast to a scalar.
        ((a | b) as u16) as u16
    }

    /// Computes a bitwise XOR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_xor(self) -> u16 {
        // Get the two lanes in two separate u32s, and ensure that
        // each lane's bits fits within the low 16-bits.
        let a = self.0 & 0x0000FFFF_u32;
        let b = (self.0 >> u16::BITS) & 0x0000FFFF_u32;

        // Compute the result, and cast to a scalar.
        ((a ^ b) as u16) as u16
    }
}

/// A 64-bit SWAR vector containing 4 [`u16`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u64`], but is
/// treated as a `[u16; 4]`.
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

impl ::core::fmt::Debug for U16x4 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
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
    /// assert_eq!(U16x4::MAX, U16x4::splat(65535));
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
    /// assert_eq!(U16x4::MIN, U16x4::splat(0));
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
    /// assert_eq!(U16x4::LSB, U16x4::splat(0x0001_u16));
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
    /// assert_eq!(U16x4::MSB, U16x4::splat(0x8000_u16));
    ///
    /// ```
    pub const MSB: U16x4 = U16x4::splat(1 << (u16::BITS - 1));

    /// A [`U16x4`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::ZERO, U16x4::splat(0));
    ///
    /// ```
    pub const ZERO: U16x4 = U16x4::splat(0);

    /// A [`U16x4`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::ONE, U16x4::splat(1));
    ///
    /// ```
    pub const ONE: U16x4 = U16x4::splat(1);
}
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
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U16x4::from_array([0x00, 0x01, 0x02, 0x03]);
    /// let after = U16x4::from_array([0x03, 0x00, 0x01, 0x02]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> U16x4 {
        let n_bits = u16::BITS * (n % U16x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U16x4(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U16x4(self.0.rotate_left(n_bits))
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
    /// let before = U16x4::from_array([0x00, 0x01, 0x02, 0x03]);
    /// let after = U16x4::from_array([0x01, 0x02, 0x03, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> U16x4 {
        let n_bits = u16::BITS * (n % U16x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U16x4(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U16x4(self.0.rotate_right(n_bits))
        }
    }
}
impl U16x4 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U16x4::from_array([0x0A, 0x0A, 0x0B, 0x0B]);
    /// let after = U16x4::from_array([0x00, 0x00, 0x0A, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(2), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> U16x4 {
        let n_bits = u16::BITS * (n % U16x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U16x4(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            U16x4(self.0 << n_bits)
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
    /// let before = U16x4::from_array([0x0A, 0x0A, 0x0B, 0x0B]);
    /// let after = U16x4::from_array([0x0B, 0x0B, 0x00, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(2), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> U16x4 {
        let n_bits = u16::BITS * (n % U16x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U16x4(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            U16x4(self.0 >> n_bits)
        }
    }
}
impl U16x4 {
    /// Performs a bitwise NOT on each [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::splat(0x00).not(), U16x4::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> U16x4 {
        U16x4(!self.0)
    }

    /// Performs a bitwise OR on each [`u16`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::splat(0b01).or(U16x4::splat(0b10)), U16x4::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: U16x4) -> U16x4 {
        U16x4(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`u16`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::splat(0b1101).and(U16x4::splat(0b0111)), U16x4::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: U16x4) -> U16x4 {
        U16x4(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`u16`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::splat(0b1101).xor(U16x4::splat(0b0111)), U16x4::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: U16x4) -> U16x4 {
        U16x4(self.0 ^ rhs.0)
    }
}
impl U16x4 {
    /// Performs an unchecked left shift on every [`u16`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 16`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> U16x4 {
        // SAFETY: The caller ensures `n < 16`.
        unsafe { ::core::hint::assert_unchecked(n < u16::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask =
            !(0x8000800080008000_u64 >> u16::BITS - 1 - n).wrapping_sub(0x0001000100010001_u64);

        // Calculate the left shift.
        let shifted = self.0 << n;

        U16x4(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`u16`] lane by `n` bits.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 16`.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> U16x4 {
        // NOTE: `n` is a [`u32`] mainly to maintain parity with the Rust standard library. All of the
        //       right shift methods on [`u16`]s accept a [`u32`] as an argument.
        //
        //       Even though we know that `n` could definitely fit within a byte, this is just easier
        //       for consumers of the library. API consistency.

        // SAFETY: The caller ensures `n < 16`. This permits the omission of
        //         UB checks in debug builds (given the code is compiled with `opt-level > 0`),
        //         as well as permits surrounding code to be optimized further by giving the
        //         compiler *more* information.
        //
        //         One such example is the following mask calculation, if the compiler knows that `u16::BITS - n` never
        //         will over/underflow, it permits the omission of Rust's automatically inserted debug checks for the subtraction
        //         `u16::BITS - 1 - n`. In release builds, Rust will always default to wrapping subtraction, but due to this
        //         utilization of LLVM's `assume` intrinsic (which `assert_unchecked` lowers to), we're telling the compiler that,
        //         it is impossible for `n >= u16::BITS` to ever be true.
        //
        //         This is a micro-optimization. While on `x86_64` on Zen 4, on release builds, the difference is negligible, we're
        //         able to give the compiler *more* information that it previously would not have, given the caller upholds the contract.
        unsafe { ::core::hint::assert_unchecked(n < u16::BITS) };

        // Calculate the mask for the bits we want to keep.
        //
        // TODO: Figure out a way that is as quick as the mask calculation for `shl`.
        //
        //       According to LLVM-MCA, on Zen 4 this seems to put undue stress on the ALU
        //       when doing the wrapping subtraction.
        //
        //       There *may* be a way around this, but I am unaware of how. Until I figure
        //       that out, this seems to be the fastest way of calculating the mask.
        let mask =
            (0x0002000200020002_u64 << u16::BITS - 1 - n).wrapping_sub(0x0001000100010001_u64);

        // Perform a logical right shift.
        U16x4((self.0 >> n) & mask)
    }

    /// Performs a wrapping left shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::splat(0b01).wrapping_shl(1), U16x4::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> U16x4 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (u16::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::splat(0b10).wrapping_shr(1), U16x4::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> U16x4 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (u16::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::splat(0b001).overflowing_shl(2), (U16x4::splat(0b100), false));
    /// assert_eq!(U16x4::splat(0b001).overflowing_shl(16), (U16x4::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (U16x4, bool) {
        (self.wrapping_shl(n), n >= u16::BITS)
    }

    /// Performs an overflowing right shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::splat(0b100).overflowing_shr(2), (U16x4::splat(0b001), false));
    /// assert_eq!(U16x4::splat(0b100).overflowing_shr(16), (U16x4::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (U16x4, bool) {
        (self.wrapping_shr(n), n >= u16::BITS)
    }

    /// Performs a checked left shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::splat(0b001).checked_shl(2), Some(U16x4::splat(0b100)));
    /// assert_eq!(U16x4::splat(0b001).checked_shl(16), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<U16x4> {
        if n < u16::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::splat(0b100).checked_shr(2), Some(U16x4::splat(0b001)));
    /// assert_eq!(U16x4::splat(0b100).checked_shr(16), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<U16x4> {
        if n < u16::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::splat(0b001).unbounded_shl(2), U16x4::splat(0b100));
    /// assert_eq!(U16x4::splat(0b001).unbounded_shl(16), U16x4::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> U16x4 {
        if n < u16::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            U16x4::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x4::splat(0b100).unbounded_shr(2), U16x4::splat(0b001));
    /// assert_eq!(U16x4::splat(0b100).unbounded_shr(16), U16x4::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> U16x4 {
        if n < u16::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            U16x4::splat(0)
        }
    }
}

impl U16x4 {
    /// Computes a bitwise AND reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_and(self) -> u16 {
        use crate::u32::U32x2;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x0000FFFF0000FFFF_u64;
        let b = (self.0 >> u16::BITS) & 0x0000FFFF0000FFFF_u64;

        // Compute the bitwise AND for two neighboring pairs, and then treat
        // the result as a U32x2 vector, defering to
        // it's `reduce_and` implementation for the further reduction steps.
        //
        // This works as bitwise AND is an operation that is commutative and associative.
        let reduced = U32x2::from_bits(a & b).reduce_and();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u32) as u16
    }

    /// Computes a bitwise OR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_or(self) -> u16 {
        use crate::u32::U32x2;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x0000FFFF0000FFFF_u64;
        let b = (self.0 >> u16::BITS) & 0x0000FFFF0000FFFF_u64;

        // Compute the bitwise OR for two neighboring pairs, and then treat
        // the result as a U32x2 vector, defering to
        // it's `reduce_or` implementation for the further reduction steps.
        //
        // This works as bitwise OR is an operation that is commutative and associative.
        let reduced = U32x2::from_bits(a | b).reduce_or();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u32) as u16
    }

    /// Computes a bitwise XOR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_xor(self) -> u16 {
        use crate::u32::U32x2;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x0000FFFF0000FFFF_u64;
        let b = (self.0 >> u16::BITS) & 0x0000FFFF0000FFFF_u64;

        // Compute the bitwise XOR for two neighboring pairs, and then treat
        // the result as a U32x2 vector, defering to
        // it's `reduce_xor` implementation for the further reduction steps.
        //
        // This works as bitwise XOR is an operation that is commutative and associative.
        let reduced = U32x2::from_bits(a ^ b).reduce_xor();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u32) as u16
    }
}

/// A 128-bit SWAR vector containing 8 [`u16`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u128`], but is
/// treated as a `[u16; 8]`.
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

impl ::core::fmt::Debug for U16x8 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
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
    /// assert_eq!(U16x8::MAX, U16x8::splat(65535));
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
    /// assert_eq!(U16x8::MIN, U16x8::splat(0));
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
    /// assert_eq!(U16x8::LSB, U16x8::splat(0x0001_u16));
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
    /// assert_eq!(U16x8::MSB, U16x8::splat(0x8000_u16));
    ///
    /// ```
    pub const MSB: U16x8 = U16x8::splat(1 << (u16::BITS - 1));

    /// A [`U16x8`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::ZERO, U16x8::splat(0));
    ///
    /// ```
    pub const ZERO: U16x8 = U16x8::splat(0);

    /// A [`U16x8`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::ONE, U16x8::splat(1));
    ///
    /// ```
    pub const ONE: U16x8 = U16x8::splat(1);
}
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
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U16x8::from_array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]);
    /// let after = U16x8::from_array([0x07, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> U16x8 {
        let n_bits = u16::BITS * (n % U16x8::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U16x8(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U16x8(self.0.rotate_left(n_bits))
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
    /// let before = U16x8::from_array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]);
    /// let after = U16x8::from_array([0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> U16x8 {
        let n_bits = u16::BITS * (n % U16x8::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U16x8(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            U16x8(self.0.rotate_right(n_bits))
        }
    }
}
impl U16x8 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = U16x8::from_array([0x0A, 0x0A, 0x0A, 0x0A, 0x0B, 0x0B, 0x0B, 0x0B]);
    /// let after = U16x8::from_array([0x00, 0x00, 0x00, 0x00, 0x0A, 0x0A, 0x0A, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(4), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> U16x8 {
        let n_bits = u16::BITS * (n % U16x8::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U16x8(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            U16x8(self.0 << n_bits)
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
    /// let before = U16x8::from_array([0x0A, 0x0A, 0x0A, 0x0A, 0x0B, 0x0B, 0x0B, 0x0B]);
    /// let after = U16x8::from_array([0x0B, 0x0B, 0x0B, 0x0B, 0x00, 0x00, 0x00, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(4), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> U16x8 {
        let n_bits = u16::BITS * (n % U16x8::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            U16x8(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            U16x8(self.0 >> n_bits)
        }
    }
}
impl U16x8 {
    /// Performs a bitwise NOT on each [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::splat(0x00).not(), U16x8::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> U16x8 {
        U16x8(!self.0)
    }

    /// Performs a bitwise OR on each [`u16`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::splat(0b01).or(U16x8::splat(0b10)), U16x8::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: U16x8) -> U16x8 {
        U16x8(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`u16`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::splat(0b1101).and(U16x8::splat(0b0111)), U16x8::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: U16x8) -> U16x8 {
        U16x8(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`u16`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::splat(0b1101).xor(U16x8::splat(0b0111)), U16x8::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: U16x8) -> U16x8 {
        U16x8(self.0 ^ rhs.0)
    }
}
impl U16x8 {
    /// Performs an unchecked left shift on every [`u16`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 16`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> U16x8 {
        // SAFETY: The caller ensures `n < 16`.
        unsafe { ::core::hint::assert_unchecked(n < u16::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask = !(0x80008000800080008000800080008000_u128 >> u16::BITS - 1 - n)
            .wrapping_sub(0x00010001000100010001000100010001_u128);

        // Calculate the left shift.
        let shifted = self.0 << n;

        U16x8(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`u16`] lane by `n` bits.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 16`.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> U16x8 {
        // NOTE: `n` is a [`u32`] mainly to maintain parity with the Rust standard library. All of the
        //       right shift methods on [`u16`]s accept a [`u32`] as an argument.
        //
        //       Even though we know that `n` could definitely fit within a byte, this is just easier
        //       for consumers of the library. API consistency.

        // SAFETY: The caller ensures `n < 16`. This permits the omission of
        //         UB checks in debug builds (given the code is compiled with `opt-level > 0`),
        //         as well as permits surrounding code to be optimized further by giving the
        //         compiler *more* information.
        //
        //         One such example is the following mask calculation, if the compiler knows that `u16::BITS - n` never
        //         will over/underflow, it permits the omission of Rust's automatically inserted debug checks for the subtraction
        //         `u16::BITS - 1 - n`. In release builds, Rust will always default to wrapping subtraction, but due to this
        //         utilization of LLVM's `assume` intrinsic (which `assert_unchecked` lowers to), we're telling the compiler that,
        //         it is impossible for `n >= u16::BITS` to ever be true.
        //
        //         This is a micro-optimization. While on `x86_64` on Zen 4, on release builds, the difference is negligible, we're
        //         able to give the compiler *more* information that it previously would not have, given the caller upholds the contract.
        unsafe { ::core::hint::assert_unchecked(n < u16::BITS) };

        // Calculate the mask for the bits we want to keep.
        //
        // TODO: Figure out a way that is as quick as the mask calculation for `shl`.
        //
        //       According to LLVM-MCA, on Zen 4 this seems to put undue stress on the ALU
        //       when doing the wrapping subtraction.
        //
        //       There *may* be a way around this, but I am unaware of how. Until I figure
        //       that out, this seems to be the fastest way of calculating the mask.
        let mask = (0x00020002000200020002000200020002_u128 << u16::BITS - 1 - n)
            .wrapping_sub(0x00010001000100010001000100010001_u128);

        // Perform a logical right shift.
        U16x8((self.0 >> n) & mask)
    }

    /// Performs a wrapping left shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::splat(0b01).wrapping_shl(1), U16x8::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> U16x8 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (u16::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::splat(0b10).wrapping_shr(1), U16x8::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> U16x8 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (u16::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::splat(0b001).overflowing_shl(2), (U16x8::splat(0b100), false));
    /// assert_eq!(U16x8::splat(0b001).overflowing_shl(16), (U16x8::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (U16x8, bool) {
        (self.wrapping_shl(n), n >= u16::BITS)
    }

    /// Performs an overflowing right shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::splat(0b100).overflowing_shr(2), (U16x8::splat(0b001), false));
    /// assert_eq!(U16x8::splat(0b100).overflowing_shr(16), (U16x8::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (U16x8, bool) {
        (self.wrapping_shr(n), n >= u16::BITS)
    }

    /// Performs a checked left shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::splat(0b001).checked_shl(2), Some(U16x8::splat(0b100)));
    /// assert_eq!(U16x8::splat(0b001).checked_shl(16), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<U16x8> {
        if n < u16::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::splat(0b100).checked_shr(2), Some(U16x8::splat(0b001)));
    /// assert_eq!(U16x8::splat(0b100).checked_shr(16), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<U16x8> {
        if n < u16::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::splat(0b001).unbounded_shl(2), U16x8::splat(0b100));
    /// assert_eq!(U16x8::splat(0b001).unbounded_shl(16), U16x8::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> U16x8 {
        if n < u16::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            U16x8::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`u16`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(U16x8::splat(0b100).unbounded_shr(2), U16x8::splat(0b001));
    /// assert_eq!(U16x8::splat(0b100).unbounded_shr(16), U16x8::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> U16x8 {
        if n < u16::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            U16x8::splat(0)
        }
    }
}

impl U16x8 {
    /// Computes a bitwise AND reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_and(self) -> u16 {
        use crate::u32::U32x4;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x0000FFFF0000FFFF0000FFFF0000FFFF_u128;
        let b = (self.0 >> u16::BITS) & 0x0000FFFF0000FFFF0000FFFF0000FFFF_u128;

        // Compute the bitwise AND for two neighboring pairs, and then treat
        // the result as a U32x4 vector, defering to
        // it's `reduce_and` implementation for the further reduction steps.
        //
        // This works as bitwise AND is an operation that is commutative and associative.
        let reduced = U32x4::from_bits(a & b).reduce_and();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u32) as u16
    }

    /// Computes a bitwise OR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_or(self) -> u16 {
        use crate::u32::U32x4;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x0000FFFF0000FFFF0000FFFF0000FFFF_u128;
        let b = (self.0 >> u16::BITS) & 0x0000FFFF0000FFFF0000FFFF0000FFFF_u128;

        // Compute the bitwise OR for two neighboring pairs, and then treat
        // the result as a U32x4 vector, defering to
        // it's `reduce_or` implementation for the further reduction steps.
        //
        // This works as bitwise OR is an operation that is commutative and associative.
        let reduced = U32x4::from_bits(a | b).reduce_or();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u32) as u16
    }

    /// Computes a bitwise XOR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_xor(self) -> u16 {
        use crate::u32::U32x4;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x0000FFFF0000FFFF0000FFFF0000FFFF_u128;
        let b = (self.0 >> u16::BITS) & 0x0000FFFF0000FFFF0000FFFF0000FFFF_u128;

        // Compute the bitwise XOR for two neighboring pairs, and then treat
        // the result as a U32x4 vector, defering to
        // it's `reduce_xor` implementation for the further reduction steps.
        //
        // This works as bitwise XOR is an operation that is commutative and associative.
        let reduced = U32x4::from_bits(a ^ b).reduce_xor();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u32) as u16
    }
}
