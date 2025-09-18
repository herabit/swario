/// A 64-bit SWAR vector containing 2 [`i32`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u64`], but is
/// treated as a `[i32; 2]`.
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

impl ::core::fmt::Debug for I32x2 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
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
    /// assert_eq!(I32x2::MAX, I32x2::splat(2147483647));
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
    /// assert_eq!(I32x2::MIN, I32x2::splat(-2147483648));
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
    /// assert_eq!(I32x2::LSB, I32x2::splat(0x00000001_i32));
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
    /// assert_eq!(I32x2::MSB, I32x2::splat(0x80000000_u32 as i32));
    ///
    /// ```
    pub const MSB: I32x2 = I32x2::splat(1 << (i32::BITS - 1));

    /// A [`I32x2`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::ZERO, I32x2::splat(0));
    ///
    /// ```
    pub const ZERO: I32x2 = I32x2::splat(0);

    /// A [`I32x2`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::ONE, I32x2::splat(1));
    ///
    /// ```
    pub const ONE: I32x2 = I32x2::splat(1);

    /// A [`I32x2`] with all lanes set to negative one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::NEG_ONE, I32x2::splat(-1));
    ///
    /// ```
    pub const NEG_ONE: I32x2 = I32x2::splat(-1);
}
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
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = I32x2::from_array([0x00, 0x01]);
    /// let after = I32x2::from_array([0x01, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> I32x2 {
        let n_bits = i32::BITS * (n % I32x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I32x2(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            I32x2(self.0.rotate_left(n_bits))
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
    /// let before = I32x2::from_array([0x00, 0x01]);
    /// let after = I32x2::from_array([0x01, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> I32x2 {
        let n_bits = i32::BITS * (n % I32x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I32x2(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            I32x2(self.0.rotate_right(n_bits))
        }
    }
}
impl I32x2 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = I32x2::from_array([0x0A, 0x0B]);
    /// let after = I32x2::from_array([0x00, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> I32x2 {
        let n_bits = i32::BITS * (n % I32x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I32x2(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            I32x2(self.0 << n_bits)
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
    /// let before = I32x2::from_array([0x0A, 0x0B]);
    /// let after = I32x2::from_array([0x0B, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> I32x2 {
        let n_bits = i32::BITS * (n % I32x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I32x2(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            I32x2(self.0 >> n_bits)
        }
    }
}
impl I32x2 {
    /// Performs a bitwise NOT on each [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::splat(0x00).not(), I32x2::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> I32x2 {
        I32x2(!self.0)
    }

    /// Performs a bitwise OR on each [`i32`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::splat(0b01).or(I32x2::splat(0b10)), I32x2::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: I32x2) -> I32x2 {
        I32x2(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`i32`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::splat(0b1101).and(I32x2::splat(0b0111)), I32x2::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: I32x2) -> I32x2 {
        I32x2(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`i32`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::splat(0b1101).xor(I32x2::splat(0b0111)), I32x2::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: I32x2) -> I32x2 {
        I32x2(self.0 ^ rhs.0)
    }
}
impl I32x2 {
    /// Performs an unchecked left shift on every [`i32`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 32`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> I32x2 {
        // SAFETY: The caller ensures `n < 32`.
        unsafe { ::core::hint::assert_unchecked(n < i32::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask =
            !(0x8000000080000000_u64 >> i32::BITS - 1 - n).wrapping_sub(0x0000000100000001_u64);

        // Calculate the left shift.
        let shifted = self.0 << n;

        I32x2(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`i32`] lane by `n` bits.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 32`. Failure to do so is *undefined behavior*.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> I32x2 {
        // NOTE: `n` is a [`u32`] mainly to maintain parity with the Rust standard library. All of the
        //       right shift methods on [`i32`]s accept a [`u32`] as an argument.
        //
        //       Even though we know that `n` could definitely fit within a byte, this is just easier
        //       for consumers of the library. API consistency.

        // SAFETY: The caller ensures `n < 32`. This permits the omission of
        //         UB checks in debug builds (given the code is compiled with `opt-level > 0`),
        //         as well as permits surrounding code to be optimized further by giving the
        //         compiler *more* information.
        //
        //         One such example is the following mask calculation, if the compiler knows that `i32::BITS - n` never
        //         will over/underflow, it permits the omission of Rust's automatically inserted debug checks for the subtraction
        //         `i32::BITS - 1 - n`. In release builds, Rust will always default to wrapping subtraction, but due to this
        //         utilization of LLVM's `assume` intrinsic (which `assert_unchecked` lowers to), we're telling the compiler that,
        //         it is impossible for `n >= i32::BITS` to ever be true.
        //
        //         This is a micro-optimization. While on `x86_64` on Zen 4, on release builds, the difference is negligible, we're
        //         able to give the compiler *more* information that it previously would not have, given the caller upholds the contract.
        unsafe { ::core::hint::assert_unchecked(n < i32::BITS) };

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
            (0x0000000200000002_u64 << i32::BITS - 1 - n).wrapping_sub(0x0000000100000001_u64);

        // PERFORMANCE NOTE:
        //
        // This algorithm seems to have better theoretical performance according to
        // `LLVM-MCA` than my original implementation. The reasoning behind this would
        // appear to be the fact my previous algorithm essentially calculated a mask of all the
        // negative lanes (which relied significantly on `sign_mask`), and then in order
        // to even perform the shift, we would have to XOR the vector with the mask.
        //
        // By inverting all of the bits of each negative lane, they cease to be negative,
        // making the logical shift we do afterwards perform the sign extension for us.
        //
        // Then, we'd flip the negative lane bits back with another XOR with the mask, followed
        // by us masking out the bits that overflowed into other lanes.
        //
        // This, was the obvious implementation, at least for me originally. The issue is, however,
        // this makes *every operation after* dependent on the result of not only the `sign_mask`
        // calculation, but that of the `neg_mask` calculation (`neg_mask` being a mask of all the
        // lanes that were negative).
        //
        // This creates quite a significant dependency chain, one that restricts how modern CPUs, at
        // least `x86_64`, can schedule the execution of instructions. Dependency chains hinder the
        // ability for out-of-order execution to be performed...
        //
        // This algorithm, however, differs in that the actual shift is done *independently* of the
        // sign extension. Both have their dependency chains, sure, but they can be executed independently
        // of one another.
        //
        // We compute the logical right shift, and then we calculate the sign extension, then, at the end,
        // we merge them through an `unchecked_add` (as the sign extension's bits are mutually exclusive to
        // the masked out bits of the logical right shift).
        //
        // Even further performance could be achieved through the utilization of `disjoint_bitor` whenever that
        // becomes available in the standard library, as it gives LLVM even further information about what we
        // guarantee, allowing it to better decide which instruction to use.
        //
        //
        // See below for the pseudo code for the old algorithm (`mask` is the same value as above):
        //
        // ```
        // let sign_mask = self.0 & 0x8000000080000000_u64;
        //
        // let neg_mask = sign_mask.wrapping_add(
        //     sign_mask.wrapping_sub(sign_mask >> i32::BITS - 1)
        // );
        //
        // let shifted = ((self.0 ^ neg_mask) >> n) ^ neg_mask;
        //
        // return I32x2(shifted & mask);
        // ```

        // NOTE ON REPRESENTATION: All signed integers in Rust, at least those that are primitives,
        //                         are stored in two's complement. This algorithm relies upon that
        //                         fact.

        // Perform a logical right shift.
        let logical = (self.0 >> n) & mask;

        // Calculate the sign mask.
        let sign_mask = self.0 & 0x8000000080000000_u64;

        // Calculate the sign extension.
        //
        // This essentially calculates a vector where the leading `n` bits of each lane
        // are all set to the sign bit of the source lane.
        //
        // This is also the sole depender on `sign_mask`.
        let sign_ext = (sign_mask - (sign_mask >> n)) << 1;

        // SAFETY: We know that `logical` and `sign_ext` do not have any overlapping set bits.
        //
        //         We know this because `logical` is the result of a zero-extended right shift
        //         on all of the lanes.
        //
        //         Since we know none of that none of the bits overlap, then the sum calculation
        //         can never overflow. As an overflow for any given bit (in unsigned arithmetic)
        //         can only occur if both bits are `1`.
        I32x2(unsafe { logical.unchecked_add(sign_ext) })
    }

    /// Performs a wrapping left shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::splat(0b01).wrapping_shl(1), I32x2::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> I32x2 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (i32::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::splat(0b10).wrapping_shr(1), I32x2::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> I32x2 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (i32::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::splat(0b001).overflowing_shl(2), (I32x2::splat(0b100), false));
    /// assert_eq!(I32x2::splat(0b001).overflowing_shl(32), (I32x2::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (I32x2, bool) {
        (self.wrapping_shl(n), n >= i32::BITS)
    }

    /// Performs an overflowing right shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::splat(0b100).overflowing_shr(2), (I32x2::splat(0b001), false));
    /// assert_eq!(I32x2::splat(0b100).overflowing_shr(32), (I32x2::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (I32x2, bool) {
        (self.wrapping_shr(n), n >= i32::BITS)
    }

    /// Performs a checked left shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::splat(0b001).checked_shl(2), Some(I32x2::splat(0b100)));
    /// assert_eq!(I32x2::splat(0b001).checked_shl(32), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<I32x2> {
        if n < i32::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::splat(0b100).checked_shr(2), Some(I32x2::splat(0b001)));
    /// assert_eq!(I32x2::splat(0b100).checked_shr(32), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<I32x2> {
        if n < i32::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::splat(0b001).unbounded_shl(2), I32x2::splat(0b100));
    /// assert_eq!(I32x2::splat(0b001).unbounded_shl(32), I32x2::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> I32x2 {
        if n < i32::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            I32x2::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x2::splat(0b100).unbounded_shr(2), I32x2::splat(0b001));
    /// assert_eq!(I32x2::splat(0b100).unbounded_shr(32), I32x2::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> I32x2 {
        if n < i32::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            I32x2::splat(0)
        }
    }
}

impl I32x2 {
    /// Computes a bitwise AND reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_and(self) -> i32 {
        // Get the two lanes in two separate u64s, and ensure that
        // each lane's bits fits within the low 32-bits.
        let a = self.0 & 0x00000000FFFFFFFF_u64;
        let b = (self.0 >> i32::BITS) & 0x00000000FFFFFFFF_u64;

        // Compute the result, and cast to a scalar.
        ((a & b) as u32) as i32
    }

    /// Computes a bitwise OR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_or(self) -> i32 {
        // Get the two lanes in two separate u64s, and ensure that
        // each lane's bits fits within the low 32-bits.
        let a = self.0 & 0x00000000FFFFFFFF_u64;
        let b = (self.0 >> i32::BITS) & 0x00000000FFFFFFFF_u64;

        // Compute the result, and cast to a scalar.
        ((a | b) as u32) as i32
    }

    /// Computes a bitwise XOR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_xor(self) -> i32 {
        // Get the two lanes in two separate u64s, and ensure that
        // each lane's bits fits within the low 32-bits.
        let a = self.0 & 0x00000000FFFFFFFF_u64;
        let b = (self.0 >> i32::BITS) & 0x00000000FFFFFFFF_u64;

        // Compute the result, and cast to a scalar.
        ((a ^ b) as u32) as i32
    }
}

/// A 128-bit SWAR vector containing 4 [`i32`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u128`], but is
/// treated as a `[i32; 4]`.
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

impl ::core::fmt::Debug for I32x4 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
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
    /// assert_eq!(I32x4::MAX, I32x4::splat(2147483647));
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
    /// assert_eq!(I32x4::MIN, I32x4::splat(-2147483648));
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
    /// assert_eq!(I32x4::LSB, I32x4::splat(0x00000001_i32));
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
    /// assert_eq!(I32x4::MSB, I32x4::splat(0x80000000_u32 as i32));
    ///
    /// ```
    pub const MSB: I32x4 = I32x4::splat(1 << (i32::BITS - 1));

    /// A [`I32x4`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::ZERO, I32x4::splat(0));
    ///
    /// ```
    pub const ZERO: I32x4 = I32x4::splat(0);

    /// A [`I32x4`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::ONE, I32x4::splat(1));
    ///
    /// ```
    pub const ONE: I32x4 = I32x4::splat(1);

    /// A [`I32x4`] with all lanes set to negative one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::NEG_ONE, I32x4::splat(-1));
    ///
    /// ```
    pub const NEG_ONE: I32x4 = I32x4::splat(-1);
}
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
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = I32x4::from_array([0x00, 0x01, 0x02, 0x03]);
    /// let after = I32x4::from_array([0x03, 0x00, 0x01, 0x02]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> I32x4 {
        let n_bits = i32::BITS * (n % I32x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I32x4(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            I32x4(self.0.rotate_left(n_bits))
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
    /// let before = I32x4::from_array([0x00, 0x01, 0x02, 0x03]);
    /// let after = I32x4::from_array([0x01, 0x02, 0x03, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> I32x4 {
        let n_bits = i32::BITS * (n % I32x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I32x4(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            I32x4(self.0.rotate_right(n_bits))
        }
    }
}
impl I32x4 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = I32x4::from_array([0x0A, 0x0A, 0x0B, 0x0B]);
    /// let after = I32x4::from_array([0x00, 0x00, 0x0A, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(2), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> I32x4 {
        let n_bits = i32::BITS * (n % I32x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I32x4(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            I32x4(self.0 << n_bits)
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
    /// let before = I32x4::from_array([0x0A, 0x0A, 0x0B, 0x0B]);
    /// let after = I32x4::from_array([0x0B, 0x0B, 0x00, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(2), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> I32x4 {
        let n_bits = i32::BITS * (n % I32x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I32x4(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            I32x4(self.0 >> n_bits)
        }
    }
}
impl I32x4 {
    /// Performs a bitwise NOT on each [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::splat(0x00).not(), I32x4::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> I32x4 {
        I32x4(!self.0)
    }

    /// Performs a bitwise OR on each [`i32`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::splat(0b01).or(I32x4::splat(0b10)), I32x4::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: I32x4) -> I32x4 {
        I32x4(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`i32`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::splat(0b1101).and(I32x4::splat(0b0111)), I32x4::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: I32x4) -> I32x4 {
        I32x4(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`i32`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::splat(0b1101).xor(I32x4::splat(0b0111)), I32x4::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: I32x4) -> I32x4 {
        I32x4(self.0 ^ rhs.0)
    }
}
impl I32x4 {
    /// Performs an unchecked left shift on every [`i32`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 32`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> I32x4 {
        // SAFETY: The caller ensures `n < 32`.
        unsafe { ::core::hint::assert_unchecked(n < i32::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask = !(0x80000000800000008000000080000000_u128 >> i32::BITS - 1 - n)
            .wrapping_sub(0x00000001000000010000000100000001_u128);

        // Calculate the left shift.
        let shifted = self.0 << n;

        I32x4(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`i32`] lane by `n` bits.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 32`. Failure to do so is *undefined behavior*.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> I32x4 {
        // NOTE: `n` is a [`u32`] mainly to maintain parity with the Rust standard library. All of the
        //       right shift methods on [`i32`]s accept a [`u32`] as an argument.
        //
        //       Even though we know that `n` could definitely fit within a byte, this is just easier
        //       for consumers of the library. API consistency.

        // SAFETY: The caller ensures `n < 32`. This permits the omission of
        //         UB checks in debug builds (given the code is compiled with `opt-level > 0`),
        //         as well as permits surrounding code to be optimized further by giving the
        //         compiler *more* information.
        //
        //         One such example is the following mask calculation, if the compiler knows that `i32::BITS - n` never
        //         will over/underflow, it permits the omission of Rust's automatically inserted debug checks for the subtraction
        //         `i32::BITS - 1 - n`. In release builds, Rust will always default to wrapping subtraction, but due to this
        //         utilization of LLVM's `assume` intrinsic (which `assert_unchecked` lowers to), we're telling the compiler that,
        //         it is impossible for `n >= i32::BITS` to ever be true.
        //
        //         This is a micro-optimization. While on `x86_64` on Zen 4, on release builds, the difference is negligible, we're
        //         able to give the compiler *more* information that it previously would not have, given the caller upholds the contract.
        unsafe { ::core::hint::assert_unchecked(n < i32::BITS) };

        // Calculate the mask for the bits we want to keep.
        //
        // TODO: Figure out a way that is as quick as the mask calculation for `shl`.
        //
        //       According to LLVM-MCA, on Zen 4 this seems to put undue stress on the ALU
        //       when doing the wrapping subtraction.
        //
        //       There *may* be a way around this, but I am unaware of how. Until I figure
        //       that out, this seems to be the fastest way of calculating the mask.
        let mask = (0x00000002000000020000000200000002_u128 << i32::BITS - 1 - n)
            .wrapping_sub(0x00000001000000010000000100000001_u128);

        // PERFORMANCE NOTE:
        //
        // This algorithm seems to have better theoretical performance according to
        // `LLVM-MCA` than my original implementation. The reasoning behind this would
        // appear to be the fact my previous algorithm essentially calculated a mask of all the
        // negative lanes (which relied significantly on `sign_mask`), and then in order
        // to even perform the shift, we would have to XOR the vector with the mask.
        //
        // By inverting all of the bits of each negative lane, they cease to be negative,
        // making the logical shift we do afterwards perform the sign extension for us.
        //
        // Then, we'd flip the negative lane bits back with another XOR with the mask, followed
        // by us masking out the bits that overflowed into other lanes.
        //
        // This, was the obvious implementation, at least for me originally. The issue is, however,
        // this makes *every operation after* dependent on the result of not only the `sign_mask`
        // calculation, but that of the `neg_mask` calculation (`neg_mask` being a mask of all the
        // lanes that were negative).
        //
        // This creates quite a significant dependency chain, one that restricts how modern CPUs, at
        // least `x86_64`, can schedule the execution of instructions. Dependency chains hinder the
        // ability for out-of-order execution to be performed...
        //
        // This algorithm, however, differs in that the actual shift is done *independently* of the
        // sign extension. Both have their dependency chains, sure, but they can be executed independently
        // of one another.
        //
        // We compute the logical right shift, and then we calculate the sign extension, then, at the end,
        // we merge them through an `unchecked_add` (as the sign extension's bits are mutually exclusive to
        // the masked out bits of the logical right shift).
        //
        // Even further performance could be achieved through the utilization of `disjoint_bitor` whenever that
        // becomes available in the standard library, as it gives LLVM even further information about what we
        // guarantee, allowing it to better decide which instruction to use.
        //
        //
        // See below for the pseudo code for the old algorithm (`mask` is the same value as above):
        //
        // ```
        // let sign_mask = self.0 & 0x80000000800000008000000080000000_u128;
        //
        // let neg_mask = sign_mask.wrapping_add(
        //     sign_mask.wrapping_sub(sign_mask >> i32::BITS - 1)
        // );
        //
        // let shifted = ((self.0 ^ neg_mask) >> n) ^ neg_mask;
        //
        // return I32x4(shifted & mask);
        // ```

        // NOTE ON REPRESENTATION: All signed integers in Rust, at least those that are primitives,
        //                         are stored in two's complement. This algorithm relies upon that
        //                         fact.

        // Perform a logical right shift.
        let logical = (self.0 >> n) & mask;

        // Calculate the sign mask.
        let sign_mask = self.0 & 0x80000000800000008000000080000000_u128;

        // Calculate the sign extension.
        //
        // This essentially calculates a vector where the leading `n` bits of each lane
        // are all set to the sign bit of the source lane.
        //
        // This is also the sole depender on `sign_mask`.
        let sign_ext = (sign_mask - (sign_mask >> n)) << 1;

        // SAFETY: We know that `logical` and `sign_ext` do not have any overlapping set bits.
        //
        //         We know this because `logical` is the result of a zero-extended right shift
        //         on all of the lanes.
        //
        //         Since we know none of that none of the bits overlap, then the sum calculation
        //         can never overflow. As an overflow for any given bit (in unsigned arithmetic)
        //         can only occur if both bits are `1`.
        I32x4(unsafe { logical.unchecked_add(sign_ext) })
    }

    /// Performs a wrapping left shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::splat(0b01).wrapping_shl(1), I32x4::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> I32x4 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (i32::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::splat(0b10).wrapping_shr(1), I32x4::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> I32x4 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (i32::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::splat(0b001).overflowing_shl(2), (I32x4::splat(0b100), false));
    /// assert_eq!(I32x4::splat(0b001).overflowing_shl(32), (I32x4::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (I32x4, bool) {
        (self.wrapping_shl(n), n >= i32::BITS)
    }

    /// Performs an overflowing right shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::splat(0b100).overflowing_shr(2), (I32x4::splat(0b001), false));
    /// assert_eq!(I32x4::splat(0b100).overflowing_shr(32), (I32x4::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (I32x4, bool) {
        (self.wrapping_shr(n), n >= i32::BITS)
    }

    /// Performs a checked left shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::splat(0b001).checked_shl(2), Some(I32x4::splat(0b100)));
    /// assert_eq!(I32x4::splat(0b001).checked_shl(32), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<I32x4> {
        if n < i32::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::splat(0b100).checked_shr(2), Some(I32x4::splat(0b001)));
    /// assert_eq!(I32x4::splat(0b100).checked_shr(32), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<I32x4> {
        if n < i32::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::splat(0b001).unbounded_shl(2), I32x4::splat(0b100));
    /// assert_eq!(I32x4::splat(0b001).unbounded_shl(32), I32x4::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> I32x4 {
        if n < i32::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            I32x4::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`i32`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I32x4::splat(0b100).unbounded_shr(2), I32x4::splat(0b001));
    /// assert_eq!(I32x4::splat(0b100).unbounded_shr(32), I32x4::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> I32x4 {
        if n < i32::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            I32x4::splat(0)
        }
    }
}

impl I32x4 {
    /// Computes a bitwise AND reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_and(self) -> i32 {
        use crate::i64::I64x2;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x00000000FFFFFFFF00000000FFFFFFFF_u128;
        let b = (self.0 >> i32::BITS) & 0x00000000FFFFFFFF00000000FFFFFFFF_u128;

        // Compute the bitwise AND for two neighboring pairs, and then treat
        // the result as a I64x2 vector, defering to
        // it's `reduce_and` implementation for the further reduction steps.
        //
        // This works as bitwise AND is an operation that is commutative and associative.
        let reduced = I64x2::from_bits(a & b).reduce_and();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u64) as i32
    }

    /// Computes a bitwise OR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_or(self) -> i32 {
        use crate::i64::I64x2;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x00000000FFFFFFFF00000000FFFFFFFF_u128;
        let b = (self.0 >> i32::BITS) & 0x00000000FFFFFFFF00000000FFFFFFFF_u128;

        // Compute the bitwise OR for two neighboring pairs, and then treat
        // the result as a I64x2 vector, defering to
        // it's `reduce_or` implementation for the further reduction steps.
        //
        // This works as bitwise OR is an operation that is commutative and associative.
        let reduced = I64x2::from_bits(a | b).reduce_or();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u64) as i32
    }

    /// Computes a bitwise XOR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_xor(self) -> i32 {
        use crate::i64::I64x2;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x00000000FFFFFFFF00000000FFFFFFFF_u128;
        let b = (self.0 >> i32::BITS) & 0x00000000FFFFFFFF00000000FFFFFFFF_u128;

        // Compute the bitwise XOR for two neighboring pairs, and then treat
        // the result as a I64x2 vector, defering to
        // it's `reduce_xor` implementation for the further reduction steps.
        //
        // This works as bitwise XOR is an operation that is commutative and associative.
        let reduced = I64x2::from_bits(a ^ b).reduce_xor();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u64) as i32
    }
}
