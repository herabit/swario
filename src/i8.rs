/// A 16-bit SWAR vector containing 2 [`i8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u16`], but is
/// treated as a `[i8; 2]`.
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

impl ::core::fmt::Debug for I8x2 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
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
    /// assert_eq!(I8x2::MAX, I8x2::splat(127));
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
    /// assert_eq!(I8x2::MIN, I8x2::splat(-128));
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
    /// assert_eq!(I8x2::LSB, I8x2::splat(0x01_i8));
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
    /// assert_eq!(I8x2::MSB, I8x2::splat(0x80_u8 as i8));
    ///
    /// ```
    pub const MSB: I8x2 = I8x2::splat(1 << (i8::BITS - 1));

    /// A [`I8x2`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::ZERO, I8x2::splat(0));
    ///
    /// ```
    pub const ZERO: I8x2 = I8x2::splat(0);

    /// A [`I8x2`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::ONE, I8x2::splat(1));
    ///
    /// ```
    pub const ONE: I8x2 = I8x2::splat(1);

    /// A [`I8x2`] with all lanes set to negative one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::NEG_ONE, I8x2::splat(-1));
    ///
    /// ```
    pub const NEG_ONE: I8x2 = I8x2::splat(-1);
}
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
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = I8x2::from_array([0x00, 0x01]);
    /// let after = I8x2::from_array([0x01, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> I8x2 {
        let n_bits = i8::BITS * (n % I8x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x2(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            I8x2(self.0.rotate_left(n_bits))
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
    /// let before = I8x2::from_array([0x00, 0x01]);
    /// let after = I8x2::from_array([0x01, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> I8x2 {
        let n_bits = i8::BITS * (n % I8x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x2(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            I8x2(self.0.rotate_right(n_bits))
        }
    }
}
impl I8x2 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = I8x2::from_array([0x0A, 0x0B]);
    /// let after = I8x2::from_array([0x00, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> I8x2 {
        let n_bits = i8::BITS * (n % I8x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x2(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            I8x2(self.0 << n_bits)
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
    /// let before = I8x2::from_array([0x0A, 0x0B]);
    /// let after = I8x2::from_array([0x0B, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> I8x2 {
        let n_bits = i8::BITS * (n % I8x2::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x2(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            I8x2(self.0 >> n_bits)
        }
    }
}
impl I8x2 {
    /// Performs a bitwise NOT on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::splat(0x00).not(), I8x2::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> I8x2 {
        I8x2(!self.0)
    }

    /// Performs a bitwise OR on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::splat(0b01).or(I8x2::splat(0b10)), I8x2::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: I8x2) -> I8x2 {
        I8x2(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::splat(0b1101).and(I8x2::splat(0b0111)), I8x2::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: I8x2) -> I8x2 {
        I8x2(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::splat(0b1101).xor(I8x2::splat(0b0111)), I8x2::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: I8x2) -> I8x2 {
        I8x2(self.0 ^ rhs.0)
    }
}
impl I8x2 {
    /// Performs an unchecked left shift on every [`i8`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> I8x2 {
        // SAFETY: The caller ensures `n < 8`.
        unsafe { ::core::hint::assert_unchecked(n < i8::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask = !(0x8080_u16 >> i8::BITS - 1 - n).wrapping_sub(0x0101_u16);

        // Calculate the left shift.
        let shifted = self.0 << n;

        I8x2(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`i8`] lane by `n` bits.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> I8x2 {
        // NOTE: `n` is a [`u32`] mainly to maintain parity with the Rust standard library. All of the
        //       right shift methods on [`i8`]s accept a [`u32`] as an argument.
        //
        //       Even though we know that `n` could definitely fit within a byte, this is just easier
        //       for consumers of the library. API consistency.

        // SAFETY: The caller ensures `n < 8`. This permits the omission of
        //         UB checks in debug builds (given the code is compiled with `opt-level > 0`),
        //         as well as permits surrounding code to be optimized further by giving the
        //         compiler *more* information.
        //
        //         One such example is the following mask calculation, if the compiler knows that `i8::BITS - n` never
        //         will over/underflow, it permits the omission of Rust's automatically inserted debug checks for the subtraction
        //         `i8::BITS - 1 - n`. In release builds, Rust will always default to wrapping subtraction, but due to this
        //         utilization of LLVM's `assume` intrinsic (which `assert_unchecked` lowers to), we're telling the compiler that,
        //         it is impossible for `n >= i8::BITS` to ever be true.
        //
        //         This is a micro-optimization. While on `x86_64` on Zen 4, on release builds, the difference is negligible, we're
        //         able to give the compiler *more* information that it previously would not have, given the caller upholds the contract.
        unsafe { ::core::hint::assert_unchecked(n < i8::BITS) };

        // Calculate the mask for the bits we want to keep.
        //
        // TODO: Figure out a way that is as quick as the mask calculation for `shl`.
        //
        //       According to LLVM-MCA, on Zen 4 this seems to put undue stress on the ALU
        //       when doing the wrapping subtraction.
        //
        //       There *may* be a way around this, but I am unaware of how. Until I figure
        //       that out, this seems to be the fastest way of calculating the mask.
        let mask = (0x0202_u16 << i8::BITS - 1 - n).wrapping_sub(0x0101_u16);

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
        // let sign_mask = self.0 & 0x8080_u16;
        //
        // let neg_mask = sign_mask.wrapping_add(
        //     sign_mask.wrapping_sub(sign_mask >> i8::BITS - 1)
        // );
        //
        // let shifted = ((self.0 ^ neg_mask) >> n) ^ neg_mask;
        //
        // return I8x2(shifted & mask);
        // ```

        // NOTE ON REPRESENTATION: All signed integers in Rust, at least those that are primitives,
        //                         are stored in two's complement. This algorithm relies upon that
        //                         fact.

        // Perform a logical right shift.
        let logical = (self.0 >> n) & mask;

        // Calculate the sign mask.
        let sign_mask = self.0 & 0x8080_u16;

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
        I8x2(unsafe { logical.unchecked_add(sign_ext) })
    }

    /// Performs a wrapping left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::splat(0b01).wrapping_shl(1), I8x2::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> I8x2 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (i8::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::splat(0b10).wrapping_shr(1), I8x2::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> I8x2 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (i8::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::splat(0b001).overflowing_shl(2), (I8x2::splat(0b100), false));
    /// assert_eq!(I8x2::splat(0b001).overflowing_shl(8), (I8x2::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (I8x2, bool) {
        (self.wrapping_shl(n), n >= i8::BITS)
    }

    /// Performs an overflowing right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::splat(0b100).overflowing_shr(2), (I8x2::splat(0b001), false));
    /// assert_eq!(I8x2::splat(0b100).overflowing_shr(8), (I8x2::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (I8x2, bool) {
        (self.wrapping_shr(n), n >= i8::BITS)
    }

    /// Performs a checked left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::splat(0b001).checked_shl(2), Some(I8x2::splat(0b100)));
    /// assert_eq!(I8x2::splat(0b001).checked_shl(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<I8x2> {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::splat(0b100).checked_shr(2), Some(I8x2::splat(0b001)));
    /// assert_eq!(I8x2::splat(0b100).checked_shr(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<I8x2> {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::splat(0b001).unbounded_shl(2), I8x2::splat(0b100));
    /// assert_eq!(I8x2::splat(0b001).unbounded_shl(8), I8x2::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> I8x2 {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            I8x2::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x2::splat(0b100).unbounded_shr(2), I8x2::splat(0b001));
    /// assert_eq!(I8x2::splat(0b100).unbounded_shr(8), I8x2::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> I8x2 {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            I8x2::splat(0)
        }
    }
}

impl I8x2 {
    /// Computes a bitwise AND reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_and(self) -> i8 {
        // Get the two lanes in two separate u16s, and ensure that
        // each lane's bits fits within the low 8-bits.
        let a = self.0 & 0x00FF_u16;
        let b = (self.0 >> i8::BITS) & 0x00FF_u16;

        // Compute the result, and cast to a scalar.
        ((a & b) as u8) as i8
    }

    /// Computes a bitwise OR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_or(self) -> i8 {
        // Get the two lanes in two separate u16s, and ensure that
        // each lane's bits fits within the low 8-bits.
        let a = self.0 & 0x00FF_u16;
        let b = (self.0 >> i8::BITS) & 0x00FF_u16;

        // Compute the result, and cast to a scalar.
        ((a | b) as u8) as i8
    }

    /// Computes a bitwise XOR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_xor(self) -> i8 {
        // Get the two lanes in two separate u16s, and ensure that
        // each lane's bits fits within the low 8-bits.
        let a = self.0 & 0x00FF_u16;
        let b = (self.0 >> i8::BITS) & 0x00FF_u16;

        // Compute the result, and cast to a scalar.
        ((a ^ b) as u8) as i8
    }
}

/// A 32-bit SWAR vector containing 4 [`i8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u32`], but is
/// treated as a `[i8; 4]`.
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

impl ::core::fmt::Debug for I8x4 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
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
    /// assert_eq!(I8x4::MAX, I8x4::splat(127));
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
    /// assert_eq!(I8x4::MIN, I8x4::splat(-128));
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
    /// assert_eq!(I8x4::LSB, I8x4::splat(0x01_i8));
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
    /// assert_eq!(I8x4::MSB, I8x4::splat(0x80_u8 as i8));
    ///
    /// ```
    pub const MSB: I8x4 = I8x4::splat(1 << (i8::BITS - 1));

    /// A [`I8x4`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::ZERO, I8x4::splat(0));
    ///
    /// ```
    pub const ZERO: I8x4 = I8x4::splat(0);

    /// A [`I8x4`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::ONE, I8x4::splat(1));
    ///
    /// ```
    pub const ONE: I8x4 = I8x4::splat(1);

    /// A [`I8x4`] with all lanes set to negative one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::NEG_ONE, I8x4::splat(-1));
    ///
    /// ```
    pub const NEG_ONE: I8x4 = I8x4::splat(-1);
}
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
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = I8x4::from_array([0x00, 0x01, 0x02, 0x03]);
    /// let after = I8x4::from_array([0x03, 0x00, 0x01, 0x02]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> I8x4 {
        let n_bits = i8::BITS * (n % I8x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x4(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            I8x4(self.0.rotate_left(n_bits))
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
    /// let before = I8x4::from_array([0x00, 0x01, 0x02, 0x03]);
    /// let after = I8x4::from_array([0x01, 0x02, 0x03, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> I8x4 {
        let n_bits = i8::BITS * (n % I8x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x4(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            I8x4(self.0.rotate_right(n_bits))
        }
    }
}
impl I8x4 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = I8x4::from_array([0x0A, 0x0A, 0x0B, 0x0B]);
    /// let after = I8x4::from_array([0x00, 0x00, 0x0A, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(2), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> I8x4 {
        let n_bits = i8::BITS * (n % I8x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x4(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            I8x4(self.0 << n_bits)
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
    /// let before = I8x4::from_array([0x0A, 0x0A, 0x0B, 0x0B]);
    /// let after = I8x4::from_array([0x0B, 0x0B, 0x00, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(2), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> I8x4 {
        let n_bits = i8::BITS * (n % I8x4::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x4(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            I8x4(self.0 >> n_bits)
        }
    }
}
impl I8x4 {
    /// Performs a bitwise NOT on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::splat(0x00).not(), I8x4::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> I8x4 {
        I8x4(!self.0)
    }

    /// Performs a bitwise OR on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::splat(0b01).or(I8x4::splat(0b10)), I8x4::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: I8x4) -> I8x4 {
        I8x4(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::splat(0b1101).and(I8x4::splat(0b0111)), I8x4::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: I8x4) -> I8x4 {
        I8x4(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::splat(0b1101).xor(I8x4::splat(0b0111)), I8x4::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: I8x4) -> I8x4 {
        I8x4(self.0 ^ rhs.0)
    }
}
impl I8x4 {
    /// Performs an unchecked left shift on every [`i8`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> I8x4 {
        // SAFETY: The caller ensures `n < 8`.
        unsafe { ::core::hint::assert_unchecked(n < i8::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask = !(0x80808080_u32 >> i8::BITS - 1 - n).wrapping_sub(0x01010101_u32);

        // Calculate the left shift.
        let shifted = self.0 << n;

        I8x4(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`i8`] lane by `n` bits.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> I8x4 {
        // NOTE: `n` is a [`u32`] mainly to maintain parity with the Rust standard library. All of the
        //       right shift methods on [`i8`]s accept a [`u32`] as an argument.
        //
        //       Even though we know that `n` could definitely fit within a byte, this is just easier
        //       for consumers of the library. API consistency.

        // SAFETY: The caller ensures `n < 8`. This permits the omission of
        //         UB checks in debug builds (given the code is compiled with `opt-level > 0`),
        //         as well as permits surrounding code to be optimized further by giving the
        //         compiler *more* information.
        //
        //         One such example is the following mask calculation, if the compiler knows that `i8::BITS - n` never
        //         will over/underflow, it permits the omission of Rust's automatically inserted debug checks for the subtraction
        //         `i8::BITS - 1 - n`. In release builds, Rust will always default to wrapping subtraction, but due to this
        //         utilization of LLVM's `assume` intrinsic (which `assert_unchecked` lowers to), we're telling the compiler that,
        //         it is impossible for `n >= i8::BITS` to ever be true.
        //
        //         This is a micro-optimization. While on `x86_64` on Zen 4, on release builds, the difference is negligible, we're
        //         able to give the compiler *more* information that it previously would not have, given the caller upholds the contract.
        unsafe { ::core::hint::assert_unchecked(n < i8::BITS) };

        // Calculate the mask for the bits we want to keep.
        //
        // TODO: Figure out a way that is as quick as the mask calculation for `shl`.
        //
        //       According to LLVM-MCA, on Zen 4 this seems to put undue stress on the ALU
        //       when doing the wrapping subtraction.
        //
        //       There *may* be a way around this, but I am unaware of how. Until I figure
        //       that out, this seems to be the fastest way of calculating the mask.
        let mask = (0x02020202_u32 << i8::BITS - 1 - n).wrapping_sub(0x01010101_u32);

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
        // let sign_mask = self.0 & 0x80808080_u32;
        //
        // let neg_mask = sign_mask.wrapping_add(
        //     sign_mask.wrapping_sub(sign_mask >> i8::BITS - 1)
        // );
        //
        // let shifted = ((self.0 ^ neg_mask) >> n) ^ neg_mask;
        //
        // return I8x4(shifted & mask);
        // ```

        // NOTE ON REPRESENTATION: All signed integers in Rust, at least those that are primitives,
        //                         are stored in two's complement. This algorithm relies upon that
        //                         fact.

        // Perform a logical right shift.
        let logical = (self.0 >> n) & mask;

        // Calculate the sign mask.
        let sign_mask = self.0 & 0x80808080_u32;

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
        I8x4(unsafe { logical.unchecked_add(sign_ext) })
    }

    /// Performs a wrapping left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::splat(0b01).wrapping_shl(1), I8x4::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> I8x4 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (i8::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::splat(0b10).wrapping_shr(1), I8x4::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> I8x4 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (i8::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::splat(0b001).overflowing_shl(2), (I8x4::splat(0b100), false));
    /// assert_eq!(I8x4::splat(0b001).overflowing_shl(8), (I8x4::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (I8x4, bool) {
        (self.wrapping_shl(n), n >= i8::BITS)
    }

    /// Performs an overflowing right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::splat(0b100).overflowing_shr(2), (I8x4::splat(0b001), false));
    /// assert_eq!(I8x4::splat(0b100).overflowing_shr(8), (I8x4::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (I8x4, bool) {
        (self.wrapping_shr(n), n >= i8::BITS)
    }

    /// Performs a checked left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::splat(0b001).checked_shl(2), Some(I8x4::splat(0b100)));
    /// assert_eq!(I8x4::splat(0b001).checked_shl(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<I8x4> {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::splat(0b100).checked_shr(2), Some(I8x4::splat(0b001)));
    /// assert_eq!(I8x4::splat(0b100).checked_shr(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<I8x4> {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::splat(0b001).unbounded_shl(2), I8x4::splat(0b100));
    /// assert_eq!(I8x4::splat(0b001).unbounded_shl(8), I8x4::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> I8x4 {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            I8x4::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x4::splat(0b100).unbounded_shr(2), I8x4::splat(0b001));
    /// assert_eq!(I8x4::splat(0b100).unbounded_shr(8), I8x4::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> I8x4 {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            I8x4::splat(0)
        }
    }
}

impl I8x4 {
    /// Computes a bitwise AND reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_and(self) -> i8 {
        use crate::i16::I16x2;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x00FF00FF_u32;
        let b = (self.0 >> i8::BITS) & 0x00FF00FF_u32;

        // Compute the bitwise AND for two neighboring pairs, and then treat
        // the result as a I16x2 vector, defering to
        // it's `reduce_and` implementation for the further reduction steps.
        //
        // This works as bitwise AND is an operation that is commutative and associative.
        let reduced = I16x2::from_bits(a & b).reduce_and();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u16) as i8
    }

    /// Computes a bitwise OR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_or(self) -> i8 {
        use crate::i16::I16x2;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x00FF00FF_u32;
        let b = (self.0 >> i8::BITS) & 0x00FF00FF_u32;

        // Compute the bitwise OR for two neighboring pairs, and then treat
        // the result as a I16x2 vector, defering to
        // it's `reduce_or` implementation for the further reduction steps.
        //
        // This works as bitwise OR is an operation that is commutative and associative.
        let reduced = I16x2::from_bits(a | b).reduce_or();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u16) as i8
    }

    /// Computes a bitwise XOR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_xor(self) -> i8 {
        use crate::i16::I16x2;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x00FF00FF_u32;
        let b = (self.0 >> i8::BITS) & 0x00FF00FF_u32;

        // Compute the bitwise XOR for two neighboring pairs, and then treat
        // the result as a I16x2 vector, defering to
        // it's `reduce_xor` implementation for the further reduction steps.
        //
        // This works as bitwise XOR is an operation that is commutative and associative.
        let reduced = I16x2::from_bits(a ^ b).reduce_xor();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u16) as i8
    }
}

/// A 64-bit SWAR vector containing 8 [`i8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u64`], but is
/// treated as a `[i8; 8]`.
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

impl ::core::fmt::Debug for I8x8 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
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
    /// assert_eq!(I8x8::MAX, I8x8::splat(127));
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
    /// assert_eq!(I8x8::MIN, I8x8::splat(-128));
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
    /// assert_eq!(I8x8::LSB, I8x8::splat(0x01_i8));
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
    /// assert_eq!(I8x8::MSB, I8x8::splat(0x80_u8 as i8));
    ///
    /// ```
    pub const MSB: I8x8 = I8x8::splat(1 << (i8::BITS - 1));

    /// A [`I8x8`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::ZERO, I8x8::splat(0));
    ///
    /// ```
    pub const ZERO: I8x8 = I8x8::splat(0);

    /// A [`I8x8`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::ONE, I8x8::splat(1));
    ///
    /// ```
    pub const ONE: I8x8 = I8x8::splat(1);

    /// A [`I8x8`] with all lanes set to negative one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::NEG_ONE, I8x8::splat(-1));
    ///
    /// ```
    pub const NEG_ONE: I8x8 = I8x8::splat(-1);
}
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
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = I8x8::from_array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]);
    /// let after = I8x8::from_array([0x07, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> I8x8 {
        let n_bits = i8::BITS * (n % I8x8::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x8(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            I8x8(self.0.rotate_left(n_bits))
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
    /// let before = I8x8::from_array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]);
    /// let after = I8x8::from_array([0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> I8x8 {
        let n_bits = i8::BITS * (n % I8x8::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x8(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            I8x8(self.0.rotate_right(n_bits))
        }
    }
}
impl I8x8 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = I8x8::from_array([0x0A, 0x0A, 0x0A, 0x0A, 0x0B, 0x0B, 0x0B, 0x0B]);
    /// let after = I8x8::from_array([0x00, 0x00, 0x00, 0x00, 0x0A, 0x0A, 0x0A, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(4), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> I8x8 {
        let n_bits = i8::BITS * (n % I8x8::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x8(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            I8x8(self.0 << n_bits)
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
    /// let before = I8x8::from_array([0x0A, 0x0A, 0x0A, 0x0A, 0x0B, 0x0B, 0x0B, 0x0B]);
    /// let after = I8x8::from_array([0x0B, 0x0B, 0x0B, 0x0B, 0x00, 0x00, 0x00, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(4), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> I8x8 {
        let n_bits = i8::BITS * (n % I8x8::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x8(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            I8x8(self.0 >> n_bits)
        }
    }
}
impl I8x8 {
    /// Performs a bitwise NOT on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::splat(0x00).not(), I8x8::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> I8x8 {
        I8x8(!self.0)
    }

    /// Performs a bitwise OR on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::splat(0b01).or(I8x8::splat(0b10)), I8x8::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: I8x8) -> I8x8 {
        I8x8(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::splat(0b1101).and(I8x8::splat(0b0111)), I8x8::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: I8x8) -> I8x8 {
        I8x8(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::splat(0b1101).xor(I8x8::splat(0b0111)), I8x8::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: I8x8) -> I8x8 {
        I8x8(self.0 ^ rhs.0)
    }
}
impl I8x8 {
    /// Performs an unchecked left shift on every [`i8`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> I8x8 {
        // SAFETY: The caller ensures `n < 8`.
        unsafe { ::core::hint::assert_unchecked(n < i8::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask =
            !(0x8080808080808080_u64 >> i8::BITS - 1 - n).wrapping_sub(0x0101010101010101_u64);

        // Calculate the left shift.
        let shifted = self.0 << n;

        I8x8(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`i8`] lane by `n` bits.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> I8x8 {
        // NOTE: `n` is a [`u32`] mainly to maintain parity with the Rust standard library. All of the
        //       right shift methods on [`i8`]s accept a [`u32`] as an argument.
        //
        //       Even though we know that `n` could definitely fit within a byte, this is just easier
        //       for consumers of the library. API consistency.

        // SAFETY: The caller ensures `n < 8`. This permits the omission of
        //         UB checks in debug builds (given the code is compiled with `opt-level > 0`),
        //         as well as permits surrounding code to be optimized further by giving the
        //         compiler *more* information.
        //
        //         One such example is the following mask calculation, if the compiler knows that `i8::BITS - n` never
        //         will over/underflow, it permits the omission of Rust's automatically inserted debug checks for the subtraction
        //         `i8::BITS - 1 - n`. In release builds, Rust will always default to wrapping subtraction, but due to this
        //         utilization of LLVM's `assume` intrinsic (which `assert_unchecked` lowers to), we're telling the compiler that,
        //         it is impossible for `n >= i8::BITS` to ever be true.
        //
        //         This is a micro-optimization. While on `x86_64` on Zen 4, on release builds, the difference is negligible, we're
        //         able to give the compiler *more* information that it previously would not have, given the caller upholds the contract.
        unsafe { ::core::hint::assert_unchecked(n < i8::BITS) };

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
            (0x0202020202020202_u64 << i8::BITS - 1 - n).wrapping_sub(0x0101010101010101_u64);

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
        // let sign_mask = self.0 & 0x8080808080808080_u64;
        //
        // let neg_mask = sign_mask.wrapping_add(
        //     sign_mask.wrapping_sub(sign_mask >> i8::BITS - 1)
        // );
        //
        // let shifted = ((self.0 ^ neg_mask) >> n) ^ neg_mask;
        //
        // return I8x8(shifted & mask);
        // ```

        // NOTE ON REPRESENTATION: All signed integers in Rust, at least those that are primitives,
        //                         are stored in two's complement. This algorithm relies upon that
        //                         fact.

        // Perform a logical right shift.
        let logical = (self.0 >> n) & mask;

        // Calculate the sign mask.
        let sign_mask = self.0 & 0x8080808080808080_u64;

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
        I8x8(unsafe { logical.unchecked_add(sign_ext) })
    }

    /// Performs a wrapping left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::splat(0b01).wrapping_shl(1), I8x8::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> I8x8 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (i8::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::splat(0b10).wrapping_shr(1), I8x8::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> I8x8 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (i8::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::splat(0b001).overflowing_shl(2), (I8x8::splat(0b100), false));
    /// assert_eq!(I8x8::splat(0b001).overflowing_shl(8), (I8x8::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (I8x8, bool) {
        (self.wrapping_shl(n), n >= i8::BITS)
    }

    /// Performs an overflowing right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::splat(0b100).overflowing_shr(2), (I8x8::splat(0b001), false));
    /// assert_eq!(I8x8::splat(0b100).overflowing_shr(8), (I8x8::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (I8x8, bool) {
        (self.wrapping_shr(n), n >= i8::BITS)
    }

    /// Performs a checked left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::splat(0b001).checked_shl(2), Some(I8x8::splat(0b100)));
    /// assert_eq!(I8x8::splat(0b001).checked_shl(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<I8x8> {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::splat(0b100).checked_shr(2), Some(I8x8::splat(0b001)));
    /// assert_eq!(I8x8::splat(0b100).checked_shr(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<I8x8> {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::splat(0b001).unbounded_shl(2), I8x8::splat(0b100));
    /// assert_eq!(I8x8::splat(0b001).unbounded_shl(8), I8x8::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> I8x8 {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            I8x8::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x8::splat(0b100).unbounded_shr(2), I8x8::splat(0b001));
    /// assert_eq!(I8x8::splat(0b100).unbounded_shr(8), I8x8::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> I8x8 {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            I8x8::splat(0)
        }
    }
}

impl I8x8 {
    /// Computes a bitwise AND reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_and(self) -> i8 {
        use crate::i16::I16x4;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x00FF00FF00FF00FF_u64;
        let b = (self.0 >> i8::BITS) & 0x00FF00FF00FF00FF_u64;

        // Compute the bitwise AND for two neighboring pairs, and then treat
        // the result as a I16x4 vector, defering to
        // it's `reduce_and` implementation for the further reduction steps.
        //
        // This works as bitwise AND is an operation that is commutative and associative.
        let reduced = I16x4::from_bits(a & b).reduce_and();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u16) as i8
    }

    /// Computes a bitwise OR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_or(self) -> i8 {
        use crate::i16::I16x4;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x00FF00FF00FF00FF_u64;
        let b = (self.0 >> i8::BITS) & 0x00FF00FF00FF00FF_u64;

        // Compute the bitwise OR for two neighboring pairs, and then treat
        // the result as a I16x4 vector, defering to
        // it's `reduce_or` implementation for the further reduction steps.
        //
        // This works as bitwise OR is an operation that is commutative and associative.
        let reduced = I16x4::from_bits(a | b).reduce_or();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u16) as i8
    }

    /// Computes a bitwise XOR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_xor(self) -> i8 {
        use crate::i16::I16x4;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x00FF00FF00FF00FF_u64;
        let b = (self.0 >> i8::BITS) & 0x00FF00FF00FF00FF_u64;

        // Compute the bitwise XOR for two neighboring pairs, and then treat
        // the result as a I16x4 vector, defering to
        // it's `reduce_xor` implementation for the further reduction steps.
        //
        // This works as bitwise XOR is an operation that is commutative and associative.
        let reduced = I16x4::from_bits(a ^ b).reduce_xor();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u16) as i8
    }
}

/// A 128-bit SWAR vector containing 16 [`i8`]s.
///
///
/// # Memory Layout
///
/// This type is a transparent wrapper over a [`u128`], but is
/// treated as a `[i8; 16]`.
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

impl ::core::fmt::Debug for I8x16 {
    #[inline]
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        self.as_array().fmt(f)
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
    /// assert_eq!(I8x16::MAX, I8x16::splat(127));
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
    /// assert_eq!(I8x16::MIN, I8x16::splat(-128));
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
    /// assert_eq!(I8x16::LSB, I8x16::splat(0x01_i8));
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
    /// assert_eq!(I8x16::MSB, I8x16::splat(0x80_u8 as i8));
    ///
    /// ```
    pub const MSB: I8x16 = I8x16::splat(1 << (i8::BITS - 1));

    /// A [`I8x16`] with all lanes set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::ZERO, I8x16::splat(0));
    ///
    /// ```
    pub const ZERO: I8x16 = I8x16::splat(0);

    /// A [`I8x16`] with all lanes set to one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::ONE, I8x16::splat(1));
    ///
    /// ```
    pub const ONE: I8x16 = I8x16::splat(1);

    /// A [`I8x16`] with all lanes set to negative one.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::NEG_ONE, I8x16::splat(-1));
    ///
    /// ```
    pub const NEG_ONE: I8x16 = I8x16::splat(-1);
}
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
    /// Rotates the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = I8x16::from_array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F]);
    /// let after = I8x16::from_array([0x0F, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E]);
    ///
    /// assert_eq!(before.rotate_lanes_right(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_right(self, n: u32) -> I8x16 {
        let n_bits = i8::BITS * (n % I8x16::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x16(self.0.rotate_right(n_bits))
        } else {
            // NOTE: Little endian is weird.
            I8x16(self.0.rotate_left(n_bits))
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
    /// let before = I8x16::from_array([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F]);
    /// let after = I8x16::from_array([0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x00]);
    ///
    /// assert_eq!(before.rotate_lanes_left(1), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn rotate_lanes_left(self, n: u32) -> I8x16 {
        let n_bits = i8::BITS * (n % I8x16::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x16(self.0.rotate_left(n_bits))
        } else {
            // NOTE: Little endian is weird.
            I8x16(self.0.rotate_right(n_bits))
        }
    }
}
impl I8x16 {
    /// Shifts the vector by `n` lanes to the right.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// let before = I8x16::from_array([0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B]);
    /// let after = I8x16::from_array([0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A]);
    ///
    /// assert_eq!(before.shift_lanes_right(8), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_right(self, n: u32) -> I8x16 {
        let n_bits = i8::BITS * (n % I8x16::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x16(self.0 >> n_bits)
        } else {
            // NOTE: Little endian is weird.
            I8x16(self.0 << n_bits)
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
    /// let before = I8x16::from_array([0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0A, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B]);
    /// let after = I8x16::from_array([0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x0B, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
    ///
    /// assert_eq!(before.shift_lanes_left(8), after);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn shift_lanes_left(self, n: u32) -> I8x16 {
        let n_bits = i8::BITS * (n % I8x16::LANES as u32);

        if ::core::cfg!(target_endian = "big") {
            I8x16(self.0 << n_bits)
        } else {
            // NOTE: Little endian is weird.
            I8x16(self.0 >> n_bits)
        }
    }
}
impl I8x16 {
    /// Performs a bitwise NOT on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::splat(0x00).not(), I8x16::splat(!0x00));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn not(self) -> I8x16 {
        I8x16(!self.0)
    }

    /// Performs a bitwise OR on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::splat(0b01).or(I8x16::splat(0b10)), I8x16::splat(0b11));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn or(self, rhs: I8x16) -> I8x16 {
        I8x16(self.0 | rhs.0)
    }

    /// Performs a bitwise AND on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::splat(0b1101).and(I8x16::splat(0b0111)), I8x16::splat(0b0101));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn and(self, rhs: I8x16) -> I8x16 {
        I8x16(self.0 & rhs.0)
    }

    /// Performs a bitwise XOR on each [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::splat(0b1101).xor(I8x16::splat(0b0111)), I8x16::splat(0b1010));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn xor(self, rhs: I8x16) -> I8x16 {
        I8x16(self.0 ^ rhs.0)
    }
}
impl I8x16 {
    /// Performs an unchecked left shift on every [`i8`] lane.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`. Failure to do so is undefined behavior.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shl(self, n: u32) -> I8x16 {
        // SAFETY: The caller ensures `n < 8`.
        unsafe { ::core::hint::assert_unchecked(n < i8::BITS) };

        // Calculate the mask for the bits we want to keep.
        let mask = !(0x80808080808080808080808080808080_u128 >> i8::BITS - 1 - n)
            .wrapping_sub(0x01010101010101010101010101010101_u128);

        // Calculate the left shift.
        let shifted = self.0 << n;

        I8x16(shifted & mask)
    }

    /// Performs an unchecked right shift on every [`i8`] lane by `n` bits.
    ///
    /// # Safety
    ///
    /// The caller must ensure `n < 8`.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const unsafe fn unchecked_shr(self, n: u32) -> I8x16 {
        // NOTE: `n` is a [`u32`] mainly to maintain parity with the Rust standard library. All of the
        //       right shift methods on [`i8`]s accept a [`u32`] as an argument.
        //
        //       Even though we know that `n` could definitely fit within a byte, this is just easier
        //       for consumers of the library. API consistency.

        // SAFETY: The caller ensures `n < 8`. This permits the omission of
        //         UB checks in debug builds (given the code is compiled with `opt-level > 0`),
        //         as well as permits surrounding code to be optimized further by giving the
        //         compiler *more* information.
        //
        //         One such example is the following mask calculation, if the compiler knows that `i8::BITS - n` never
        //         will over/underflow, it permits the omission of Rust's automatically inserted debug checks for the subtraction
        //         `i8::BITS - 1 - n`. In release builds, Rust will always default to wrapping subtraction, but due to this
        //         utilization of LLVM's `assume` intrinsic (which `assert_unchecked` lowers to), we're telling the compiler that,
        //         it is impossible for `n >= i8::BITS` to ever be true.
        //
        //         This is a micro-optimization. While on `x86_64` on Zen 4, on release builds, the difference is negligible, we're
        //         able to give the compiler *more* information that it previously would not have, given the caller upholds the contract.
        unsafe { ::core::hint::assert_unchecked(n < i8::BITS) };

        // Calculate the mask for the bits we want to keep.
        //
        // TODO: Figure out a way that is as quick as the mask calculation for `shl`.
        //
        //       According to LLVM-MCA, on Zen 4 this seems to put undue stress on the ALU
        //       when doing the wrapping subtraction.
        //
        //       There *may* be a way around this, but I am unaware of how. Until I figure
        //       that out, this seems to be the fastest way of calculating the mask.
        let mask = (0x02020202020202020202020202020202_u128 << i8::BITS - 1 - n)
            .wrapping_sub(0x01010101010101010101010101010101_u128);

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
        // let sign_mask = self.0 & 0x80808080808080808080808080808080_u128;
        //
        // let neg_mask = sign_mask.wrapping_add(
        //     sign_mask.wrapping_sub(sign_mask >> i8::BITS - 1)
        // );
        //
        // let shifted = ((self.0 ^ neg_mask) >> n) ^ neg_mask;
        //
        // return I8x16(shifted & mask);
        // ```

        // NOTE ON REPRESENTATION: All signed integers in Rust, at least those that are primitives,
        //                         are stored in two's complement. This algorithm relies upon that
        //                         fact.

        // Perform a logical right shift.
        let logical = (self.0 >> n) & mask;

        // Calculate the sign mask.
        let sign_mask = self.0 & 0x80808080808080808080808080808080_u128;

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
        I8x16(unsafe { logical.unchecked_add(sign_ext) })
    }

    /// Performs a wrapping left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::splat(0b01).wrapping_shl(1), I8x16::splat(0b10));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shl(self, n: u32) -> I8x16 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shl(n & (i8::BITS - 1)) }
    }

    /// Performs a wrapping right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::splat(0b10).wrapping_shr(1), I8x16::splat(0b01));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_shr(self, n: u32) -> I8x16 {
        // SAFETY: By masking by the lane bit size we ensure that
        //         we're not overflowing when we shift.
        unsafe { self.unchecked_shr(n & (i8::BITS - 1)) }
    }

    /// Performs an overflowing left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::splat(0b001).overflowing_shl(2), (I8x16::splat(0b100), false));
    /// assert_eq!(I8x16::splat(0b001).overflowing_shl(8), (I8x16::splat(0b001), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shl(self, n: u32) -> (I8x16, bool) {
        (self.wrapping_shl(n), n >= i8::BITS)
    }

    /// Performs an overflowing right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    ///
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::splat(0b100).overflowing_shr(2), (I8x16::splat(0b001), false));
    /// assert_eq!(I8x16::splat(0b100).overflowing_shr(8), (I8x16::splat(0b100), true));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_shr(self, n: u32) -> (I8x16, bool) {
        (self.wrapping_shr(n), n >= i8::BITS)
    }

    /// Performs a checked left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::splat(0b001).checked_shl(2), Some(I8x16::splat(0b100)));
    /// assert_eq!(I8x16::splat(0b001).checked_shl(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shl(self, n: u32) -> Option<I8x16> {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shl(n) })
        } else {
            None
        }
    }

    /// Performs a checked right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::splat(0b100).checked_shr(2), Some(I8x16::splat(0b001)));
    /// assert_eq!(I8x16::splat(0b100).checked_shr(8), None);
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn checked_shr(self, n: u32) -> Option<I8x16> {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            Some(unsafe { self.unchecked_shr(n) })
        } else {
            None
        }
    }

    /// Performs an unbounded left shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::splat(0b001).unbounded_shl(2), I8x16::splat(0b100));
    /// assert_eq!(I8x16::splat(0b001).unbounded_shl(8), I8x16::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shl(self, n: u32) -> I8x16 {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shl(n) }
        } else {
            I8x16::splat(0)
        }
    }

    /// Performs an unbounded right shift on every [`i8`] lane.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swario::*;
    ///
    /// assert_eq!(I8x16::splat(0b100).unbounded_shr(2), I8x16::splat(0b001));
    /// assert_eq!(I8x16::splat(0b100).unbounded_shr(8), I8x16::splat(0));
    ///
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn unbounded_shr(self, n: u32) -> I8x16 {
        if n < i8::BITS {
            // SAFETY: We just checked that `n` is in range.
            unsafe { self.unchecked_shr(n) }
        } else {
            I8x16::splat(0)
        }
    }
}

impl I8x16 {
    /// Computes a bitwise AND reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_and(self) -> i8 {
        use crate::i16::I16x8;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x00FF00FF00FF00FF00FF00FF00FF00FF_u128;
        let b = (self.0 >> i8::BITS) & 0x00FF00FF00FF00FF00FF00FF00FF00FF_u128;

        // Compute the bitwise AND for two neighboring pairs, and then treat
        // the result as a I16x8 vector, defering to
        // it's `reduce_and` implementation for the further reduction steps.
        //
        // This works as bitwise AND is an operation that is commutative and associative.
        let reduced = I16x8::from_bits(a & b).reduce_and();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u16) as i8
    }

    /// Computes a bitwise OR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_or(self) -> i8 {
        use crate::i16::I16x8;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x00FF00FF00FF00FF00FF00FF00FF00FF_u128;
        let b = (self.0 >> i8::BITS) & 0x00FF00FF00FF00FF00FF00FF00FF00FF_u128;

        // Compute the bitwise OR for two neighboring pairs, and then treat
        // the result as a I16x8 vector, defering to
        // it's `reduce_or` implementation for the further reduction steps.
        //
        // This works as bitwise OR is an operation that is commutative and associative.
        let reduced = I16x8::from_bits(a | b).reduce_or();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u16) as i8
    }

    /// Computes a bitwise XOR reduction.
    #[inline(always)]
    #[must_use]
    pub const fn reduce_xor(self) -> i8 {
        use crate::i16::I16x8;

        // Align neighboring pairs of lanes.
        let a = self.0 & 0x00FF00FF00FF00FF00FF00FF00FF00FF_u128;
        let b = (self.0 >> i8::BITS) & 0x00FF00FF00FF00FF00FF00FF00FF00FF_u128;

        // Compute the bitwise XOR for two neighboring pairs, and then treat
        // the result as a I16x8 vector, defering to
        // it's `reduce_xor` implementation for the further reduction steps.
        //
        // This works as bitwise XOR is an operation that is commutative and associative.
        let reduced = I16x8::from_bits(a ^ b).reduce_xor();

        // We want a truncating cast, normal casts should be fine, but this better
        // demonstrates what we're doing.
        (reduced as u16) as i8
    }
}
