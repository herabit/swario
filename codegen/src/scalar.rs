use core::fmt;
use core::num::NonZero;

macro_rules! scalars {
    (
        $($unsigned:ident <=> $signed:ident),+ $(,)?
    ) => {
        ::paste::paste! {
            /// All of the scalars we could want to represent.
            #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
            pub enum Scalar {
                Unsigned(Unsigned),
                Signed(Signed),
            }

            impl Scalar {
                pub const ALL: &[Scalar] = &[ $(Scalar::Unsigned(Unsigned::$unsigned), Scalar::Signed(Signed::$signed)),+ ];

                /// Returns whether this scalar is signed.
                #[inline]
                #[must_use]
                pub const fn is_signed(self) -> bool {
                    matches!(self, Scalar::Signed(_))
                }

                /// Returns whether this scalar is unsigned.
                #[inline]
                #[must_use]
                pub const fn is_unsigned(self) -> bool {
                    matches!(self, Scalar::Unsigned(_))
                }

                /// Get the name of this scalar.
                #[inline]
                #[must_use]
                pub const fn name(self) -> &'static str {
                    match self {
                        Self::Unsigned(u) => u.name(),
                        Self::Signed(s) => s.name(),
                    }
                }

                /// Get the pascal case name of this scalar.
                #[inline]
                #[must_use]
                pub const fn pascal_name(self) -> &'static str {
                    match self {
                        Self::Unsigned(u) => u.pascal_name(),
                        Self::Signed(s) => s.pascal_name(),
                    }
                }

                /// Get the bit width of this scalar.
                #[inline]
                #[must_use]
                pub const fn width(self) -> Option<NonZero<u32>> {
                    match self {
                        Self::Unsigned(u) => u.width(),
                        Self::Signed(s) => s.width(),
                    }
                }

                /// Flip the signedness
                #[inline]
                #[must_use]
                pub const fn flip_signedness(self) -> Self {
                    match self {
                        Self::Unsigned(u) => Self::Signed(u.signed()),
                        Self::Signed(s) => Self::Unsigned(s.unsigned()),
                    }
                }

                /// Get the unsigned variation of this scalar.
                #[inline]
                #[must_use]
                pub const fn unsigned(self) -> Unsigned {
                    match self {
                        Self::Unsigned(u) => u,
                        Self::Signed(s) => s.unsigned(),
                    }
                }

                /// Get the signed variation of this scalar.
                #[inline]
                #[must_use]
                pub const fn signed(self) -> Signed {
                    match self {
                        Self::Signed(s) => s,
                        Self::Unsigned(u) => u.signed(),
                    }
                }

                /// Get a list of lane counts supported for this scalar.
                ///
                /// Namely, the dimensions of vectors that contain this scalar
                /// as a lane.
                #[inline]
                #[must_use]
                pub const fn supported_counts(self) -> &'static [NonZero<u32>] {
                    let Some(width) = self.width() else {
                        return &[];
                    };

                    match width.get() {
                        8 =>   const { &[
                            // NonZero::new(1).unwrap(),
                            NonZero::new(2).unwrap(),
                            NonZero::new(4).unwrap(),
                            NonZero::new(8).unwrap(),
                            NonZero::new(16).unwrap(),
                        ] },
                        16 =>  const { &[
                            // NonZero::new(1).unwrap(),
                            NonZero::new(2).unwrap(),
                            NonZero::new(4).unwrap(),
                            NonZero::new(8).unwrap(),
                        ] },
                        32 =>  const { &[
                            // NonZero::new(1).unwrap(),
                            NonZero::new(2).unwrap(),
                            NonZero::new(4).unwrap(),
                        ] },
                        64 =>  const { &[
                            // NonZero::new(1).unwrap(),
                            NonZero::new(2).unwrap(),
                        ] },
                        128 => const { &[
                            // NonZero::new(1).unwrap(),
                        ] },
                        _ =>   &[],
                    }
                }

                #[inline]
                #[must_use]
                pub const fn min(self) -> Option<i128> {
                    match self {
                        Self::Unsigned(u) => u.min(),
                        Self::Signed(s) => s.min(),
                    }
                }

                #[inline]
                #[must_use]
                pub const fn max(self) -> Option<u128> {
                    match self {
                        Self::Unsigned(u) => u.max(),
                        Self::Signed(s) => s.max(),
                    }
                }
            }


            impl fmt::Display for Scalar {
                #[inline]
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    f.write_str(self.name())
                }
            }

            /// Unsigned scalars.
            #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
            pub enum Unsigned {
                $(
                    $unsigned,
                )+
            }

            impl Unsigned {
                /// Create an unsigned scalar from a bit width.
                #[inline]
                #[must_use]
                pub const fn from_width(bits: u32) -> Option<Unsigned> {
                    match bits {
                        8 => Some(Unsigned::U8),
                        16 => Some(Unsigned::U16),
                        32 => Some(Unsigned::U32),
                        64 => Some(Unsigned::U64),
                        128 => Some(Unsigned::U128),
                        _ => None,
                    }
                }

                /// Get the name of this scalar.
                #[inline]
                #[must_use]
                pub const fn name(self) -> &'static str {
                    match self {
                        $(Self::$unsigned => stringify!([<$unsigned:lower>]),)+
                    }
                }

                /// Get the pascal case name of this scalar.
                #[inline]
                #[must_use]
                pub const fn pascal_name(self) -> &'static str {
                    match self {
                        $(Self::$unsigned => stringify!($unsigned),)+
                    }
                }

                /// Get the bit width of this scalar.
                ///
                /// Returns `None` if it is platform dependent.
                #[inline]
                #[must_use]
                pub const fn width(self) -> Option<NonZero<u32>> {
                    match self {
                        $(Self::$unsigned => const {
                            let name = Self::$unsigned.name().as_bytes();

                            if let b"usize" = name {
                                None
                            } else {
                               Some(NonZero::new([<$unsigned:lower>]::BITS).unwrap())
                            }
                        },)+
                    }
                }

                /// Get the signed variant of this scalar.
                #[inline]
                #[must_use]
                pub const fn signed(self) -> Signed {
                    match self {
                        $(Self::$unsigned => Signed::$signed,)+
                    }
                }

                /// Get the minimum of this scalar.
                #[inline]
                #[must_use]
                pub const fn min(self) -> Option<i128> {
                    match self {
                        $( Self::$unsigned => const {
                            let name = Self::$unsigned.name().as_bytes();

                            if let b"usize" = name {
                                None
                            } else {
                                Some([<$unsigned:lower>]::MIN as i128)
                            }
                        }, )+
                    }
                }

                /// Get the maximum of this scalar.
                #[inline]
                #[must_use]
                pub const fn max(self) -> Option<u128> {
                    match self {
                        $(Self::$unsigned => const {
                            let name = Self::$unsigned.name().as_bytes();

                            if let b"usize" = name {
                                None
                            } else {
                                Some([<$unsigned:lower>]::MAX as u128)
                            }

                        },)+
                    }
                }
            }


            impl fmt::Display for Unsigned {
                #[inline]
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    f.write_str(self.name())
                }
            }

            /// Signed scalars.
            #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
            pub enum Signed {
                $(
                    $signed,
                )+
            }

            impl Signed {
                /// Create a signed scalar from a bit width.
                #[inline]
                #[must_use]
                pub const fn from_width(bits: u32) -> Option<Signed> {
                    match bits {
                        8 => Some(Signed::I8),
                        16 => Some(Signed::I16),
                        32 => Some(Signed::I32),
                        64 => Some(Signed::I64),
                        128 => Some(Signed::I128),
                        _ => None,
                    }
                }

                /// Get the name of this scalar.
                #[inline]
                #[must_use]
                pub const fn name(self) -> &'static str {
                    match self {
                        $(Self::$signed => stringify!([<$signed:lower>]),)+
                    }
                }

                /// Get the pascal case name of this scalar.
                #[inline]
                #[must_use]
                pub const fn pascal_name(self) -> &'static str {
                    match self {
                        $(Self::$signed => stringify!($signed),)+
                    }
                }

                /// Get the bit width of this scalar.
                ///
                /// Returns `None` if it is platform dependent.
                #[inline]
                #[must_use]
                pub const fn width(self) -> Option<NonZero<u32>> {
                    match self {
                        $(Self::$signed => const {
                            let name = Self::$signed.name().as_bytes();

                            if let b"isize" = name {
                                None
                            } else {
                               Some(NonZero::new([<$signed:lower>]::BITS).unwrap())
                            }
                        },)+
                    }
                }

                /// Get the [`Unsigned`] variant of this scalar.
                #[inline]
                #[must_use]
                pub const fn unsigned(self) -> Unsigned {
                    match self {
                        $(Self::$signed => Unsigned::$unsigned,)+
                    }
                }

                /// Get the maximum value of this scalar.
                #[inline]
                #[must_use]
                pub const fn max(self) -> Option<u128> {
                    match self {
                        $(
                            Self::$signed => const {
                                let name = Self::$signed.name().as_bytes();

                                if let b"isize" = name {
                                    None
                                } else {
                                    Some([<$signed:lower>]::MAX as u128)
                                }
                            },
                        )+
                    }
                }

                /// Get the minimum value of this scalar.
                #[inline]
                #[must_use]
                pub const fn min(self) -> Option<i128> {
                    match self {
                        $(
                            Self::$signed => const {
                                let name = Self::$signed.name().as_bytes();

                                if let b"isize" = name {
                                    None
                                } else {
                                    Some([<$signed:lower>]::MIN as i128)
                                }
                            },
                        )+
                    }
                }
            }

            impl fmt::Display for Signed {
                #[inline]
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    f.write_str(self.name())
                }
            }
        }
    };
}

scalars! {
    U8 <=> I8,
    U16 <=> I16,
    U32 <=> I32,
    U64 <=> I64,
    U128 <=> I128,
    Usize <=> Isize,
}
