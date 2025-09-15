use core::fmt;
use core::num::NonZero;

const fn lane_counts(bits: u32) -> &'static [NonZero<u32>] {
    macro_rules! counts {
        ($($count:expr),*) => {
            [$(NonZero::new($count).unwrap(),)*]
        };
    }

    const COUNTS: &[NonZero<u32>] = &counts![1, 2, 4, 8, 16];

    let end = match bits {
        8 => COUNTS.len(),
        16 => COUNTS.len() - 1,
        32 => COUNTS.len() - 2,
        64 => COUNTS.len() - 3,
        128 => COUNTS.len() - 4,
        _ => 0,
    };

    COUNTS.split_at(end).0
}

macro_rules! int_common {
    (
        $(#[$meta:meta])*
        pub enum $name:ident {
            $(
                $(#[$var_meta:meta])*
                $var_pascal:ident/$var_snake:ident {
                    inverse: $var_inv:ident
                    $(, half: $var_half:ident)?
                    $(, double: $var_double:ident)?
                    $(, bits: $bits:tt)?
                    $(,)?
                }
            ),+

            $(,)?
        }

        impl Self {
            $(#[$inv_meta:meta])*
            pub const fn $inv_fn:ident(self) -> $inv:ident;
        }
    ) => {
        $(#[$meta])*
        pub enum $name {
            $(
                $(#[$var_meta])*
                $var_pascal
            ),+
        }

        impl $name {
            pub const ALL: &[$name] = &[$($name::$var_pascal,)+];

            #[doc = concat!(
                "Given some bit width, get the [`", stringify!($name), "`] variant ",
                "with an equivalent size in bits."
            )]
            #[inline]
            #[must_use]
            pub const fn from_width(bits: u32) -> Option<$name> {
                match bits {
                    $(
                        $( $bits => Some($name::$var_pascal), )?
                    )+
                    _ => None,
                }
            }

            /// Get the bit width of this scalar if it is static.
            #[inline]
            #[must_use]
            pub const fn width(self) -> Option<NonZero<u32>> {
                match self {
                    $(
                        $( $name::$var_pascal => const { Some(NonZero::new($bits).unwrap()) }, )?
                    )+
                    _ => None,
                }
            }

            /// Get a scalar half the width of this one, if it exists.
            #[inline]
            #[must_use]
            pub const fn half_width(self) -> Option<$name> {
                match self {
                    $(
                        $( $name::$var_pascal => Some($name::$var_half), )?
                    )+
                    _ => None,
                }
            }

            /// Get a scalar double the width of this one, if it exists.
            #[inline]
            #[must_use]
            pub const fn double_width(self) -> Option<$name> {
                match self {
                    $(
                        $( $name::$var_pascal => Some($name::$var_double), )?
                    )+
                    _ => None,
                }
            }

            $(#[$inv_meta])*
            #[inline]
            #[must_use]
            pub const fn $inv_fn(self) -> $inv {
                match self {
                    $( $name::$var_pascal => $inv::$var_inv, )+
                }
            }

            /// Get the name of this scalar.
            #[inline]
            #[must_use]
            pub const fn name(self) -> &'static str {
                match self {
                    $( $name::$var_pascal => stringify!($var_snake), )+
                }
            }

            /// Get the pascal-case name of this scalar.
            #[inline]
            #[must_use]
            pub const fn pascal_name(self) -> &'static str {
                match self {
                    $( $name::$var_pascal => stringify!($var_pascal), )+
                }
            }

            /// Get a list of lane counts.
            #[inline]
            #[must_use]
            pub const fn lane_counts(self) -> &'static [NonZero<u32>] {
                let width = match self.width() {
                    Some(width) => width.get(),
                    None => 0,
                };

                lane_counts(width)
            }

            /// Get the minimum of this scalar.
            #[inline]
            #[must_use]
            pub const fn min(self) -> Option<i128> {
                match self {
                    $( $(
                        $name::$var_pascal => const {
                            let _ = $bits;

                            Some($var_snake::MIN as i128)
                        },
                    )? )+
                    _ => None,
                }
            }

            /// Get the maximum of this scalar.
            #[inline]
            #[must_use]
            pub const fn max(self) -> Option<u128> {
                match self {
                    $( $(
                        $name::$var_pascal => const {
                            let _ = $bits;

                            Some($var_snake::MAX as u128)
                        },
                    )? )+
                    _ => None,
                }
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str(self.name())
            }
        }
    };
}

int_common! {
    /// An enum of all the possible unsigned integers we may want to support.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum Unsigned {
        U8/u8 {
            inverse: I8,
            double: U16,
            bits: 8,
        },
        U16/u16 {
            inverse: I16,
            half: U8,
            double: U32,
            bits: 16,
        },
        U32/u32 {
            inverse: I32,
            half: U16,
            double: U64,
            bits: 32,
        },
        U64/u64 {
            inverse: I64,
            half: U32,
            double: U128,
            bits: 64,
        },
        U128/u128 {
            inverse: I128,
            half: U64,
            bits: 128,
        },
        Usize/usize {
            inverse: Isize,
        },
    }

    impl Self {
        /// Get the [`Signed`] equivalent of this [`Unsigned`].
        pub const fn to_signed(self) -> Signed;
    }
}

int_common! {
    /// An enum of all the possible signed integers we may want to support.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum Signed {
        I8/i8 {
            inverse: U8,
            double: I16,
            bits: 8,
        },
        I16/i16 {
            inverse: U16,
            half: I8,
            double: I32,
            bits: 16,
        },
        I32/i32 {
            inverse: U32,
            half: I16,
            double: I64,
            bits: 32,
        },
        I64/i64 {
            inverse: U64,
            half: I32,
            double: I128,
            bits: 64,
        },
        I128/i128 {
            inverse: U128,
            half: I64,
            bits: 128,
        },
        Isize/isize {
            inverse: Usize,
        },
    }

    impl Self {
        /// Get the [`Unsigned`] equivalent of this [`Signed`].
        pub const fn to_unsigned(self) -> Unsigned;
    }
}

/// An enum for all scalars we may want to support.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Scalar {
    Unsigned(Unsigned),
    Signed(Signed),
}

impl Scalar {
    pub const ALL: &[Scalar] = &{
        let mut all = [Scalar::Unsigned(Unsigned::U8); Unsigned::ALL.len() + Signed::ALL.len()];
        let (unsigned, signed) = all.split_at_mut(Unsigned::ALL.len());

        let mut index = 0_usize;
        while index < Unsigned::ALL.len() {
            unsigned[index] = Scalar::Unsigned(Unsigned::ALL[index]);
            index += 1;
        }

        let mut index = 0_usize;
        while index < Signed::ALL.len() {
            signed[index] = Scalar::Signed(Signed::ALL[index]);
            index += 1;
        }

        all
    };

    #[inline]
    #[must_use]
    pub const fn to_signed(self) -> Option<Signed> {
        match self {
            Scalar::Unsigned(unsigned) => Some(unsigned.to_signed()),
            Scalar::Signed(signed) => Some(signed),
        }
    }

    #[inline]
    #[must_use]
    pub const fn to_unsigned(self) -> Option<Unsigned> {
        match self {
            Scalar::Unsigned(unsigned) => Some(unsigned),
            Scalar::Signed(signed) => Some(signed.to_unsigned()),
        }
    }

    #[inline]
    #[must_use]
    pub const fn width(self) -> Option<NonZero<u32>> {
        match self {
            Scalar::Unsigned(unsigned) => unsigned.width(),
            Scalar::Signed(signed) => signed.width(),
        }
    }

    #[inline]
    #[must_use]
    pub const fn half_width(self) -> Option<Scalar> {
        match self {
            Scalar::Unsigned(unsigned) => match unsigned.half_width() {
                Some(half) => Some(Scalar::Unsigned(half)),
                None => None,
            },
            Scalar::Signed(signed) => match signed.half_width() {
                Some(half) => Some(Scalar::Signed(half)),
                None => None,
            },
        }
    }

    #[inline]
    #[must_use]
    pub const fn double_width(self) -> Option<Scalar> {
        match self {
            Scalar::Unsigned(unsigned) => match unsigned.double_width() {
                Some(double) => Some(Scalar::Unsigned(double)),
                None => None,
            },
            Scalar::Signed(signed) => match signed.double_width() {
                Some(double) => Some(Scalar::Signed(double)),
                None => None,
            },
        }
    }

    #[inline]
    #[must_use]
    pub const fn min(self) -> Option<i128> {
        match self {
            Scalar::Unsigned(unsigned) => unsigned.min(),
            Scalar::Signed(signed) => signed.min(),
        }
    }

    #[inline]
    #[must_use]
    pub const fn max(self) -> Option<u128> {
        match self {
            Scalar::Unsigned(unsigned) => unsigned.max(),
            Scalar::Signed(signed) => signed.max(),
        }
    }

    #[inline]
    #[must_use]
    pub const fn lane_counts(self) -> &'static [NonZero<u32>] {
        match self {
            Scalar::Unsigned(unsigned) => unsigned.lane_counts(),
            Scalar::Signed(signed) => signed.lane_counts(),
        }
    }

    #[inline]
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Scalar::Unsigned(unsigned) => unsigned.name(),
            Scalar::Signed(signed) => signed.name(),
        }
    }

    #[inline]
    #[must_use]
    pub const fn pascal_name(self) -> &'static str {
        match self {
            Scalar::Unsigned(unsigned) => unsigned.pascal_name(),
            Scalar::Signed(signed) => signed.pascal_name(),
        }
    }

    #[inline]
    #[must_use]
    pub const fn is_signed(self) -> bool {
        matches!(self, Scalar::Signed(..))
    }

    #[inline]
    #[must_use]
    pub const fn is_unsigned(self) -> bool {
        matches!(self, Scalar::Unsigned(..))
    }
}

impl From<Unsigned> for Scalar {
    #[inline]
    fn from(value: Unsigned) -> Self {
        Scalar::Unsigned(value)
    }
}

impl From<Signed> for Scalar {
    #[inline]
    fn from(value: Signed) -> Self {
        Scalar::Signed(value)
    }
}

impl fmt::Display for Scalar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}
