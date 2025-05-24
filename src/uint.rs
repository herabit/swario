use crate::macros::define;

define!(U8x2[u8; 2] => u16 {});
define!(U8x4[u8; 4] => u32 {});
define!(U8x8[u8; 8] => u64 {});
define!(U8x16[u8; 16] => u128 {});

define!(U16x2[u16; 2] => u32 {});
define!(U16x4[u16; 4] => u64 {});
define!(U16x8[u16; 8] => u128 {});

define!(U32x2[u32; 2] => u64 {});
define!(U32x4[u32; 4] => u128 {});

define!(U64x2[u64; 2] => u128 {});
