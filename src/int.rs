use crate::macros::define;

define!(I8x2[i8; 2] => u16 {});
define!(I8x4[i8; 4] => u32 {});
define!(I8x8[i8; 8] => u64 {});
define!(I8x16[i8; 16] => u128 {});

define!(I16x2[i16; 2] => u32 {});
define!(I16x4[i16; 4] => u64 {});
define!(I16x8[i16; 8] => u128 {});

define!(I32x2[i32; 2] => u64 {});
define!(I32x4[i32; 4] => u128 {});

define!(I64x2[i64; 2] => u128  {});
