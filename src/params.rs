pub const MIN_PREFIX_LENGTH: usize = 64;
pub const MAX_PREFIX_LENGTH: usize = 128;
pub const PREFIX_FR_LENGTH: usize = MAX_PREFIX_LENGTH / 31 + 1; // If it's divisible without adding 1

pub const MIN_SECRET_LENGTH: usize = 6;
pub const MAX_SECRET_LENGTH: usize = 100;
pub const SECRET_FR_LENGTH: usize = MAX_SECRET_LENGTH / 31 + 1; // If it's divisible without adding 1

pub const MIN_SUFFIX_LENGTH: usize = 768;
pub const MAX_SUFFIX_LENGTH: usize = 1024;

// The suffix needs to be padded to MAX_HASH_PREIMAGE_LENGTH
pub const PADDING_SUFFIX_LENGTH: usize =
    MAX_HASH_PREIMAGE_LENGTH - MIN_PREFIX_LENGTH - MIN_SECRET_LENGTH;
pub const SUFFIX_FR_LENGTH: usize = PADDING_SUFFIX_LENGTH / 31 + 1; // If it's divisible without adding 1

pub const MIN_PREFIX_BIT_WIDTH: usize = MIN_PREFIX_LENGTH * 8;
pub const MAX_PREFIX_BIT_WIDTH: usize = MAX_PREFIX_LENGTH * 8;

pub const MIN_SECRET_BIT_WIDTH: usize = MIN_SECRET_LENGTH * 8;
pub const MAX_SECRET_BIT_WIDTH: usize = MAX_SECRET_LENGTH * 8;

pub const MIN_SUFFIX_BIT_WIDTH: usize = MIN_SUFFIX_LENGTH * 8;
pub const MAX_SUFFIX_BIT_WIDTH: usize = MAX_SUFFIX_LENGTH * 8;

pub const MIN_HASH_PREIMAGE_LENGTH: usize =
    MIN_PREFIX_LENGTH + MIN_SUFFIX_LENGTH + MIN_SECRET_LENGTH;
pub const MAX_HASH_PREIMAGE_LENGTH: usize =
    MAX_PREFIX_LENGTH + MAX_SUFFIX_LENGTH + MAX_SECRET_LENGTH;

pub const MIN_HASH_PREIMAGE_BIT_WIDTH: usize = MIN_HASH_PREIMAGE_LENGTH * 8;
pub const MAX_HASH_PREIMAGE_BIT_WIDTH: usize = MAX_HASH_PREIMAGE_LENGTH * 8;

pub const CHUNK_BIT_WIDTH: usize = 8 * 8;
pub const LENGTH_REPR_BIT_WIDTH: usize = 11; // 2^LENGTH_REPR_BIT_WIDTH > MAX_HASH_PREIMAGE_BIT_WIDTH
