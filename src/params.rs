#[allow(clippy::useless_attribute)]

pub const MIN_PREFIX_LENGTH: usize = 64;
pub const PREFIX_LENGTH: usize = 128;
pub const PREFIX_FR_LENGTH: usize = PREFIX_LENGTH / 31 + 1;

pub const MIN_SECRET_LENGTH: usize = 6;
pub const SECRET_LENGTH: usize = 100;
pub const SECRET_FR_LENGTH: usize = SECRET_LENGTH / 31 + 1;

pub const MIN_SUFFIX_LENGTH: usize = 768;
pub const SUFFIX_LENGTH: usize = 1024;
pub const SUFFIX_FR_LENGTH: usize = SUFFIX_LENGTH / 31 + 1;

pub const MIN_PREFIX_BIT_WIDTH: usize = MIN_PREFIX_LENGTH * 8;
pub const PREFIX_BIT_WIDTH: usize = PREFIX_LENGTH * 8;
pub const MIN_SECRET_BIT_WIDTH: usize = MIN_SECRET_LENGTH * 8;
pub const SECRET_BIT_WIDTH: usize = SECRET_LENGTH * 8;
pub const MIN_SUFFIX_BIT_WIDTH: usize = MIN_SUFFIX_LENGTH * 8;
pub const SUFFIX_BIT_WIDTH: usize = SUFFIX_LENGTH * 8;

pub const MIN_HASH_PREIMAGE_LENGTH: usize =
    MIN_PREFIX_LENGTH + MIN_SUFFIX_LENGTH + MIN_SECRET_LENGTH;

pub const MAX_HASH_PREIMAGE_LENGTH: usize = PREFIX_LENGTH + SUFFIX_LENGTH + SECRET_LENGTH;
pub const MAX_HASH_PREIMAGE_BIT_WIDTH: usize = MAX_HASH_PREIMAGE_LENGTH * 8;

pub const CHUNK_BIT_WIDTH: usize = 8 * 8;
pub const LENGTH_REPR_BIT_WIDTH: usize = 16;
