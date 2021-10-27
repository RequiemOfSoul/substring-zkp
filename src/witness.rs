use crate::circuit::SecretStringCircuit;
use crate::params::{
    CHUNK_WIDTH, FR_CHUNKS_BIT_WIDTH, MAX_HASH_PREIMAGE_LENGTH, MAX_PREFIX_LENGTH,
    MAX_SECRET_LENGTH, MIN_PREFIX_LENGTH, MIN_SECRET_LENGTH, MIN_SUFFIX_LENGTH,
    PADDING_SUFFIX_LENGTH, PREFIX_FR_LENGTH, SECRET_FR_LENGTH, SUFFIX_FR_LENGTH,
};
use ark_ff::{BitIteratorBE, PrimeField};
#[allow(clippy::useless_attribute)]
use sha2::{Digest, Sha256};

#[derive(Clone, Debug)]
pub struct SecretWitness<F: PrimeField> {
    // padding bytes
    prefix_bytes: Vec<u8>,
    secret_bytes: Vec<u8>,
    suffix_bytes: Vec<u8>,
    message_bytes: Vec<u8>,

    // (padding, length)
    prefix: (Vec<F>, usize),
    secret: (Vec<F>, usize),
    suffix: (Vec<F>, usize),

    message_circuit_bytes: Vec<F>,
    pub secret_commitment: Option<F>,
    pub message_hash: Option<F>,
    pub public_input_hash: Option<F>,
}

impl<F: PrimeField> SecretWitness<F> {
    pub fn generate_witness(secret: String, message: String) -> SecretWitness<F> {
        let split_message = message.split(&secret).collect::<Vec<&str>>();
        let prefix = split_message
            .first()
            .expect("Secret don't split message")
            .to_string()
            .into_bytes();
        let suffix = split_message
            .last()
            .expect("Secret don't split message")
            .to_string()
            .into_bytes();

        let mut secret_witness = SecretWitness::default();
        secret_witness
            .absorb_prefix(&prefix)
            .absorb_secret(secret.as_bytes())
            .absorb_suffix(&suffix)
            .finalize_hash(message.into_bytes());

        secret_witness
    }

    pub fn into_circuit_instance(self) -> SecretStringCircuit<F> {
        SecretStringCircuit {
            prefix_padding: Some(self.prefix.0),
            prefix_length: Some(F::from(self.prefix.1 as u128)),
            secret_padding: Some(self.secret.0),
            secret_length: Some(F::from(self.secret.1 as u128)),
            suffix_padding: Some(self.suffix.0),
            suffix_length: Some(F::from(self.suffix.1 as u128)),
            secret: None,
            message: Some(self.message_circuit_bytes),
            secret_hash: self.secret_commitment,
            message_hash: self.message_hash,
            pub_data_hash: self.public_input_hash,
        }
    }

    // Not circuit's really public input, it's just a formality
    pub fn get_raw_public_input(&self) -> Vec<F> {
        let mut public_input = Vec::with_capacity(PREFIX_FR_LENGTH + SUFFIX_FR_LENGTH + 2);
        public_input.extend_from_slice(&self.prefix.0);
        public_input.extend_from_slice(&self.suffix.0);
        public_input.push(self.secret_commitment.unwrap());
        public_input.push(self.message_hash.unwrap());
        public_input
    }

    pub fn get_compress_public_input(&self) -> F {
        if let Some(public_input) = self.public_input_hash {
            public_input
        } else {
            let secret_commitment = calculate_hash(&self.secret_bytes);
            let signature_msg_hash = calculate_hash(&self.message_bytes);
            let public_input_hash = compress_public_input(
                &self.prefix_bytes,
                &self.suffix_bytes,
                &secret_commitment,
                &signature_msg_hash,
            );
            F::read(&*public_input_hash).expect("packed public input hash hash error")
        }
    }

    fn get_prefix(&self) -> &[F] {
        &self.prefix.0
    }

    fn get_secret(&self) -> &[F] {
        &self.secret.0
    }

    fn get_suffix(&self) -> &[F] {
        &self.suffix.0
    }
}

impl<F: PrimeField> Default for SecretWitness<F> {
    fn default() -> Self {
        SecretWitness {
            prefix_bytes: vec![],
            secret_bytes: vec![],
            suffix_bytes: vec![],
            message_bytes: vec![],
            prefix: (vec![Default::default(); PREFIX_FR_LENGTH], 0),
            secret: (vec![Default::default(); SECRET_FR_LENGTH], 0),
            suffix: (vec![Default::default(); SUFFIX_FR_LENGTH], 0),
            message_circuit_bytes: vec![Default::default(); MAX_HASH_PREIMAGE_LENGTH],
            secret_commitment: None,
            message_hash: None,
            public_input_hash: None,
        }
    }
}

impl<F: PrimeField> SecretWitness<F> {
    fn absorb_prefix(&mut self, prefix: &[u8]) -> &mut Self {
        let length = prefix.len();
        assert!(MIN_PREFIX_LENGTH <= length && length <= MAX_PREFIX_LENGTH);
        let (split_fe_vec, padding_bytes) = append_fr_chunk_fixed_width(prefix, PREFIX_FR_LENGTH);

        self.prefix_bytes = padding_bytes;
        self.prefix = (split_fe_vec, length);
        self
    }

    fn absorb_secret(&mut self, secret: &[u8]) -> &mut Self {
        let length = secret.len();
        assert!(MIN_SECRET_LENGTH <= length && length <= MAX_SECRET_LENGTH);

        let (split_fe_vec, padding_bytes) = append_fr_chunk_fixed_width(secret, SECRET_FR_LENGTH);

        self.secret_bytes = padding_bytes;
        self.secret = (split_fe_vec, length);
        self
    }

    fn absorb_suffix(&mut self, suffix: &[u8]) -> &mut Self {
        let length = suffix.len();
        assert!(MIN_SUFFIX_LENGTH <= length && length <= PADDING_SUFFIX_LENGTH);

        let (split_fe_vec, padding_bytes) = append_fr_chunk_fixed_width(suffix, SUFFIX_FR_LENGTH);

        self.suffix_bytes = padding_bytes;
        self.suffix = (split_fe_vec, length);
        self
    }

    fn finalize_hash(&mut self, message: Vec<u8>) {
        let secret_commitment = calculate_hash(&self.secret_bytes);
        let signature_msg_hash = calculate_hash(&self.message_bytes);

        // for reduce verification key size.
        let public_input_hash = compress_public_input(
            &self.prefix_bytes,
            &self.suffix_bytes,
            &secret_commitment,
            &signature_msg_hash,
        );

        self.message_circuit_bytes = message.iter().map(|&byte| F::from(byte as u128)).collect();
        self.message_bytes = message;

        self.secret_commitment =
            Some(F::read(&*secret_commitment).expect("packed secret commitment error"));
        self.message_hash =
            Some(F::read(&*signature_msg_hash).expect("packed signature message hash error"));
        self.public_input_hash =
            Some(F::read(&*public_input_hash).expect("packed public input hash hash error"));
    }
}

fn part_string_padding<F: PrimeField>(part: &[u8]) -> F {
    let mut part_vec = part.to_vec();
    part_vec.resize(32, 0);
    F::read(&*part_vec).expect("pack part string as field element")
}

pub fn calculate_hash(preimage: &[u8]) -> Vec<u8> {
    let mut h = Sha256::new();
    h.update(&preimage);

    let mut hash_result = h.finalize().to_vec();
    hash_result.reverse();
    hash_result[31] &= 0x1f;

    hash_result
}

pub fn from_be_bytes(bytes: &[u8]) -> Vec<bool> {
    let mut bits = vec![];
    for byte in bytes {
        let mut temp = *byte;
        for _ in 0..8 {
            bits.push(temp & 0x80 == 0x80);
            temp <<= 1;
        }
    }
    bits
}

pub fn le_bit_vector_into_field_element<F: PrimeField>(bits: &[bool]) -> F {
    let mut fe = F::zero();
    let mut base = F::one();
    for bit in bits {
        if *bit {
            fe.add_assign(&base);
        }
        base = base.double();
    }
    fe
}

pub fn append_be_fixed_width<F: PrimeField>(content: &mut Vec<bool>, x: &F, width: usize) {
    let mut bits: Vec<bool> = BitIteratorBE::new(x.into_repr()).collect();
    bits.reverse();
    bits.resize(width, false);
    bits.reverse();
    content.extend(bits);
}

pub fn append_fr_chunk_fixed_width<F: PrimeField>(
    raw_bytes: &[u8],
    number_frs: usize,
) -> (Vec<F>, Vec<u8>) {
    let mut split_fe_vec = raw_bytes
        .chunks(CHUNK_WIDTH)
        .map(part_string_padding)
        .collect::<Vec<_>>();
    split_fe_vec.resize(number_frs, F::zero());

    let mut padding_bytes = raw_bytes.to_vec();
    padding_bytes.resize(number_frs * CHUNK_WIDTH, 0);

    (split_fe_vec, padding_bytes)
}

pub fn compress_public_input(
    prefix_bytes: &[u8],
    suffix_bytes: &[u8],
    secret_commitment: &[u8],
    msg_hash: &[u8],
) -> Vec<u8> {
    let mut public_inputs = Vec::new();
    public_inputs.extend_from_slice(prefix_bytes);
    public_inputs.extend_from_slice(suffix_bytes);
    public_inputs.extend_from_slice(secret_commitment);
    public_inputs.extend_from_slice(msg_hash);

    let mut h = Sha256::new();
    h.update(&public_inputs);
    let mut public_input_hash = h.finalize().to_vec();
    public_input_hash.reverse();
    public_input_hash[31] &= 0x1f;

    public_input_hash
}
