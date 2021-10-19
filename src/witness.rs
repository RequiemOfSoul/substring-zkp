use crate::circuit::SecretStringCircuit;
use crate::params::{
    MAX_HASH_PREIMAGE_LENGTH, PREFIX_FR_LENGTH, SECRET_FR_LENGTH, SUFFIX_FR_LENGTH,
};
use ark_ff::{BitIteratorBE, PrimeField};
#[allow(clippy::useless_attribute)]
use sha2::{Digest, Sha256};

#[derive(Clone, Debug)]
pub struct SecretWitness<F: PrimeField> {
    // (padding, length)
    prefix: (Vec<F>, usize),
    secret: (Vec<F>, usize),
    suffix: (Vec<F>, usize),
    message_bytes: Vec<F>,
    pub secret_commitment: Option<F>,
    pub message_hash: Option<F>,
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
            .finalize_hash(secret.into_bytes(), message.into_bytes());

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
            message: Some(self.message_bytes),
            secret_hash: self.secret_commitment,
            message_hash: self.message_hash,
        }
    }

    pub fn get_public_input(&self) -> Vec<F> {
        let mut public_input = Vec::with_capacity(PREFIX_FR_LENGTH + SUFFIX_FR_LENGTH + 2);
        public_input.extend_from_slice(&self.prefix.0);
        public_input.extend_from_slice(&self.suffix.0);
        public_input.push(self.secret_commitment.unwrap());
        public_input.push(self.message_hash.unwrap());
        public_input
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
            prefix: (vec![Default::default(); PREFIX_FR_LENGTH], 0),
            secret: (vec![Default::default(); SECRET_FR_LENGTH], 0),
            suffix: (vec![Default::default(); SUFFIX_FR_LENGTH], 0),
            message_bytes: vec![Default::default(); MAX_HASH_PREIMAGE_LENGTH],
            secret_commitment: None,
            message_hash: None,
        }
    }
}

impl<F: PrimeField> SecretWitness<F> {
    fn absorb_prefix(&mut self, prefix: &[u8]) -> &mut Self {
        let length = prefix.len();
        let mut split_fe_vec = prefix
            .chunks(31)
            .map(part_string_padding)
            .collect::<Vec<_>>();
        split_fe_vec.resize(PREFIX_FR_LENGTH, F::zero());
        self.prefix = (split_fe_vec, length);
        self
    }

    fn absorb_secret(&mut self, secret: &[u8]) -> &mut Self {
        let length = secret.len();
        let mut split_fe_vec = secret
            .chunks(31)
            .map(part_string_padding)
            .collect::<Vec<_>>();
        split_fe_vec.resize(SECRET_FR_LENGTH, F::zero());
        self.secret = (split_fe_vec, length);
        self
    }

    fn absorb_suffix(&mut self, suffix: &[u8]) -> &mut Self {
        let length = suffix.len();
        let mut split_fe_vec = suffix
            .chunks(31)
            .map(part_string_padding)
            .collect::<Vec<_>>();
        split_fe_vec.resize(SUFFIX_FR_LENGTH, F::zero());
        self.suffix = (split_fe_vec, length);
        self
    }

    fn finalize_hash(&mut self, secret: Vec<u8>, message: Vec<u8>) {
        let mut secret_padding = secret;
        secret_padding.resize(SECRET_FR_LENGTH * 31, 0);

        let mut h = Sha256::new();
        h.update(&secret_padding);
        let mut secret_commitment = h.finalize().to_vec();
        secret_commitment.reverse();
        secret_commitment[31] &= 0x1f;

        let mut h = Sha256::new();
        h.update(&message);
        let mut signature_msg_hash = h.finalize().to_vec();
        signature_msg_hash.reverse();
        signature_msg_hash[31] &= 0x1f;

        self.message_bytes = message.iter().map(|&byte| F::from(byte as u128)).collect();
        self.secret_commitment =
            Some(F::read(&*secret_commitment).expect("packed secret commitment error"));
        self.message_hash =
            Some(F::read(&*signature_msg_hash).expect("packed signature message hash error"));
    }
}

fn part_string_padding<F: PrimeField>(part: &[u8]) -> F {
    let mut part_vec = part.to_vec();
    part_vec.resize(32, 0);
    F::read(&*part_vec).expect("pack part string as field element")
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

#[test]
fn test_secret_witness() {}
