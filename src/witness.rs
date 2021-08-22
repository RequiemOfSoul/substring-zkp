#[allow(clippy::useless_attribute)]
use ark_ff::{FpParameters, PrimeField};
use ark_std::ops::Deref;

pub struct CircuitString<F: PrimeField> {
    bytes: Vec<u8>,
    frs: Vec<F>,
    length: usize,
}

impl<F: PrimeField> CircuitString<F> {
    fn into_vec(self) -> Vec<u8> {
        self.bytes
    }
    fn into_frs(self) -> Vec<F> {
        self.frs
    }
}

impl<F: PrimeField> From<(String, usize)> for CircuitString<F> {
    fn from(s: (String, usize)) -> Self {
        let cap = F::Params::CAPACITY as usize;
        let length = if s.0.len() % cap != 0 {
            s.0.len() / cap + 1
        } else {
            s.0.len() / cap
        };
        assert!(
            length * cap > s.1 * 8,
            "The length of the string exceeds the specified length."
        );
        let bytes = s.0.into_bytes();
        let bits = from_be_bytes(&bytes);
        let frs = le_bit_vector_into_field_element(&bits);
        CircuitString {
            bytes,
            frs: vec![frs],
            length,
        }
    }
}

impl<F: PrimeField> Deref for CircuitString<F> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &*self.bytes
    }
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
