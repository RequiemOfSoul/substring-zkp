#[allow(clippy::useless_attribute)]
use ark_ff::{BitIteratorBE, PrimeField};
use ark_std::ops::Deref;

#[derive(Clone, Debug)]
pub struct StringWitness<F: PrimeField> {
    bytes: Vec<u8>,
    frs: Vec<F>,
    length: usize,
}

impl<F: PrimeField> Deref for StringWitness<F> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &*self.bytes
    }
}

impl<F: PrimeField> StringWitness<F> {
    fn get_vec(&self) -> &[u8] {
        &self.bytes
    }
    fn get_frs(&self) -> &[F] {
        &self.frs
    }
}

impl<F: PrimeField> From<String> for StringWitness<F> {
    fn from(s: String) -> Self {
        let bytes = s.into_bytes();
        let bits = from_be_bytes(&bytes);
        let frs = le_bit_vector_into_field_element(&bits);
        StringWitness {
            bytes,
            frs: vec![frs],
            length: 1,
        }
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

pub fn append_be_fixed_width<P: PrimeField>(content: &mut Vec<bool>, x: &P, width: usize) {
    let mut bits: Vec<bool> = BitIteratorBE::new(x.into_repr()).collect();
    bits.reverse();
    bits.resize(width, false);
    bits.reverse();
    content.extend(bits);
}
