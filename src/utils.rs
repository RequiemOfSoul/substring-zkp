use crate::circuit::SecretStringCircuit;
use ark_bn254::fr::Fr;
use ark_ff::{FpParameters, FromBytes, PrimeField};
use ckb_gadgets::algebra::boolean::Boolean;
use ckb_gadgets::algebra::fr::AllocatedFr;
use ckb_r1cs::{ConstraintSystem, LinearCombination, SynthesisError};
use sha2::{Digest, Sha256};

pub fn pack_bits_to_element<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    mut bits: Vec<Boolean>,
) -> Result<Vec<Boolean>, SynthesisError> {
    bits.chunks_mut(8).for_each(|bit| bit.reverse());
    bits.truncate(F::Params::CAPACITY as usize);
    assert!(
        bits.len() <= F::Params::MODULUS_BITS as usize,
        "can not pack bits into field element"
    );

    let mut data_from_lc = LinearCombination::<F>::zero();
    let mut value = F::zero();
    let mut coeff = F::one();
    for bit8 in bits.chunks(8) {
        for bit in bit8.iter() {
            data_from_lc = data_from_lc + bit.lc(CS::one(), coeff);
            if let Some(bit) = bit.get_value() {
                if bit {
                    value.add_assign(coeff);
                }
            }
            coeff = coeff.double();
        }
    }

    let data_packed = AllocatedFr::alloc_input(cs.ns(|| "allocate data packed"), || Ok(value))?;

    cs.enforce(
        || "pack bits into fe",
        |lc| lc + data_packed.get_variable(),
        |lc| lc + CS::one(),
        |_| LinearCombination::zero() + (F::one(), data_from_lc),
    );

    bits.resize(256, Boolean::Constant(false));
    bits.chunks_mut(8).for_each(|bit| bit.reverse());
    Ok(bits)
}

pub fn generate_circuit_instance(
    a: String,
    b: String,
    secret: String,
    _string_length: usize,
) -> (SecretStringCircuit, Vec<Fr>) {
    assert!(a.len() <= 64);
    assert!(secret.len() <= 32);
    assert!(b.len() <= 512);

    let mut a_bytes = a.into_bytes();
    a_bytes.resize(64, 0);
    let mut b_bytes = b.into_bytes();
    b_bytes.resize(512, 0);
    let mut secret_bytes = secret.into_bytes();
    secret_bytes.resize(32, 0);

    a_bytes[31] &= 0x1f;
    b_bytes[31] &= 0x1f;
    secret_bytes[31] &= 0x1f;

    let mut h = Sha256::new();
    h.update(&secret_bytes);
    let mut secret_commitment = h.finalize().to_vec();

    let mut all_string = Vec::with_capacity(a_bytes.len() + b_bytes.len() + secret_bytes.len());
    all_string.extend_from_slice(&a_bytes);
    all_string.extend_from_slice(&secret_bytes);
    all_string.extend_from_slice(&b_bytes);

    let mut h = Sha256::new();
    h.update(&all_string);
    let mut all_string_commitment = h.finalize().to_vec();

    secret_commitment[31] &= 0x1f;
    all_string_commitment[31] &= 0x1f;

    let circuit = SecretStringCircuit {
        a_bytes: Some(a_bytes.clone()),
        b_bytes: Some(b_bytes.clone()),
        secret_bytes: Some(secret_bytes),
        secret_commitment: Some(secret_commitment.clone()),
        all_string_commitment: Some(all_string_commitment.clone()),
    };

    let public_input = vec![a_bytes, b_bytes, secret_commitment, all_string_commitment];
    let pub_input = public_input
        .iter()
        .map(|bytes| Fr::read(&bytes[..]).expect("pack hash as field element"))
        .collect::<Vec<_>>();

    (circuit, pub_input)
}

pub fn _transform_public_input(input: Vec<Vec<u8>>) -> Vec<Fr> {
    input
        .iter()
        .flatten()
        .map(|byte| {
            let mut v = Vec::with_capacity(8);
            (0..8)
                .rev()
                .for_each(|i| v.push(Fr::from((byte >> i) & 1u8 == 1u8)));
            v
        })
        .flatten()
        .collect()
}
