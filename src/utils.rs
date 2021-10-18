use crate::circuit::SecretStringCircuit;
use crate::params::{
    MAX_HASH_PREIMAGE_LENGTH, MAX_SECRET_LENGTH, MIN_HASH_PREIMAGE_LENGTH, MIN_SECRET_LENGTH,
};
use crate::witness::SecretWitness;
use ark_bn254::fr::Fr;
use ark_ff::{FpParameters, PrimeField};
use ckb_gadgets::algebra::boolean::Boolean;
use ckb_gadgets::algebra::fr::AllocatedFr;
use ckb_r1cs::{ConstraintSystem, LinearCombination, SynthesisError};

pub fn generate_circuit_instance<F: PrimeField>(
    secret: String,
    message: String,
) -> (SecretStringCircuit<F>, Vec<F>) {
    assert!(MIN_SECRET_LENGTH <= secret.len() && secret.len() <= MAX_SECRET_LENGTH);
    assert!(MIN_HASH_PREIMAGE_LENGTH <= message.len() && message.len() <= MAX_HASH_PREIMAGE_LENGTH);

    let secret_witness = SecretWitness::<F>::generate_witness(secret, message);

    let public_input = secret_witness.get_public_input();
    let circuit = secret_witness.into_circuit_instance();

    (circuit, public_input)
}

pub fn transform_public_input(input: Vec<Vec<u8>>) -> Vec<Fr> {
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

pub fn pack_bits_to_element<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    bits: &[Boolean],
) -> Result<AllocatedFr<F>, SynthesisError> {
    // bits.chunks_mut(8).for_each(|bit| bit.reverse());
    // bits.truncate(F::Params::CAPACITY as usize);
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

    // bits.resize(256, Boolean::Constant(false));
    // bits.chunks_mut(8).for_each(|bit| bit.reverse());
    Ok(data_packed)
}

pub fn calculate_ascii_char<F: PrimeField, CS: ConstraintSystem<F>>(
    length: &mut AllocatedFr<F>,
    mut cs: CS,
    char_bits: &[Boolean],
) -> Result<(), SynthesisError> {
    assert_eq!(char_bits.len() % 8, 0);
    let mut result_boolean = Boolean::constant(false);
    for (i, bit) in char_bits.iter().enumerate() {
        result_boolean = Boolean::and(
            cs.ns(|| format!("computes Boolean{} operation iteratively", i)),
            &bit.not(),
            &result_boolean.not(),
        )?
        .not();
    }
    let temp = AllocatedFr::alloc(cs.ns(|| "temp variable"), || {
        let mut tmp = length
            .get_value()
            .ok_or(SynthesisError::AssignmentMissing)?;
        tmp.add_assign(&if result_boolean
            .get_value()
            .ok_or(SynthesisError::AssignmentMissing)?
        {
            F::one()
        } else {
            F::zero()
        });

        Ok(tmp)
    })?;

    cs.enforce(
        || "update length",
        |lc| lc + length.get_variable() + result_boolean.lc(CS::one(), F::one()),
        |lc| lc + CS::one(),
        |lc| lc + temp.get_variable(),
    );
    *length = temp;
    Ok(())
}
