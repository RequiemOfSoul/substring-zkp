use crate::circuit::SecretStringCircuit;
use crate::circuit_extend::{CircuitByte, CircuitString};
use crate::params::{
    MAX_HASH_PREIMAGE_LENGTH, MAX_PREFIX_LENGTH, MAX_SECRET_LENGTH, MIN_HASH_PREIMAGE_LENGTH,
    MIN_PREFIX_LENGTH, MIN_SECRET_LENGTH, MIN_SUFFIX_LENGTH, PADDING_SUFFIX_LENGTH,
    PREFIX_FR_LENGTH, SECRET_FR_LENGTH, SUFFIX_FR_LENGTH,
};
use crate::witness::{
    append_fr_chunk_fixed_width, calculate_hash, compress_public_input, SecretWitness,
};
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

    let public_input = secret_witness.get_compress_public_input();
    let circuit = secret_witness.into_circuit_instance();

    (circuit, vec![public_input])
}

pub fn calculate_public_input<F: PrimeField>(secret: String, message: String) -> F {
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

    assert!(MIN_PREFIX_LENGTH <= prefix.len() && prefix.len() <= MAX_PREFIX_LENGTH);
    let (_, prefix_padding) = append_fr_chunk_fixed_width::<F>(&prefix, PREFIX_FR_LENGTH);

    assert!(MIN_SECRET_LENGTH <= secret.len() && secret.len() <= MAX_SECRET_LENGTH);
    let (_, secret_padding) = append_fr_chunk_fixed_width::<F>(secret.as_bytes(), SECRET_FR_LENGTH);

    assert!(MIN_SUFFIX_LENGTH <= suffix.len() && suffix.len() <= PADDING_SUFFIX_LENGTH);
    let (_, suffix_padding) = append_fr_chunk_fixed_width::<F>(&prefix, SUFFIX_FR_LENGTH);

    let secret_commitment = calculate_hash(&secret_padding);
    let signature_msg_hash = calculate_hash(message.as_bytes());

    let public_input_hash = compress_public_input(
        &prefix_padding,
        &suffix_padding,
        &secret_commitment,
        &signature_msg_hash,
    );

    F::read(&*public_input_hash).expect("packed public input hash hash error")
}

pub fn check_external_string_consistency<
    'a,
    'b,
    F: PrimeField,
    U: Iterator<Item = &'a CircuitByte<F>>,
    T: Iterator<Item = &'b F>,
>(
    (message, external_message): (U, T),
    (prefix, prefix_length): (&CircuitString<F>, Option<&F>),
    (secret, secret_length): (&CircuitString<F>, Option<&F>),
    (suffix, suffix_length): (&CircuitString<F>, Option<&F>),
) {
    if let (Some(inter_prefix), Some(&prefix_length)) =
        (prefix.get_length().get_value(), prefix_length)
    {
        assert_eq!(
            prefix_length, inter_prefix,
            "Not equal to the external prefix length."
        );
    }
    if let (Some(inter_secret), Some(&secret_length)) =
        (secret.get_length().get_value(), secret_length)
    {
        assert_eq!(
            secret_length, inter_secret,
            "Not equal to the external secret length."
        );
    }
    if let (Some(inter_suffix), Some(&suffix_length)) =
        (suffix.get_length().get_value(), suffix_length)
    {
        assert_eq!(
            suffix_length, inter_suffix,
            "Not equal to the external suffix length."
        );
    }
    message
        .zip(external_message)
        .enumerate()
        .for_each(|(i, (byte1, byte2))| {
            if let Some(byte) = byte1.get_num().get_value() {
                if byte != *byte2 {
                    println!("{}th:{} {}", i, byte, *byte2);
                }
                assert_eq!(byte, *byte2, "char{} is not equals", i);
            }
        });
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

    let data_packed = AllocatedFr::alloc(cs.ns(|| "allocate data packed"), || Ok(value))?;

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
