#[warn(non_snake_case)]
mod circuit;
mod circuit_extend;
mod params;
mod utils;
mod witness;

use ark_serialize::*;
use ark_std::test_rng;
use std::time::Instant;

// use ark_bls12_381::{Bls12_381 as E, Fr};
use crate::utils::generate_circuit_instance;
use ark_bn254::{Bn254 as E, Fr};
use ark_ff::FpParameters;
use ark_ff::PrimeField;
use ckb_groth16::{
    create_random_proof, generate_random_parameters, verifier::prepare_verifying_key, verify_proof,
};

fn main() {
    println!("CAPACITY:{}", <Fr as PrimeField>::Params::CAPACITY);
    println!("MODULUS_BITS:{}", <Fr as PrimeField>::Params::MODULUS_BITS);
    let rng = &mut test_rng();

    let prefix = "a".to_string();
    let suffix = "b".to_string();
    let secret = "secret".to_string();
    let (c, public_input) = generate_circuit_instance(prefix, suffix, secret, 32);

    let s_start = Instant::now();
    let params = generate_random_parameters::<E, _, _>(c.clone(), rng).unwrap();
    let s_time = s_start.elapsed();
    println!("[Groth16] Setup : {:?}", s_time);

    let mut vk_bytes = Vec::new();
    params.vk.serialize(&mut vk_bytes).unwrap();
    println!("[Groth16] VerifyKey length : {}", vk_bytes.len());

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);
    println!("pvk:{}", pvk.gamma_abc_g1.len());

    let p_start = Instant::now();
    let proof = create_random_proof(&params, c, rng).unwrap();
    let p_time = p_start.elapsed();
    println!("[Groth16] Prove : {:?}", p_time);

    let mut proof_bytes = vec![];
    proof.serialize(&mut proof_bytes).unwrap();
    println!("[Groth16] Proof : {}", proof_bytes.len());

    let v_start = Instant::now();
    assert!(verify_proof(&pvk, &proof, &public_input).unwrap());
    println!("[Groth16] Verify : {:?}", v_start.elapsed());
}
