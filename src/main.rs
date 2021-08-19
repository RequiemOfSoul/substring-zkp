use ark_serialize::*;
use ark_ff::{Field, test_rng, PrimeField};
use ark_bls12_381::{Bls12_381 as E, Fr};
use ckb_gadgets::algebra::{
    boolean::Boolean, uint32::UInt32, fr::AllocatedFr
};
use ckb_r1cs::{
    ConstraintSynthesizer, ConstraintSystem, Namespace, SynthesisError
};
use ckb_gadgets::hashes::sha256::{
    self, AbstractHashSha256Output, AbstractHashSha256
};
use ckb_gadgets::hashes::abstract_hash::AbstractHash;
use ckb_groth16::{
    create_random_proof, generate_random_parameters, verifier::prepare_verifying_key, verify_proof,
    Proof, VerifyKey,
};
use std::time::Instant;
use std::convert::TryInto;


#[derive(Clone, Debug)]
struct StringSecret {
    a_bytes: Option<Vec<u8>>,
    b_bytes: Option<Vec<u8>>,
    secret_bytes: Option<Vec<u8>>,

    secret_commitment: Option<Vec<u8>>,
    all_string_commitment: Option<Vec<u8>>,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for StringSecret {
    fn generate_constraints<CS:ConstraintSystem<F>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let secret_var = AbstractHashSha256Output::alloc(
            cs.ns(||"secret"),
            self.secret_bytes.unwrap(),
        )?;
        let a_var = AbstractHashSha256Output::alloc_input(
            cs.ns(||"a"),
            self.a_bytes.unwrap(),
        )?;
        let b_var = AbstractHashSha256Output::alloc_input(
            cs.ns(||"b"),
            self.b_bytes.unwrap(),
        )?;

        let secret_commitment_out = AbstractHashSha256::hash_enforce(
            cs.ns(||"secret commitment out"),
            &[&secret_var]
        )?;
        let all_string_commitment_out = AbstractHashSha256::hash_enforce(
            cs.ns(||"all string commitment out"),
            &[&a_var, &secret_var, &b_var]
        )?;


        let secret_commitment = AbstractHashSha256Output::alloc_input(
            cs.ns(||"secret commitment"),
            self.secret_commitment.unwrap().to_vec(),
        )?;
        let all_string_commitment = AbstractHashSha256Output::alloc_input(
            cs.ns(||"all string commitment"),
            self.all_string_commitment.unwrap().to_vec(),
        )?;

        if let Some(hash_bits) = all_string_commitment.get_value(){
            for (i, (circuit_in, hash_out)) in hash_bits.iter()
                            .zip(all_string_commitment_out.get_value().unwrap().iter()).enumerate(){
                Boolean::enforce_equal(
                    cs.ns(||format!("all string:{}",i)),
                    circuit_in, hash_out
                )?
            }
        }
        if let Some(hash_bits) = secret_commitment.get_value(){
            for (i, (circuit_in, hash_out)) in hash_bits.iter()
                            .zip(secret_commitment_out.get_value().unwrap().iter()).enumerate(){
                Boolean::enforce_equal(
                    cs.ns(||format!("secret string:{}",i)),
                    circuit_in, hash_out
                )?
            }
        }
        Ok(())
    }
}

fn generate_circuit_instance(a:String, b:String, secret:String, string_length:usize) -> (StringSecret, Vec<u8>, Vec<u8> , Vec<u8>, Vec<u8> ) {
    assert!(a.len() <= string_length && a.len() <= string_length && a.len() <= string_length);
    use sha2::{Digest, Sha256};
    
    let mut a_bytes = a.into_bytes();
    a_bytes.resize(string_length, 0);
    let mut b_bytes = b.into_bytes();
    b_bytes.resize(string_length, 0);
    let mut secret_bytes = secret.into_bytes();
    secret_bytes.resize(string_length, 0);

    let mut h = Sha256::new();
    h.update(&secret_bytes);
    let secret_commitment = h.finalize().to_vec();

    let mut all_string = Vec::with_capacity(a_bytes.len() + b_bytes.len() + secret_bytes.len());
    all_string.extend_from_slice(&a_bytes);
    all_string.extend_from_slice(&secret_bytes);
    all_string.extend_from_slice(&b_bytes);

    let mut h = Sha256::new();
    h.update(&all_string);
    let all_string_commitment = h.finalize().to_vec();

    let circuit = StringSecret {
        a_bytes: Some(a_bytes.clone()),
        b_bytes: Some(b_bytes.clone()),
        secret_bytes: Some(secret_bytes),
        secret_commitment: Some(secret_commitment.clone()),
        all_string_commitment: Some(all_string_commitment.clone())
    };
    (circuit, a_bytes, b_bytes, secret_commitment, all_string_commitment)
}

fn transform_public_input(input:Vec<Vec<u8>>) -> Vec<Fr>{
    input.iter().flatten().map(|byte| {
        let mut v = Vec::with_capacity(8);
        (0..8).rev().for_each(|i| v.push(Fr::from((byte >> i) & 1u8 == 1u8)));
        v
    }).flatten().collect()
}

fn main() {
    let rng = &mut test_rng();

    let a = "a".to_string();
    let b = "b".to_string();
    let secret = "secret".to_string();
    let (c, a, b, secret_commitment, all_string_commitment) =
            generate_circuit_instance(a.clone(), b.clone(), secret.clone(), 32);

    let s_start = Instant::now();
    let params = generate_random_parameters::<E, _, _>(c.clone(), rng).unwrap();
    let s_time = s_start.elapsed();
    println!("[Groth16] Setup : {:?}", s_time);

    let mut vk_bytes = Vec::new();
    params.vk.serialize(&mut vk_bytes).unwrap();
    println!("[Groth16] VerifyKey length : {}", vk_bytes.len());

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);
    println!("pvk:{}",pvk.gamma_abc_g1.len());

    let p_start = Instant::now();
    let proof = create_random_proof(&params, c, rng).unwrap();
    let p_time = p_start.elapsed();
    println!("[Groth16] Prove : {:?}", p_time);

    let mut proof_bytes = vec![];
    proof.serialize(&mut proof_bytes).unwrap();
    println!("[Groth16] Proof : {}", proof_bytes.len());

    let v_start = Instant::now();
    let public_input = vec![a, b, secret_commitment, all_string_commitment];
    assert!(verify_proof(
        &pvk,
        &proof,
        &transform_public_input(public_input.clone())
    ).unwrap());
    let v_time = v_start.elapsed();
    println!("[Groth16] Verify : {:?}", v_time);

    let vk2 = VerifyKey::<E>::deserialize(&vk_bytes[..]).unwrap();
    let proof2 = Proof::<E>::deserialize(&proof_bytes[..]).unwrap();
    let pvk2 = prepare_verifying_key(&vk2);
    assert!(verify_proof(
        &pvk2,
        &proof2,
        &transform_public_input(public_input)
    ).unwrap());
}
