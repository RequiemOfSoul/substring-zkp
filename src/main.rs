use ark_serialize::*;
use ark_std::test_rng;
use std::time::Instant;

// use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_bn254::Bn254 as E;
use ckb_groth16::{
    create_random_proof, generate_random_parameters, verifier::prepare_verifying_key, verify_proof,
};
use substring_zkp::circuit::SecretStringCircuit;
use substring_zkp::{params, utils::generate_circuit_instance};

fn main() {
    let rng = &mut test_rng();

    let c = SecretStringCircuit::default();
    let s_start = Instant::now();
    let params = generate_random_parameters::<E, _, _>(c, rng).unwrap();
    let s_time = s_start.elapsed();
    println!("[Groth16] Setup : {:?}", s_time);

    let mut vk_bytes = Vec::new();
    params.vk.serialize(&mut vk_bytes).unwrap();
    println!("[Groth16] VerifyKey length : {}", vk_bytes.len());

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);
    println!("pvk:{}", pvk.gamma_abc_g1.len());

    // generate circuit instance
    let padding = "0"; // must be single char, or else fill it to MAX_HASH_PREIMAGE_LENGTH
    let secret = "christian.schneider@androidloves.me";
    let mut padding_message = "from:Christian Schneider Christian Schneider Christian Schneider <christian.schneider@androidloves.me>\r\nsubject:this is a test mail\r\ndate:Sat, 14 Mar 2020 21:48:57 +0100\r\nmessage-id:<4c2828df-2dae-74ff-2fa7-e6ac36100341@androidloves.me>\r\nto:mail@kmille.wtf\r\ncontent-type:text/plain; charset=utf-8; format=flowed\r\ncontent-transfer-encoding:7bit\r\ndkim-signature:v=1; a=rsa-sha256; c=relaxed/relaxed; d=androidloves.me; s=2019022801; t=1584218937; h=from:from:reply-to:subject:subject:date:date:message-id:message-id: to:to:cc:content-type:content-type: content-transfer-encoding:content-transfer-encoding; bh=aeLbTnlUQQv2UFEWKHeiL5Q0NjOwj4ktNSInk8rN/P0=; b=".to_string();
    padding_message
        .push_str(&*padding.repeat(params::MAX_HASH_PREIMAGE_LENGTH - padding_message.len()));
    let (c, public_input) = generate_circuit_instance(secret.to_string(), padding_message, None);

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
