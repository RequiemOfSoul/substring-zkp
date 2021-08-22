use crate::utils::pack_bits_to_element;
// use crate::witness::CircuitString;
use ark_ff::PrimeField;
use ckb_gadgets::algebra::boolean::Boolean;
use ckb_gadgets::hashes::abstract_hash::AbstractHash;
use ckb_gadgets::hashes::sha256::{AbstractHashSha256, AbstractHashSha256Output};
use ckb_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

#[derive(Clone, Debug)]
pub struct SecretStringCircuit {
    pub a_bytes: Option<Vec<u8>>,
    pub b_bytes: Option<Vec<u8>>,
    pub secret_bytes: Option<Vec<u8>>,

    pub secret_commitment: Option<Vec<u8>>,
    pub all_string_commitment: Option<Vec<u8>>,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for SecretStringCircuit {
    fn generate_constraints<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let secret_var =
            AbstractHashSha256Output::alloc(cs.ns(|| "secret"), self.secret_bytes.unwrap())?;
        let a_var = AbstractHashSha256Output::alloc(cs.ns(|| "a"), self.a_bytes.unwrap())?;
        pack_bits_to_element(cs.ns(|| "packed a"), a_var.get_value().unwrap())?;
        let b_var = AbstractHashSha256Output::alloc(cs.ns(|| "b"), self.b_bytes.unwrap())?;
        pack_bits_to_element(cs.ns(|| "packed b"), b_var.get_value().unwrap())?;

        let secret_commitment = AbstractHashSha256Output::alloc(
            cs.ns(|| "secret commitment"),
            self.secret_commitment.unwrap(),
        )?;
        let all_string_commitment = AbstractHashSha256Output::alloc(
            cs.ns(|| "all string commitment"),
            self.all_string_commitment.unwrap(),
        )?;

        let secret_commitment_out =
            AbstractHashSha256::hash_enforce(cs.ns(|| "secret commitment out"), &[&secret_var])?;
        let all_string_commitment_out = AbstractHashSha256::hash_enforce(
            cs.ns(|| "all string commitment out"),
            &[&a_var, &secret_var, &b_var],
        )?;

        if let (Some(hash_bits), Some(out_bits)) = (
            secret_commitment.get_value(),
            secret_commitment_out.get_value(),
        ) {
            let out_bits = pack_bits_to_element(cs.ns(|| "packed secret_commitment"), out_bits)?;
            for (i, (circuit_in, hash_out)) in hash_bits.iter().zip(out_bits.iter()).enumerate() {
                assert_eq!(
                    circuit_in.get_value(),
                    hash_out.get_value(),
                    "secret_commitment:{}",
                    i
                );
                Boolean::enforce_equal(
                    cs.ns(|| format!("secret string:{}", i)),
                    circuit_in,
                    hash_out,
                )?
            }
        }
        if let (Some(hash_bits), Some(out_bits)) = (
            all_string_commitment.get_value(),
            all_string_commitment_out.get_value(),
        ) {
            let out_bits =
                pack_bits_to_element(cs.ns(|| "packed all_string_commitment"), out_bits)?;
            for (i, (circuit_in, hash_out)) in hash_bits.iter().zip(out_bits.iter()).enumerate() {
                assert_eq!(
                    circuit_in.get_value(),
                    hash_out.get_value(),
                    "all_string_commitment:{}",
                    i
                );
                Boolean::enforce_equal(cs.ns(|| format!("all string:{}", i)), circuit_in, hash_out)?
            }
        }
        Ok(())
    }
}
