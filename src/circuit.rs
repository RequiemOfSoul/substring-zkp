use crate::circuit_extend::CircuitString;
use crate::params::{
    LENGTH_REPR_BIT_WIDTH, MAX_HASH_PREIMAGE_BIT_WIDTH, MIN_PREFIX_BIT_WIDTH, MIN_SECRET_BIT_WIDTH,
    PREFIX_BIT_WIDTH, SECRET_BIT_WIDTH, SUFFIX_BIT_WIDTH,
};
use crate::utils::pack_bits_to_element;
use ark_ff::PrimeField;
use ckb_gadgets::algebra::boolean::Boolean;
use ckb_gadgets::algebra::fr::AllocatedFr;
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
            let (out_bits, _) =
                pack_bits_to_element(cs.ns(|| "packed secret_commitment"), out_bits)?;
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
            let (out_bits, _) =
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

fn calculate_string_length<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    string_bits: &[Boolean],
) -> Result<CircuitString<F>, SynthesisError> {
    let mut length = AllocatedFr::alloc(cs.ns(|| "initialized zero"), || Ok(F::one()))?;
    let mut init_boolean = Boolean::constant(true);
    for (i, char_bits) in string_bits.chunks(8).enumerate() {
        for (j, bit) in char_bits.iter().enumerate() {
            init_boolean = Boolean::and(
                cs.ns(|| format!("calculate char{} iteration boolean{} operation", i, j)),
                &bit.not(),
                &init_boolean.not(),
            )?
            .not();
        }
        let temp = AllocatedFr::alloc(cs.ns(|| format!("temp variable{}", i)), || {
            let mut tmp = length
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            tmp.add_assign(&if init_boolean
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
            || format!("update {}th", i),
            |lc| lc + length.get_variable() + init_boolean.lc(CS::one(), F::one()),
            |lc| lc + CS::one(),
            |lc| lc + temp.get_variable(),
        );
        length = temp;
    }
    // TODO: mul 8
    CircuitString::from_num_with_known_length(
        cs.ns(|| "generate CircuitString length"),
        length,
        LENGTH_REPR_BIT_WIDTH,
    )
}

fn select_chars<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &[Boolean],
    b: &[Boolean],
    c: &[Boolean],
) -> Result<Vec<Boolean>, SynthesisError> {
    let a_length = calculate_string_length(cs.ns(|| "a length"), a)?;
    let _b_length = calculate_string_length(cs.ns(|| "b length"), b)?;
    let _c_length = calculate_string_length(cs.ns(|| "c length"), c)?;

    let mut selected_bits = Vec::with_capacity(MAX_HASH_PREIMAGE_BIT_WIDTH);
    // first section
    for i in 0..MIN_PREFIX_BIT_WIDTH {
        selected_bits.push(a[i].clone());
    }

    // second section
    for i in MIN_PREFIX_BIT_WIDTH..MIN_PREFIX_BIT_WIDTH + MIN_SECRET_BIT_WIDTH {
        let nth = CircuitString::from_fe_with_known_length(
            cs.ns(|| format!("Second section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
        let _is_the_corresponding_range = CircuitString::less_than_fixed(
            cs.ns(|| format!("{}th bit is the second section corresponding range", i)),
            &nth,
            &a_length,
        )?;
    }

    // third section
    for i in MIN_PREFIX_BIT_WIDTH + MIN_SECRET_BIT_WIDTH..PREFIX_BIT_WIDTH {
        let _nth = CircuitString::from_fe_with_known_length(
            cs.ns(|| format!("Third section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
    }

    // fourth section
    for i in PREFIX_BIT_WIDTH..PREFIX_BIT_WIDTH + SECRET_BIT_WIDTH {
        let _nth = CircuitString::from_fe_with_known_length(
            cs.ns(|| format!("Fourth section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
    }

    // fifth section
    for i in PREFIX_BIT_WIDTH + SECRET_BIT_WIDTH..SECRET_BIT_WIDTH + SUFFIX_BIT_WIDTH {
        let _nth = CircuitString::from_fe_with_known_length(
            cs.ns(|| format!("Fifth section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
    }
    Ok(selected_bits)
}
