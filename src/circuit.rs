use crate::circuit_extend::{CircuitByte, CircuitString};
use crate::circuit_extend::{CircuitNum, ExtendFunction};
use crate::params::{
    LENGTH_REPR_BIT_WIDTH, MAX_HASH_PREIMAGE_BIT_WIDTH, MAX_HASH_PREIMAGE_LENGTH,
    MAX_PREFIX_LENGTH, MAX_SECRET_LENGTH, MAX_SUFFIX_LENGTH, MIN_HASH_PREIMAGE_LENGTH,
    MIN_PREFIX_LENGTH, MIN_SECRET_LENGTH, MIN_SUFFIX_LENGTH,
};
use crate::utils::pack_bits_to_element;
use ark_ff::{FpParameters, PrimeField};
use ckb_gadgets::algebra::fr::AllocatedFr;
use ckb_gadgets::hashes::sha256::sha256;
use ckb_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

#[derive(Clone, Debug)]
pub struct SecretStringCircuit<F: PrimeField> {
    pub prefix_padding: Option<Vec<F>>,
    pub prefix_length: Option<F>,
    pub secret_padding: Option<Vec<F>>,
    pub secret_length: Option<F>,
    pub suffix_padding: Option<Vec<F>>,
    pub suffix_length: Option<F>, // need assert!

    pub secret: Option<Vec<F>>,
    pub message: Option<Vec<F>>,

    pub secret_hash: Option<F>,
    pub message_hash: Option<F>,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for SecretStringCircuit<F> {
    fn generate_constraints<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        // convert witness to circuit variables
        let secret_commitment = AllocatedFr::alloc(cs.ns(|| "secret commitment"), || {
            self.secret_hash.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let message_commitment = AllocatedFr::alloc(cs.ns(|| "signed message commitment"), || {
            self.message_hash.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let secret = CircuitString::from_string_witness_with_fixed_length(
            cs.ns(|| "convert secret string witness to CircuitString"),
            &self
                .secret_padding
                .ok_or(SynthesisError::AssignmentMissing)?,
            MAX_SECRET_LENGTH,
        )?;
        let prefix = CircuitString::from_string_witness_with_fixed_length(
            cs.ns(|| "convert prefix string witness to CircuitString"),
            &self
                .prefix_padding
                .ok_or(SynthesisError::AssignmentMissing)?,
            MAX_PREFIX_LENGTH,
        )?;
        let suffix = CircuitString::from_string_witness_with_fixed_length(
            cs.ns(|| "convert suffix string witness to CircuitString"),
            &self
                .suffix_padding
                .ok_or(SynthesisError::AssignmentMissing)?,
            MAX_SUFFIX_LENGTH,
        )?;

        // get secret hash preimage
        let secret_bits = secret.get_bits_le();
        let mut signed_message_bytes = calculate_correct_preimage(
            cs.ns(|| "calculate correct preimage"),
            &prefix,
            &secret,
            &suffix,
        )?;
        // get message hash preimage
        let mut signed_message_bits = Vec::with_capacity(MAX_HASH_PREIMAGE_BIT_WIDTH);
        for (i, byte) in signed_message_bytes.iter_mut().enumerate() {
            let bits = byte.generate_bits_le(cs.ns(|| format!("byte{}:generate bits le", i)))?;
            signed_message_bits.extend_from_slice(bits);
        }

        // calculate secret hash
        let mut secret_commitment_bits =
            sha256(cs.ns(|| "calculate secret string hash"), &secret_bits)?;
        secret_commitment_bits.reverse();
        secret_commitment_bits.truncate(F::Params::CAPACITY as usize);

        // calculate message hash
        let mut message_commitment_bits =
            sha256(cs.ns(|| "calc signed message hash"), &signed_message_bits)?;
        message_commitment_bits.reverse();
        message_commitment_bits.truncate(F::Params::CAPACITY as usize);

        // Check whether the secret hash is correctly calculated
        let final_secret_hash =
            pack_bits_to_element(cs.ns(|| "final secret hash"), &secret_commitment_bits)?;
        cs.enforce(
            || "enforce external secret hash equality",
            |lc| lc + secret_commitment.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + final_secret_hash.get_variable(),
        );

        // Check whether the signed message hash is correctly calculated
        let final_message_hash =
            pack_bits_to_element(cs.ns(|| "final message hash"), &message_commitment_bits)?;
        cs.enforce(
            || "enforce external message hash equality",
            |lc| lc + message_commitment.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + final_message_hash.get_variable(),
        );

        // enforce public input inputize
        prefix.inputize(cs.ns(|| "inputize prefix"))?;
        suffix.inputize(cs.ns(|| "inputize prefix"))?;
        secret_commitment.inputize(cs.ns(|| "inputize pub_data"))?;
        message_commitment.inputize(cs.ns(|| "inputize signature message hash"))?;
        Ok(())
    }
}

fn calculate_correct_preimage<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &CircuitString<F>,
    b: &CircuitString<F>,
    c: &CircuitString<F>,
) -> Result<Vec<CircuitByte<F>>, SynthesisError> {
    let a_length = a.get_length();
    let b_length = b.get_length();

    let a_add_b_length = a_length
        .get_num()
        .add(cs.ns(|| "a_len + b_len"), b_length.get_num())?;
    let a_add_b_length_cn = CircuitNum::from_fr_with_known_length(
        cs.ns(|| "a + b_length as CircuitNum"),
        a_add_b_length,
        LENGTH_REPR_BIT_WIDTH,
    )?;
    let mut selecting_string = Vec::with_capacity(MAX_HASH_PREIMAGE_LENGTH);

    // first section
    for i in 0..MIN_PREFIX_LENGTH {
        selecting_string.push(a[i].clone());
    }

    // second section
    for i in MIN_PREFIX_LENGTH..MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH {
        let nth = CircuitNum::from_fe_with_known_length(
            cs.ns(|| format!("Second section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
        let index_b = nth.get_num().sub(
            cs.ns(|| format!("Second section:calculate index_a:{} - a_len", i)),
            a_length.get_num(),
        )?;
        let searched_a_char = search_char(
            cs.ns(|| format!("Second section:search a {}th char", i)),
            a,
            nth.get_num(),
            MIN_PREFIX_LENGTH..MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH,
        )?;
        let searched_b_char = search_char(
            cs.ns(|| format!("Second section:search b {}th char", i)),
            b,
            &index_b,
            0..MIN_SECRET_LENGTH,
        )?;
        let select_char = CircuitByte::select_ifle_with_unchecked(
            cs.ns(|| {
                format!(
                    "Second section:{}th bit is the second section corresponding range",
                    i
                )
            }),
            &searched_a_char,
            &searched_b_char,
            &nth,
            a_length,
        )?;
        selecting_string.push(select_char);
    }

    // third section
    for i in MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH..MAX_PREFIX_LENGTH {
        let nth = CircuitNum::from_fe_with_known_length(
            cs.ns(|| format!("Third section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
        let index_b = nth.get_num().sub(
            cs.ns(|| format!("Third section:calculate index_b={} - a_len", i)),
            a_length.get_num(),
        )?;
        let index_c = nth.get_num().sub(
            cs.ns(|| format!("Third section:calculate index_c={} - a_len - b_len", i)),
            a_add_b_length_cn.get_num(),
        )?;
        let searched_a_char = search_char(
            cs.ns(|| format!("Third section:search a {}th char", i)),
            a,
            nth.get_num(),
            MIN_PREFIX_LENGTH..MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH,
        )?;
        let searched_b_char = search_char(
            cs.ns(|| format!("Third section:search b {}th char", i)),
            b,
            &index_b,
            MIN_PREFIX_LENGTH..MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH,
        )?;
        let searched_c_char = search_char(
            cs.ns(|| format!("Third section:search c {}th char", i)),
            c,
            &index_c,
            MIN_PREFIX_LENGTH..MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH,
        )?;

        let selected_char = {
            let selected_char = CircuitByte::select_ifle_with_unchecked(
                cs.ns(|| {
                    format!(
                        "Third section:{}th bit is the third section i < a_length",
                        i
                    )
                }),
                &searched_a_char,
                &searched_b_char,
                &nth,
                a_length,
            )?;
            CircuitByte::select_ifle_with_unchecked(
                cs.ns(|| {
                    format!(
                        "Third section:{}th bit is the third section i < a_add_b_length",
                        i
                    )
                }),
                &selected_char,
                &searched_c_char,
                &nth,
                &a_add_b_length_cn,
            )?
        };
        selecting_string.push(selected_char);
    }

    // fourth section
    for i in MAX_PREFIX_LENGTH..MAX_PREFIX_LENGTH + MAX_SECRET_LENGTH {
        let nth = CircuitNum::from_fe_with_known_length(
            cs.ns(|| format!("Fourth section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
        let index_b = nth.get_num().sub(
            cs.ns(|| format!("Fourth section:calculate index_b:{} - a_len", i)),
            a_length.get_num(),
        )?;
        let index_c = nth.get_num().sub(
            cs.ns(|| format!("Fourth section:calculate index_c:{} - a_len - b_len", i)),
            a_add_b_length_cn.get_num(),
        )?;
        let searched_b_char = search_char(
            cs.ns(|| format!("Fourth section:search b {}th char", i)),
            b,
            &index_b,
            0..MAX_SECRET_LENGTH,
        )?;
        let searched_c_char = search_char(
            cs.ns(|| format!("Fourth section:search c {}th char", i)),
            c,
            &index_c,
            0..MAX_PREFIX_LENGTH + MAX_SECRET_LENGTH - MIN_PREFIX_LENGTH - MIN_SECRET_LENGTH,
        )?;
        let select_char = CircuitByte::select_ifle_with_unchecked(
            cs.ns(|| {
                format!(
                    "Fourth section:{}th bit is the fourth section corresponding range",
                    i
                )
            }),
            &searched_b_char,
            &searched_c_char,
            &nth,
            &a_add_b_length_cn,
        )?;
        selecting_string.push(select_char);
    }

    // fifth section
    for i in MAX_PREFIX_LENGTH + MAX_SECRET_LENGTH..MIN_HASH_PREIMAGE_LENGTH {
        let nth = CircuitNum::from_fe_with_known_length(
            cs.ns(|| format!("Fifth section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
        let index_c = nth.get_num().sub(
            cs.ns(|| format!("Fifth section:calculate index_c:{} - a_len - b_len", i)),
            a_add_b_length_cn.get_num(),
        )?;
        let search_c_char = search_char(
            cs.ns(|| {
                format!(
                    "Fifth section:{}th bit is the fifth section corresponding range",
                    i
                )
            }),
            c,
            &index_c,
            0..MIN_SUFFIX_LENGTH,
        )?;
        selecting_string.push(search_c_char);
    }

    // seventh section
    for i in MIN_HASH_PREIMAGE_LENGTH..MAX_HASH_PREIMAGE_LENGTH {
        let nth = CircuitNum::from_fe_with_known_length(
            cs.ns(|| format!("Seventh section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
        let index_c = nth.get_num().sub(
            cs.ns(|| format!("Seventh section:calculate index_c:{} - a_len - b_len", i)),
            a_add_b_length_cn.get_num(),
        )?;
        let search_c_char = search_char(
            cs.ns(|| {
                format!(
                    "Seventh section:{}th bit is the seventh section corresponding range",
                    i
                )
            }),
            c,
            &index_c,
            MIN_HASH_PREIMAGE_LENGTH - MAX_PREFIX_LENGTH - MAX_SECRET_LENGTH..MAX_SUFFIX_LENGTH,
        )?;
        selecting_string.push(search_c_char);
    }

    Ok(selecting_string)
}

fn search_char<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    string: &CircuitString<F>,
    index: &AllocatedFr<F>,
    range: ark_std::ops::Range<usize>,
) -> Result<CircuitByte<F>, SynthesisError> {
    let mut selected_byte = AllocatedFr::constant(cs.ns(|| "init selected_byte"), F::zero())?;
    for i in range {
        let nth = AllocatedFr::constant(cs.ns(|| format!("{}th index", i)), F::from(i as u128))?;
        selected_byte = AllocatedFr::select_ifeq(
            cs.ns(|| format!("select {}th byte ", i)),
            string[i].get_num(),
            &selected_byte,
            &nth,
            index,
        )?;
    }
    Ok(CircuitByte::from_fr_with_unchecked(selected_byte))
}

#[test]
fn test_secret_circuit() {
    use crate::test::TestConstraintSystem;
    use ark_bn254::Fr;

    let mut cs = TestConstraintSystem::<Fr>::new();

    let secret = "secret";
    println!("{}", secret.len());
    let mut message = "prefix_secret_suffix".to_string();
    let padding = "a".repeat(crate::params::MIN_HASH_PREIMAGE_LENGTH);
    message.push_str(&*padding);
    println!("{}", message.len());
    let (c, public_input) = crate::generate_circuit_instance(secret.to_string(), message);
    c.generate_constraints(&mut cs).unwrap();

    println!("num_constraints: {}", cs.num_constraints());
    println!("unconstrained: {}", cs.find_unconstrained());
    assert!(cs.is_satisfied());
    if let Some(err) = cs.which_is_unsatisfied() {
        println!("error: {}", err);
    }
}
