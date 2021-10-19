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
        assert_eq!(
            self.secret_length.unwrap(),
            secret.get_length().get_value().unwrap(),
            "secret_length calculate wrong."
        );
        let prefix = CircuitString::from_string_witness_with_fixed_length(
            cs.ns(|| "convert prefix string witness to CircuitString"),
            &self
                .prefix_padding
                .ok_or(SynthesisError::AssignmentMissing)?,
            MAX_PREFIX_LENGTH,
        )?;
        assert_eq!(
            self.prefix_length,
            prefix.get_length().get_value(),
            "prefix_length calculate wrong."
        );
        let suffix = CircuitString::from_string_witness_with_fixed_length(
            cs.ns(|| "convert suffix string witness to CircuitString"),
            &self
                .suffix_padding
                .ok_or(SynthesisError::AssignmentMissing)?,
            MAX_SUFFIX_LENGTH,
        )?;
        assert_eq!(
            self.suffix_length.unwrap(),
            suffix.get_length().get_value().unwrap(),
            "suffix_length calculate wrong."
        );

        // get secret hash preimage
        let mut secret_bits = secret.get_bits_be();
        println!("bytes len:{}", secret.get_bytes().len());
        println!("secret_bits:{}", secret_bits.len());
        secret_bits.chunks(8).for_each(|bit| {
            bit.iter()
                .for_each(|bit| print!("{}", bit.get_value().unwrap() as u8));
            print!(" ")
        });

        let mut signed_message_bytes = calculate_correct_preimage(
            cs.ns(|| "calculate correct preimage"),
            &prefix,
            &secret,
            &suffix,
        )?;
        println!("\n{}", self.message.as_ref().unwrap().len());
        signed_message_bytes
            .iter()
            .zip(self.message.as_ref().unwrap().iter())
            .enumerate()
            .for_each(|(i, (byte, byte1))| {
                println!("{}th:{} {}", i, byte.get_num().get_value().unwrap(), *byte1)
            });
        // get message hash preimage
        let mut signed_message_bits = Vec::with_capacity(MAX_HASH_PREIMAGE_BIT_WIDTH);
        for (i, byte) in signed_message_bytes.iter_mut().enumerate() {
            let bits = byte.generate_bits_be(cs.ns(|| format!("byte{}:generate bits be", i)))?;
            signed_message_bits.extend(bits);
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
        suffix.inputize(cs.ns(|| "inputize suffix"))?;
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
        println!(
            "second{} searched_a_char:{}",
            i,
            searched_a_char.get_num().get_value().unwrap()
        );
        let searched_b_char = search_char(
            cs.ns(|| format!("Second section:search b {}th char", i)),
            b,
            &index_b,
            0..MIN_SECRET_LENGTH,
        )?;
        println!(
            "second{} searched_b_char:{}",
            i,
            searched_b_char.get_num().get_value().unwrap()
        );
        let selected_char = CircuitByte::select_ifle_with_unchecked(
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
        println!(
            "second{} select char:{}",
            i,
            selected_char.get_num().get_value().unwrap()
        );
        selecting_string.push(selected_char);
    }

    // third section
    assert!(MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH <= MAX_PREFIX_LENGTH);
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
            MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH..MAX_PREFIX_LENGTH,
        )?;
        println!(
            "third{} searched_a_char:{}",
            i,
            searched_a_char.get_num().get_value().unwrap()
        );
        let searched_b_char = search_char(
            cs.ns(|| format!("Third section:search b {}th char", i)),
            b,
            &index_b,
            0..MAX_PREFIX_LENGTH - MIN_PREFIX_LENGTH,
        )?;
        println!(
            "third{} searched_b_char:{}",
            i,
            searched_b_char.get_num().get_value().unwrap()
        );
        let searched_c_char = search_char(
            cs.ns(|| format!("Third section:search c {}th char", i)),
            c,
            &index_c,
            0..MAX_PREFIX_LENGTH - MIN_SECRET_LENGTH - MIN_PREFIX_LENGTH,
        )?;
        println!(
            "third{} searched_c_char:{}",
            i,
            searched_c_char.get_num().get_value().unwrap()
        );

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
        println!(
            "third{} select char:{}",
            i,
            selected_char.get_num().get_value().unwrap()
        );
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
        let selected_char = CircuitByte::select_ifle_with_unchecked(
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
        println!(
            "fourth{} select char:{}",
            i,
            selected_char.get_num().get_value().unwrap()
        );
        selecting_string.push(selected_char);
    }

    // fifth section
    assert!(MAX_PREFIX_LENGTH + MAX_SECRET_LENGTH <= MIN_HASH_PREIMAGE_LENGTH);
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
        let selected_char = search_char(
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
        println!(
            "fifth{} select char:{}",
            i,
            selected_char.get_num().get_value().unwrap()
        );
        selecting_string.push(selected_char);
    }

    // sixth section
    for i in MIN_HASH_PREIMAGE_LENGTH..MAX_HASH_PREIMAGE_LENGTH {
        let nth = CircuitNum::from_fe_with_known_length(
            cs.ns(|| format!("sixth section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
        let index_c = nth.get_num().sub(
            cs.ns(|| format!("sixth section:calculate index_c:{} - a_len - b_len", i)),
            a_add_b_length_cn.get_num(),
        )?;
        let selected_char = search_char(
            cs.ns(|| {
                format!(
                    "sixth section:{}th bit is the sixth section corresponding range",
                    i
                )
            }),
            c,
            &index_c,
            MIN_HASH_PREIMAGE_LENGTH - MAX_PREFIX_LENGTH - MAX_SECRET_LENGTH
                ..MAX_HASH_PREIMAGE_LENGTH,
        )?;
        println!(
            "sixth{} select char:{}",
            i,
            selected_char.get_num().get_value().unwrap()
        );
        selecting_string.push(selected_char);
    }
    println!("{}", selecting_string.len());

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
    use crate::test_constraint_system::TestConstraintSystem;
    use ark_bn254::Fr;

    let mut cs = TestConstraintSystem::<Fr>::new();

    let secret = "secret";
    let mut message = "pre_secret_suffix".to_string();
    let padding = "0".repeat(crate::params::MAX_HASH_PREIMAGE_LENGTH - message.len());
    message.push_str(&*padding);
    println!("message:{:?}", message.as_bytes());
    let (c, _) = crate::generate_circuit_instance(secret.to_string(), message);
    c.generate_constraints(&mut cs).unwrap();

    println!("num_constraints: {}", cs.num_constraints());
    println!("unconstrained: {}", cs.find_unconstrained());
    if let Some(err) = cs.which_is_unsatisfied() {
        println!("error: {}", err);
    }
}
