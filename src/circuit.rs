#![allow(clippy::assertions_on_constants)]
use crate::circuit_extend::{CircuitByte, CircuitString};
use crate::circuit_extend::{CircuitNum, ExtendFunction};
use crate::params::{
    LENGTH_REPR_BIT_WIDTH, MAX_HASH_PREIMAGE_BIT_WIDTH, MAX_HASH_PREIMAGE_FR_LENGTH,
    MAX_HASH_PREIMAGE_LENGTH, MAX_PREFIX_LENGTH, MAX_SECRET_LENGTH, MIN_PREFIX_LENGTH,
    MIN_SECRET_LENGTH, MIN_SUFFIX_LENGTH, PADDING_SUFFIX_LENGTH, PREFIX_FR_LENGTH,
    SECRET_FR_LENGTH, SUFFIX_FR_LENGTH,
};
use crate::utils::{check_external_string_consistency, pack_bits_to_element};
use ark_ff::{FpParameters, PrimeField};
use ckb_gadgets::algebra::boolean::{AllocatedBit, Boolean};
use ckb_gadgets::algebra::fr::AllocatedFr;
use ckb_gadgets::hashes::sha256::sha256;
use ckb_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

#[derive(Clone, Debug)]
pub struct SecretStringCircuit<F: PrimeField> {
    pub prefix_padding: Vec<Option<F>>,
    pub prefix_length: Option<F>,
    pub secret_padding: Vec<Option<F>>,
    pub secret_length: Option<F>,
    pub suffix_padding: Vec<Option<F>>,
    pub suffix_length: Option<F>, // need assert!

    pub secret: Vec<Option<F>>,
    pub private_blind_factor: Vec<Option<bool>>,
    pub message: Vec<Option<F>>,

    pub secret_hash: Option<F>,
    pub message_hash: Option<F>,
}

impl<F: PrimeField> Default for SecretStringCircuit<F> {
    fn default() -> Self {
        Self {
            prefix_padding: vec![None; PREFIX_FR_LENGTH],
            prefix_length: None,
            secret_padding: vec![None; SECRET_FR_LENGTH],
            secret_length: None,
            suffix_padding: vec![None; SUFFIX_FR_LENGTH],
            suffix_length: None,
            secret: vec![],
            private_blind_factor: vec![None; F::Params::CAPACITY as usize],
            message: vec![None; MAX_HASH_PREIMAGE_FR_LENGTH],
            secret_hash: None,
            message_hash: None,
        }
    }
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
        let blind_factor_be_bits = self
            .private_blind_factor
            .iter()
            .enumerate()
            .map(|(i, bit)| AllocatedBit::alloc(cs.ns(|| format!("alloc {}th bit", i)), *bit))
            .collect::<Result<Vec<_>, _>>()?;

        let secret = CircuitString::from_string_witness_with_fixed_length(
            cs.ns(|| "convert secret string witness to CircuitString"),
            &self.secret_padding,
            MAX_SECRET_LENGTH,
        )?;
        let prefix = CircuitString::from_string_witness_with_fixed_length(
            cs.ns(|| "convert prefix string witness to CircuitString"),
            &self.prefix_padding,
            MAX_PREFIX_LENGTH,
        )?;
        let suffix = CircuitString::from_string_witness_with_fixed_length(
            cs.ns(|| "convert suffix string witness to CircuitString"),
            &self.suffix_padding,
            PADDING_SUFFIX_LENGTH,
        )?;

        // get secret hash preimage
        let mut secret_bits = secret.get_bits_be();
        secret_bits.push(Boolean::constant(false));
        secret_bits.push(Boolean::constant(false));
        secret_bits.push(Boolean::constant(false));
        secret_bits.extend(blind_factor_be_bits.into_iter().map(Boolean::from));

        let mut signed_message_bytes = calculate_correct_preimage(
            cs.ns(|| "calculate correct preimage"),
            &prefix,
            &secret,
            &suffix,
        )?;
        check_external_string_consistency(
            (signed_message_bytes.iter(), self.message.iter()),
            (&prefix, self.prefix_length.as_ref()),
            (&secret, self.secret_length.as_ref()),
            (&suffix, self.suffix_length.as_ref()),
        );

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

    // second section (range increasing:b: 0-6, fixed range:a)
    for i in MIN_PREFIX_LENGTH..MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH {
        let nth = CircuitNum::from_fixed_fe_with_known_length(
            cs.ns(|| format!("Second section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
        let index_b = nth.get_num().sub(
            cs.ns(|| format!("Second section:calculate index_a:{} - a_len", i)),
            a_length.get_num(),
        )?;
        let searched_b_char = search_char(
            cs.ns(|| format!("Second section:search b {}th char", i)),
            b,
            &index_b,
            0..i - MIN_PREFIX_LENGTH,
        )?;
        let selected_char = CircuitByte::select_ifle_with_unchecked(
            cs.ns(|| {
                format!(
                    "Second section:{}th bit is the second section corresponding range",
                    i
                )
            }),
            &a[i],
            &searched_b_char,
            &nth,
            a_length,
        )?;
        selecting_string.push(selected_char);
    }

    // third section (range increasing:b: 6-64,c:0-6, fixed range:a)
    assert!(MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH <= MIN_PREFIX_LENGTH + MAX_SECRET_LENGTH);
    for i in MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH..MIN_PREFIX_LENGTH + MAX_SECRET_LENGTH {
        let nth = CircuitNum::from_fixed_fe_with_known_length(
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
        let searched_b_char = search_char(
            cs.ns(|| format!("Third section:search b {}th char", i)),
            b,
            &index_b,
            0..i - MIN_PREFIX_LENGTH,
        )?;
        let searched_c_char = search_char(
            cs.ns(|| format!("Third section:search c {}th char", i)),
            c,
            &index_c,
            0..i - MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH,
        )?;

        let selected_char = {
            let selected_char = CircuitByte::select_ifle_with_unchecked(
                cs.ns(|| {
                    format!(
                        "Third section:{}th bit is the third section i < a_length",
                        i
                    )
                }),
                &a[i],
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

    // fourth section (range increasing: c:6-128, fixed range:a, b)
    assert!(
        MIN_PREFIX_LENGTH + MAX_SECRET_LENGTH
            <= MIN_PREFIX_LENGTH + MIN_PREFIX_LENGTH + MIN_SUFFIX_LENGTH
    );
    for i in MIN_PREFIX_LENGTH + MAX_SECRET_LENGTH
        ..MIN_PREFIX_LENGTH + MIN_PREFIX_LENGTH + MIN_SUFFIX_LENGTH
    {
        let nth = CircuitNum::from_fixed_fe_with_known_length(
            cs.ns(|| format!("fourth section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
        let index_b = nth.get_num().sub(
            cs.ns(|| format!("fourth section:calculate index_b={} - a_len", i)),
            a_length.get_num(),
        )?;
        let index_c = nth.get_num().sub(
            cs.ns(|| format!("fourth section:calculate index_c={} - a_len - b_len", i)),
            a_add_b_length_cn.get_num(),
        )?;
        let searched_b_char = search_char(
            cs.ns(|| format!("fourth section:search b {}th char", i)),
            b,
            &index_b,
            0..MAX_SECRET_LENGTH,
        )?;
        let searched_c_char = search_char(
            cs.ns(|| format!("fourth section:search c {}th char", i)),
            c,
            &index_c,
            0..i - MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH,
        )?;

        let selected_char = {
            let selected_char = CircuitByte::select_ifle_with_unchecked(
                cs.ns(|| {
                    format!(
                        "fourth section:{}th bit is the third section i < a_length",
                        i
                    )
                }),
                &a[i],
                &searched_b_char,
                &nth,
                a_length,
            )?;
            CircuitByte::select_ifle_with_unchecked(
                cs.ns(|| {
                    format!(
                        "fourth section:{}th bit is the third section i < a_add_b_length",
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

    // fifth section (range increasing: c:128-245, fixed range:a, b)
    assert!(MIN_PREFIX_LENGTH + MIN_PREFIX_LENGTH + MIN_SUFFIX_LENGTH <= MAX_PREFIX_LENGTH);
    for i in MIN_PREFIX_LENGTH + MIN_PREFIX_LENGTH + MIN_SUFFIX_LENGTH..MAX_PREFIX_LENGTH {
        let nth = CircuitNum::from_fixed_fe_with_known_length(
            cs.ns(|| format!("fifth section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
        let index_b = nth.get_num().sub(
            cs.ns(|| format!("fifth section:calculate index_b:{} - a_len", i)),
            a_length.get_num(),
        )?;
        let index_c = nth.get_num().sub(
            cs.ns(|| format!("fifth section:calculate index_c:{} - a_len - b_len", i)),
            a_add_b_length_cn.get_num(),
        )?;
        let searched_b_char = search_char(
            cs.ns(|| format!("fifth section:search b {}th char", i)),
            b,
            &index_b,
            0..MAX_SECRET_LENGTH,
        )?;
        let searched_c_char = search_char(
            cs.ns(|| format!("fifth section:search c {}th char", i)),
            c,
            &index_c,
            0..i - MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH,
        )?;
        let selected_char = {
            let selected_char = CircuitByte::select_ifle_with_unchecked(
                cs.ns(|| {
                    format!(
                        "fifth section:{}th bit is the fifth section i < a_length",
                        i
                    )
                }),
                &a[i],
                &searched_b_char,
                &nth,
                a_length,
            )?;
            CircuitByte::select_ifle_with_unchecked(
                cs.ns(|| {
                    format!(
                        "fifth section:{}th bit is the fifth section i < a_add_b_length",
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

    // sixth section (range increasing: c:245-256, range decreasing: b:0-64)
    assert!(MAX_PREFIX_LENGTH <= MAX_PREFIX_LENGTH + MAX_SECRET_LENGTH);
    for i in MAX_PREFIX_LENGTH..MAX_PREFIX_LENGTH + MAX_SECRET_LENGTH {
        let nth = CircuitNum::from_fixed_fe_with_known_length(
            cs.ns(|| format!("sixth section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
        let index_b = a_add_b_length_cn.get_num().sub(
            cs.ns(|| format!("sixth section:calculate index_b:a_len + b_len - {}", i)),
            nth.get_num(),
        )?;
        let index_c = nth.get_num().sub(
            cs.ns(|| format!("sixth section:calculate index_c:{} - a_len - b_len", i)),
            a_add_b_length_cn.get_num(),
        )?;
        let searched_b_char = search_char(
            cs.ns(|| format!("sixth section:search b {}th char", i)),
            b,
            &index_b,
            i - MAX_PREFIX_LENGTH..MAX_SECRET_LENGTH,
        )?;
        let searched_c_char = search_char(
            cs.ns(|| format!("sixth section:search c {}th char", i)),
            c,
            &index_c,
            0..i - MIN_PREFIX_LENGTH + MIN_SECRET_LENGTH,
        )?;
        let selected_char = CircuitByte::select_ifle_with_unchecked(
            cs.ns(|| {
                format!(
                    "sixth section:{}th bit is the sixth section corresponding range",
                    i
                )
            }),
            &searched_b_char,
            &searched_c_char,
            &nth,
            &a_add_b_length_cn,
        )?;
        selecting_string.push(selected_char);
    }

    // seventh section (range decreasing: c:245-256)
    assert!(MAX_PREFIX_LENGTH + MAX_SECRET_LENGTH <= MAX_HASH_PREIMAGE_LENGTH);
    for i in MAX_PREFIX_LENGTH + MAX_SECRET_LENGTH..MAX_HASH_PREIMAGE_LENGTH {
        let index_c = AllocatedFr::constant(
            cs.ns(|| format!("seventh section:{}th", i)),
            F::from(i as u128),
        )?
        .sub(
            cs.ns(|| format!("seventh section:calculate index_c:{} - a_len - b_len", i)),
            a_add_b_length_cn.get_num(),
        )?;
        let selected_char = search_char(
            cs.ns(|| {
                format!(
                    "seventh section:{}th bit is the seventh section corresponding range",
                    i
                )
            }),
            c,
            &index_c,
            i - MAX_PREFIX_LENGTH..MAX_HASH_PREIMAGE_LENGTH - MIN_PREFIX_LENGTH - MIN_SECRET_LENGTH,
        )?;
        selecting_string.push(selected_char);
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
    use crate::test_constraint_system::TestConstraintSystem;
    use ark_bn254::Fr;

    let mut cs = TestConstraintSystem::<Fr>::new();

    // modify that the global variable: prefix length:1-5, secret length:3-7, suffix length:10-11
    let padding = "0"; // must be single char, or else fill it to MAX_HASH_PREIMAGE_LENGTH
    let secret = "christian.schneider@androidloves.me";
    let mut padding_message = "from:Christian Schneider Christian Schneider Christian Schneider <christian.schneider@androidloves.me>\r\nsubject:this is a test mail\r\ndate:Sat, 14 Mar 2020 21:48:57 +0100\r\nmessage-id:<4c2828df-2dae-74ff-2fa7-e6ac36100341@androidloves.me>\r\nto:mail@kmille.wtf\r\ncontent-type:text/plain; charset=utf-8; format=flowed\r\ncontent-transfer-encoding:7bit\r\ndkim-signature:v=1; a=rsa-sha256; c=relaxed/relaxed; d=androidloves.me; s=2019022801; t=1584218937; h=from:from:reply-to:subject:subject:date:date:message-id:message-id: to:to:cc:content-type:content-type: content-transfer-encoding:content-transfer-encoding; bh=aeLbTnlUQQv2UFEWKHeiL5Q0NjOwj4ktNSInk8rN/P0=; b=".to_string();
    padding_message.push_str(&*padding.repeat(MAX_HASH_PREIMAGE_LENGTH - padding_message.len()));

    let (c, _) = crate::generate_circuit_instance(secret.to_string(), padding_message, None);
    c.generate_constraints(&mut cs).unwrap();

    println!("num_constraints: {}", cs.num_constraints());
    println!("unconstrained: {}", cs.find_unconstrained());
    if let Some(err) = cs.which_is_unsatisfied() {
        panic!("error: {}", err);
    }
}
