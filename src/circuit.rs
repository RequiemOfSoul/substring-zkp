use crate::circuit_extend::{CircuitByte, CircuitString};
use crate::circuit_extend::{CircuitNum, ExtendFunction};
use crate::params::{
    LENGTH_REPR_BIT_WIDTH, MAX_HASH_PREIMAGE_LENGTH, MIN_HASH_PREIMAGE_LENGTH,
    MIN_PREFIX_BIT_WIDTH, MIN_PREFIX_LENGTH, MIN_SECRET_BIT_WIDTH, MIN_SECRET_LENGTH,
    MIN_SUFFIX_LENGTH, PREFIX_BIT_WIDTH, PREFIX_LENGTH, SECRET_BIT_WIDTH, SECRET_LENGTH,
};
use crate::utils::pack_bits_to_element;
use ark_ff::PrimeField;
use ark_std::ops::Range;
use ckb_gadgets::algebra::boolean::Boolean;
use ckb_gadgets::algebra::fr::AllocatedFr;
use ckb_gadgets::hashes::abstract_hash::AbstractHash;
use ckb_gadgets::hashes::sha256::{sha256, AbstractHashSha256, AbstractHashSha256Output};
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
    pub message_hash: Option<F>, // need assert!

    pub a_bytes: Option<Vec<u8>>,
    pub b_bytes: Option<Vec<u8>>,
    pub secret_bytes: Option<Vec<u8>>,

    pub secret_commitment: Option<Vec<u8>>,
    pub all_string_commitment: Option<Vec<u8>>,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for SecretStringCircuit<F> {
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
        // let secret_commitment = sha256(cs.ns(|| "calculate secret commitment"), secret_bits)?;
        let all_string_commitment_out = AbstractHashSha256::hash_enforce(
            cs.ns(|| "all string commitment out"),
            &[&a_var, &secret_var, &b_var],
        )?;
        // let signature_message_hash = sha256(cs.ns(|| "calculate signature message hash"), message_bits)?;

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

fn select_correct_preimage<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    a: &CircuitString<F>,
    b: &CircuitString<F>,
    c: &CircuitString<F>,
) -> Result<Vec<CircuitByte<F>>, SynthesisError> {
    let a_length = a.get_length();
    let b_length = b.get_length();
    // let c_length = c.get_length();

    let a_add_b_length = a_length
        .get_num()
        .add(cs.ns(|| "a_len + b_len"), b_length.get_num())?;
    let a_add_b_length = CircuitNum::from_fr_with_known_length(
        cs.ns(|| "a + b_length as CircuitNum"),
        a_add_b_length,
        LENGTH_REPR_BIT_WIDTH,
    )?;
    let mut selecting_string = Vec::with_capacity(MAX_HASH_PREIMAGE_LENGTH);

    // first section
    for i in 0..MIN_PREFIX_BIT_WIDTH {
        selecting_string.push(a[i].clone());
    }

    // second section
    for i in MIN_PREFIX_BIT_WIDTH..MIN_PREFIX_BIT_WIDTH + MIN_SECRET_BIT_WIDTH {
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
            &a_length,
        )?;
        selecting_string.push(select_char);
    }

    // third section
    for i in MIN_PREFIX_BIT_WIDTH + MIN_SECRET_BIT_WIDTH..PREFIX_BIT_WIDTH {
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
            a_add_b_length.get_num(),
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
                        "Third section:{}th bit is the third section corresponding range",
                        i
                    )
                }),
                &searched_a_char,
                &searched_b_char,
                &nth,
                &a_length,
            )?;
            CircuitByte::select_ifle_with_unchecked(
                cs.ns(|| {
                    format!(
                        "Third section:{}th bit is the third section corresponding range",
                        i
                    )
                }),
                &selected_char,
                &searched_c_char,
                &nth,
                &a_add_b_length,
            )?
        };
        selecting_string.push(selected_char);
    }

    // fourth section
    for i in PREFIX_BIT_WIDTH..PREFIX_BIT_WIDTH + SECRET_BIT_WIDTH {
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
            a_add_b_length.get_num(),
        )?;
        let searched_b_char = search_char(
            cs.ns(|| format!("Fourth section:search b {}th char", i)),
            a,
            &index_b,
            0..SECRET_LENGTH,
        )?;
        let searched_c_char = search_char(
            cs.ns(|| format!("Fourth section:search c {}th char", i)),
            b,
            &index_c,
            0..PREFIX_LENGTH + SECRET_LENGTH - MIN_PREFIX_LENGTH - MIN_SECRET_LENGTH,
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
            &a_add_b_length,
        )?;
        selecting_string.push(select_char);
    }

    // fifth section
    for i in PREFIX_LENGTH + SECRET_LENGTH..MIN_HASH_PREIMAGE_LENGTH {
        let nth = CircuitNum::from_fe_with_known_length(
            cs.ns(|| format!("Fifth section:{}th", i)),
            || Ok(F::from(i as u128)),
            LENGTH_REPR_BIT_WIDTH,
        )?;
        let index_c = nth.get_num().sub(
            cs.ns(|| format!("Fifth section:calculate index_c:{} - a_len - b_len", i)),
            a_add_b_length.get_num(),
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
            a_add_b_length.get_num(),
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
            MIN_HASH_PREIMAGE_LENGTH - PREFIX_LENGTH - SECRET_LENGTH..MAX_HASH_PREIMAGE_LENGTH,
        )?;
        selecting_string.push(search_c_char);
    }
    Ok(selecting_string)
}

fn search_char<F: PrimeField, CS: ConstraintSystem<F>>(
    mut cs: CS,
    string: &CircuitString<F>,
    index: &AllocatedFr<F>,
    range: Range<usize>,
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
