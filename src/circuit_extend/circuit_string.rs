use crate::circuit_extend::circuit_num::get_bits_le_fixed;
use crate::circuit_extend::{CircuitNum, ExtendFunction};
use crate::params::LENGTH_REPR_BIT_WIDTH;
use crate::utils::{calculate_ascii_char, pack_bits_to_element};
use ark_ff::{FpParameters, PrimeField};
use ark_std::convert::TryInto;
use ark_std::ops::Index;
use ckb_gadgets::algebra::boolean::Boolean;
use ckb_gadgets::algebra::fr::AllocatedFr;
use ckb_r1cs::{ConstraintSystem, SynthesisError};

#[derive(Clone)]
pub struct CircuitString<F: PrimeField> {
    packed_nums: Vec<CircuitNum<F>>,
    string: Vec<CircuitByte<F>>,
    length: CircuitNum<F>,
}

impl<F: PrimeField> CircuitString<F> {
    pub fn from_string_witness_with_fixed_length<CS: ConstraintSystem<F>>(
        mut cs: CS,
        string_witness: &[F],
        max_length: usize,
    ) -> Result<Self, SynthesisError> {
        assert!(string_witness.len() * 31 <= max_length);
        let split_length = if max_length % 31 == 0 {
            max_length / 31
        } else {
            max_length / 31 + 1
        };

        let mut packed_nums = Vec::with_capacity(split_length);
        let mut string = Vec::with_capacity(max_length);
        let mut calc_length = AllocatedFr::constant(cs.ns(|| "initialized zero"), F::zero())?;

        for (i, split_fe) in string_witness.iter().enumerate() {
            let packed_split =
                AllocatedFr::alloc_input(cs.ns(|| format!("add {}th section fr", i)), || {
                    Ok(*split_fe)
                })?;
            let num = CircuitNum::from_fr_with_known_length(
                cs.ns(|| format!("packed {}th Fr", i)),
                packed_split,
                248,
            )?;
            for (j, bits) in num.get_bits_le().chunks_exact(8).enumerate() {
                calculate_ascii_char(
                    &mut calc_length,
                    cs.ns(|| format!("statistics:{}th chunk->{}th byte", i, j)),
                    bits,
                )?;
                string.push(CircuitByte::from_le_bits(
                    cs.ns(|| format!("{}th chunk->{}th byte", i, j)),
                    bits.to_vec(),
                )?);
            }
            packed_nums.push(num);
        }

        let length = CircuitNum::from_fr_with_known_length(
            cs.ns(|| "generate CircuitString length"),
            calc_length,
            LENGTH_REPR_BIT_WIDTH,
        )?;

        Ok(CircuitString {
            packed_nums,
            string,
            length,
        })
    }

    pub fn inputize<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<(), SynthesisError> {
        for (i, byte) in self.packed_nums.iter().enumerate() {
            byte.get_num()
                .inputize(cs.ns(|| format!("inputize {}th byte", i)))?;
        }
        Ok(())
    }

    pub fn get_bytes(&self) -> &[CircuitByte<F>] {
        &self.string
    }

    pub fn get_length(&self) -> &CircuitNum<F> {
        &self.length
    }

    pub fn get_bits_le(&self) -> Vec<Boolean> {
        let mut bits = Vec::with_capacity(self.string.len() * 8);
        self.string
            .iter()
            .for_each(|byte| bits.extend_from_slice(byte.get_bits_le()));
        bits
    }
}

impl<F: PrimeField> Index<usize> for CircuitString<F> {
    type Output = CircuitByte<F>;

    fn index(&self, index: usize) -> &Self::Output {
        assert!(
            F::from(index as u128) < self.length.get_value().unwrap(),
            "index out of range"
        );
        &self.string[index]
    }
}

#[derive(Clone)]
pub struct CircuitByte<F: PrimeField> {
    num: AllocatedFr<F>,
    le_bits: Option<[Boolean; 8]>,
}

impl<F: PrimeField> CircuitByte<F> {
    pub fn from_fr_with_checked<CS: ConstraintSystem<F>>(
        mut cs: CS,
        num: AllocatedFr<F>,
    ) -> Result<Self, SynthesisError> {
        let bits = get_bits_le_fixed(&num, cs.ns(|| "diff bits"), 8)?;

        Ok(CircuitByte {
            num,
            le_bits: Some(
                bits.try_into()
                    .map_err(|_| SynthesisError::AssignmentMissing)?,
            ),
        })
    }

    pub fn from_fr_with_unchecked(num: AllocatedFr<F>) -> Self {
        CircuitByte { num, le_bits: None }
    }

    pub fn from_fe_with_checked<CS: ConstraintSystem<F>>(
        mut cs: CS,
        field_element: F,
    ) -> Result<Self, SynthesisError> {
        assert!(field_element < F::from(256_u128));
        let num = AllocatedFr::alloc(cs.ns(|| "number from field element"), || Ok(field_element))?;

        CircuitByte::from_fr_with_checked(cs.ns(|| "generate CircuitString"), num)
    }

    pub fn from_le_bits<CS: ConstraintSystem<F>>(
        mut cs: CS,
        bits: Vec<Boolean>,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(bits.len() % 8, 0, "bits is not byte-aligned");
        assert!(bits.len() <= F::Params::MODULUS_BITS as usize);

        let number = pack_bits_to_element(cs.ns(|| "pack back"), &bits)?;

        Ok(CircuitByte {
            num: number,
            le_bits: Some(
                bits.try_into()
                    .map_err(|_| SynthesisError::AssignmentMissing)?,
            ),
        })
    }

    pub fn conditionally_select_with_unchecked<CS: ConstraintSystem<F>>(
        mut cs: CS,
        x: &Self,
        y: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let selected_number = AllocatedFr::conditionally_select(
            cs.ns(|| "conditionally_select"),
            &x.num,
            &y.num,
            condition,
        )?;

        Ok(CircuitByte::from_fr_with_unchecked(selected_number))
    }

    pub fn conditionally_select_with_checked<CS: ConstraintSystem<F>>(
        mut cs: CS,
        x: &Self,
        y: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let selected_number = AllocatedFr::conditionally_select(
            cs.ns(|| "conditionally_select"),
            &x.num,
            &y.num,
            condition,
        )?;

        CircuitByte::from_fr_with_checked(cs.ns(|| "chosen number as ce"), selected_number)
    }

    pub fn select_ifle_with_unchecked<CS: ConstraintSystem<F>>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        x: &CircuitNum<F>,
        y: &CircuitNum<F>,
    ) -> Result<Self, SynthesisError> {
        let eq = CircuitNum::less_than_fixed(cs.ns(|| "eq"), x, y)?;
        Self::conditionally_select_with_unchecked(cs.ns(|| "select"), a, b, &eq)
    }

    pub fn generate_bits_le<CS: ConstraintSystem<F>>(
        &mut self,
        mut cs: CS,
    ) -> Result<&[Boolean], SynthesisError> {
        let bits = get_bits_le_fixed(&self.num, cs.ns(|| "unpacked AllocatedFr"), 8)?;
        self.le_bits = Some(
            bits.try_into()
                .map_err(|_| SynthesisError::AssignmentMissing)?,
        );
        Ok(self.le_bits.as_ref().unwrap())
    }

    pub fn get_num(&self) -> &AllocatedFr<F> {
        &self.num
    }

    pub fn get_bits_le(&self) -> &[Boolean] {
        self.le_bits.as_ref().unwrap()
    }
}
