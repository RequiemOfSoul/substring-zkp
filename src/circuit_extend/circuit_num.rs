use crate::circuit_extend::ExtendFunction;
use ark_ff::{BitIteratorBE, FpParameters, PrimeField};
use ckb_gadgets::algebra::boolean::{AllocatedBit, Boolean};
use ckb_gadgets::algebra::fr::AllocatedFr;
use ckb_r1cs::{ConstraintSystem, LinearCombination, SynthesisError, Variable};

#[derive(Clone)]
pub struct CircuitNum<F: PrimeField> {
    num: AllocatedFr<F>,
    le_bits: Vec<Boolean>,
    length: usize,
}

impl<F: PrimeField> CircuitNum<F> {
    pub fn from_fe_with_known_length<
        Function: FnOnce() -> Result<F, SynthesisError>,
        CS: ConstraintSystem<F>,
    >(
        mut cs: CS,
        field_element: Function,
        max_length: usize,
    ) -> Result<Self, SynthesisError> {
        assert!(max_length <= F::Params::MODULUS_BITS as usize);
        let num = AllocatedFr::alloc(cs.ns(|| "number from field element"), field_element)?;

        CircuitNum::from_fr_with_known_length(cs.ns(|| "generate CircuitString"), num, max_length)
    }

    pub fn from_fixed_fe_with_known_length<
        Function: FnOnce() -> Result<F, SynthesisError>,
        CS: ConstraintSystem<F>,
    >(
        mut cs: CS,
        field_element: Function,
        max_length: usize,
    ) -> Result<Self, SynthesisError> {
        assert!(max_length <= F::Params::MODULUS_BITS as usize);
        let num = AllocatedFr::constant(cs.ns(|| "number from field element"), field_element()?)?;

        CircuitNum::from_fr_with_known_length(cs.ns(|| "generate CircuitString"), num, max_length)
    }

    pub fn from_fr_with_known_length<CS: ConstraintSystem<F>>(
        mut cs: CS,
        fr: AllocatedFr<F>,
        max_length: usize,
    ) -> Result<Self, SynthesisError> {
        assert!(max_length <= F::Params::MODULUS_BITS as usize);
        let bits = get_bits_le_fixed(&fr, cs.ns(|| "into_bits_le_fixed"), max_length)?;
        assert_eq!(bits.len(), max_length);

        let ce = CircuitNum {
            num: fr,
            le_bits: bits,
            length: max_length,
        };
        Ok(ce)
    }

    pub fn less_than_fixed<CS: ConstraintSystem<F>>(
        mut cs: CS,
        x: &Self,
        y: &Self,
    ) -> Result<Boolean, SynthesisError> {
        let length = std::cmp::max(x.length, y.length);
        assert!(
            length < F::Params::CAPACITY as usize,
            "comparison is only supported for fixed-length elements"
        );

        let two = F::from(2u128);
        let power = F::from(length as u128);
        let mut base = two.pow(&power.into_repr());
        base.sub_assign(&F::one());

        let expr = AllocatedFr::alloc(cs.ns(|| "calculate base - x + y"), || {
            match (x.get_value(), y.get_value()) {
                (Some(x), Some(y)) => {
                    let mut temp = base;
                    temp.sub_assign(&x);
                    temp.add_assign(&y);
                    Ok(temp)
                }
                _ => Err(SynthesisError::AssignmentMissing),
            }
        })?;
        cs.enforce(
            || "check base - x + y constraint",
            |lc| lc + (base, CS::one()) - x.get_variable() + y.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + expr.get_variable(),
        );
        let bits = get_bits_le_fixed(&expr, cs.ns(|| "diff bits"), length + 1)?;

        Ok(*bits
            .last()
            .expect("expr bit representation should always contain at least one bit"))
    }

    pub fn equals<CS: ConstraintSystem<F>>(
        mut cs: CS,
        x: &Self,
        y: &Self,
    ) -> Result<Boolean, SynthesisError> {
        let is_equal = AllocatedFr::equals(cs.ns(|| "equals"), x.get_num(), y.get_num())?;
        Ok(is_equal)
    }

    pub fn select_ifeq<CS: ConstraintSystem<F>>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        x: &Self,
        y: &Self,
    ) -> Result<Self, SynthesisError> {
        let eq = Self::equals(cs.ns(|| "eq"), a, b)?;
        Self::conditionally_select_with_number_strict(cs.ns(|| "select"), x, y, &eq)
    }

    pub fn select_ifle<CS: ConstraintSystem<F>>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        x: &Self,
        y: &Self,
    ) -> Result<Self, SynthesisError> {
        let eq = Self::less_than_fixed(cs.ns(|| "eq"), a, b)?;
        Self::conditionally_select_with_number_strict(cs.ns(|| "select"), x, y, &eq)
    }

    pub fn conditionally_select_with_number_strict<CS: ConstraintSystem<F>>(
        mut cs: CS,
        x: &Self,
        y: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let selected_number = AllocatedFr::conditionally_select(
            cs.ns(|| "conditionally_select"),
            x.get_num(),
            y.get_num(),
            condition,
        )?;

        CircuitNum::from_fr_with_known_length(
            cs.ns(|| "chosen number as ce"),
            selected_number,
            y.length,
        )
    }

    pub fn get_num(&self) -> &AllocatedFr<F> {
        &self.num
    }

    pub fn get_value(&self) -> Option<F> {
        self.num.get_value()
    }

    pub fn get_variable(&self) -> Variable {
        self.get_num().get_variable()
    }

    fn len(&self) -> usize {
        self.length
    }

    pub fn get_bits_le(&self) -> &[Boolean] {
        &self.le_bits
    }
}

pub fn get_bits_le_fixed<CS, F>(
    allocated_fr: &AllocatedFr<F>,
    mut cs: CS,
    bit_length: usize,
) -> Result<Vec<Boolean>, SynthesisError>
where
    CS: ConstraintSystem<F>,
    F: PrimeField,
{
    assert!(bit_length <= F::Params::MODULUS_BITS as usize);
    let bits = field_into_allocated_bits_le_fixed(&mut cs, allocated_fr.get_value(), bit_length)?;

    let mut packed_lc = LinearCombination::zero();
    let mut coeff = F::one();

    for bit in bits.iter() {
        packed_lc += (coeff, bit.get_variable());
        coeff = coeff.double();
    }

    cs.enforce(
        || "unpacking constraint",
        |_| packed_lc,
        |zero| zero + CS::one(),
        |zero| zero + allocated_fr.get_variable(),
    );

    Ok(bits.into_iter().map(Boolean::from).collect())
}

pub fn field_into_allocated_bits_le_fixed<CS: ConstraintSystem<F>, F: PrimeField>(
    mut cs: CS,
    value: Option<F>,
    bit_length: usize,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
    assert!(bit_length <= F::Params::MODULUS_BITS as usize);
    // Deconstruct in big-endian bit order
    let values = match value {
        Some(ref value) => {
            let mut field_char = BitIteratorBE::new(F::Params::MODULUS);

            let mut tmp = Vec::with_capacity(F::Params::MODULUS_BITS as usize);

            let mut found_one = false;
            for b in BitIteratorBE::new(value.into_repr()) {
                // Skip leading bits
                found_one |= field_char.next().unwrap();
                if !found_one {
                    continue;
                }

                tmp.push(Some(b));
            }

            assert_eq!(tmp.len(), F::Params::MODULUS_BITS as usize);

            tmp
        }
        None => vec![None; F::Params::MODULUS_BITS as usize],
    };

    // Allocate in little-endian order
    let bits = values
        .into_iter()
        .rev()
        .enumerate()
        .take(bit_length)
        .map(|(i, b)| AllocatedBit::alloc(cs.ns(|| format!("bit {}", i)), b))
        .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(bits)
}
