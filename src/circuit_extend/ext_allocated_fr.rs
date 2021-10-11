use crate::circuit_extend::ExtendFunction;
use ark_ff::PrimeField;
use ckb_gadgets::algebra::boolean::{AllocatedBit, Boolean};
use ckb_gadgets::algebra::fr::AllocatedFr;
use ckb_r1cs::{ConstraintSystem, SynthesisError};

impl<F, CS> ExtendFunction<F, CS> for AllocatedFr<F>
where
    F: PrimeField,
    CS: ConstraintSystem<F>,
{
    fn add(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError> {
        let temp = match (self.get_value(), other.get_value()) {
            (Some(a), Some(b)) => {
                // return (a - b)
                let mut a = a;
                a.add_assign(&b);
                Ok(a)
            }
            _ => Err(SynthesisError::AssignmentMissing),
        };

        let alloc_var = Self::alloc(cs.ns(|| "add num"), || temp)?;

        cs.enforce(
            || "addition constraint",
            |lc| lc + self.get_variable() + other.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + alloc_var.get_variable(),
        );

        Ok(alloc_var)
    }

    fn mul(&self, _cs: CS, _other: &Self) -> Result<Self, SynthesisError> {
        todo!()
    }

    fn equals(mut cs: CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError> {
        let r_value = match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => Some(a == b),
            _ => None,
        };

        let r = AllocatedBit::alloc(cs.ns(|| "r"), r_value)?;

        let delta_value = match (a.get_value(), b.get_value()) {
            (Some(a), Some(b)) => {
                // return (a - b)
                let mut a = a;
                a.sub_assign(&b);
                Some(a)
            }
            _ => None,
        };

        let delta_inv_value = delta_value.as_ref().map(|delta_value| {
            let tmp = delta_value.clone();
            if tmp.is_zero() {
                F::one() // we can return any number here, it doesn't matter
            } else {
                tmp.inverse().unwrap()
            }
        });

        let delta_inv = Self::alloc(cs.ns(|| "delta_inv"), || {
            delta_inv_value.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Allocate `t = delta * delta_inv`
        // If `delta` is non-zero (a != b), `t` will equal 1
        // If `delta` is zero (a == b), `t` cannot equal 1
        let t_value = match (delta_value, delta_inv_value) {
            (Some(a), Some(b)) => {
                let mut t = a.clone();
                t.mul_assign(&b);
                Ok(t)
            }
            _ => Err(SynthesisError::AssignmentMissing),
        };

        let t = Self::alloc(cs.ns(|| "t"), || t_value)?;

        // Constrain allocation:
        // t = (a - b) * delta_inv
        cs.enforce(
            || "t = (a - b) * delta_inv",
            |zero| zero + a.get_variable() - b.get_variable(),
            |zero| zero + delta_inv.get_variable(),
            |zero| zero + t.get_variable(),
        );

        // Constrain:
        // (a - b) * (t - 1) == 0
        // This enforces that correct `delta_inv` was provided,
        // and thus `t` is 1 if `(a - b)` is non zero (a != b )
        cs.enforce(
            || "(a - b) * (t - 1) == 0",
            |zero| zero + a.get_variable() - b.get_variable(),
            |zero| zero + t.get_variable() - CS::one(),
            |zero| zero,
        );

        // Constrain:
        // (a - b) * r == 0
        // This enforces that `r` is zero if `(a - b)` is non-zero (a != b)
        cs.enforce(
            || "(a - b) * r == 0",
            |zero| zero + a.get_variable() - b.get_variable(),
            |zero| zero + r.get_variable(),
            |zero| zero,
        );

        // Constrain:
        // (t - 1) * (r - 1) == 0
        // This enforces that `r` is one if `t` is not one (a == b)
        cs.enforce(
            || "(t - 1) * (r - 1) == 0",
            |zero| zero + t.get_variable() - CS::one(),
            |zero| zero + r.get_variable() - CS::one(),
            |zero| zero,
        );
        Ok(Boolean::from(r))
    }

    fn less_than(&self, _cs: CS, _other: &Self) -> Result<Boolean, SynthesisError> {
        todo!()
    }

    fn conditionally_select(
        mut cs: CS,
        a: &Self,
        b: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError> {
        let c = Self::alloc(cs.ns(|| "conditional select result"), || {
            if condition
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?
            {
                a.get_value().ok_or(SynthesisError::AssignmentMissing)
            } else {
                b.get_value().ok_or(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "conditional select constraint",
            |zero| zero + a.get_variable() - b.get_variable(),
            |_| condition.lc(CS::one(), F::one()),
            |zero| zero + c.get_variable() - b.get_variable(),
        );
        Ok(c)
    }
}
