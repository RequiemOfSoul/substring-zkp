mod circuit_char;
mod circuit_string;
mod ext_allocated_fr;

pub use circuit_string::CircuitString;

use ark_ff::PrimeField;
use ckb_gadgets::algebra::boolean::Boolean;
use ckb_r1cs::{ConstraintSystem, SynthesisError};

trait ExtendFunction<F, CS>: Sized
where
    F: PrimeField,
    CS: ConstraintSystem<F>,
{
    fn add(&self, cs: CS, other: &Self) -> Result<Self, SynthesisError>;

    fn mul(&self, cs: CS, other: &Self) -> Result<Self, SynthesisError>;

    fn equals(cs: CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError>;

    fn less_than(&self, cs: CS, other: &Self) -> Result<Boolean, SynthesisError>;

    fn conditionally_select(
        cs: CS,
        a: &Self,
        b: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError>;
}
