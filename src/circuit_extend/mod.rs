mod circuit_num;
mod circuit_string;
mod ext_allocated_fr;

pub use circuit_num::CircuitNum;
pub use circuit_string::{CircuitByte, CircuitString};

use ark_ff::PrimeField;
use ckb_gadgets::algebra::boolean::Boolean;
use ckb_r1cs::{ConstraintSystem, SynthesisError};

pub trait ExtendFunction<F, CS>: Sized + Clone
where
    F: PrimeField,
    CS: ConstraintSystem<F>,
{
    fn add(&self, cs: CS, other: &Self) -> Result<Self, SynthesisError>;

    fn sub(&self, cs: CS, other: &Self) -> Result<Self, SynthesisError>;

    fn mul(&self, cs: CS, other: &Self) -> Result<Self, SynthesisError>;

    fn constant(cs: CS, constant: F) -> Result<Self, SynthesisError>;

    fn equals(cs: CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError>;

    fn conditionally_select(
        cs: CS,
        a: &Self,
        b: &Self,
        condition: &Boolean,
    ) -> Result<Self, SynthesisError>;

    fn select_ifeq(cs: CS, a: &Self, b: &Self, x: &Self, y: &Self) -> Result<Self, SynthesisError>;

    fn select_ifle(
        cs: CS,
        a: &Self,
        b: &Self,
        x: &CircuitNum<F>,
        y: &CircuitNum<F>,
    ) -> Result<Self, SynthesisError>;
}
