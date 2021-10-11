use ark_ff::PrimeField;
use ckb_gadgets::algebra::boolean::Boolean;
use ckb_gadgets::algebra::fr::AllocatedFr;

#[derive(Clone)]
struct CircuitChar<F: PrimeField>(CircuitNum<F, 8>);

#[derive(Clone)]
pub struct CircuitString<F: PrimeField> {
    string: CircuitChar<F>,
    length: usize,
}

#[derive(Clone)]
pub struct CircuitNum<F: PrimeField, const T: usize> {
    num: AllocatedFr<F>,
    le_bits: [Boolean; T],
}
