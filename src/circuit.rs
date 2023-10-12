// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! PLONK turbo composer definitions

mod compiler;
mod prover;
mod verifier;

pub use compiler::Compiler;
pub use prover::Prover;
pub use verifier::Verifier;

use bls_12_381::Fr as BlsScalar;
use core::fmt::Debug;
use core::{cmp, ops};
use hashbrown::HashMap;
use jub_jub::compute_windowed_naf;
use sp_std::vec;
use zksnarks::{plonk::wire::PrivateWire, Constraint};
use zkstd::common::{
    CurveGroup, FftField, Group, Neg, Pairing, PrimeField, Ring, SigUtils,
    TwistedEdwardsAffine, Vec,
};

use crate::bit_iterator::BitIterator8;
use crate::error::Error;
use crate::gadget::ecc::WnafRound;
use crate::gadget::WitnessPoint;
use crate::permutation::Permutation;

/// Circuit implementation that can be proved by a Composer
///
/// The default implementation will be used to generate the proving arguments.
pub trait Circuit<P: Pairing>: Default + Debug {
    /// Circuit definition
    fn synthesize(
        &self,
        composer: &mut ConstraintSystem<P>,
    ) -> Result<(), Error>;
}

/// Construct and prove circuits
#[derive(Debug, Clone)]
pub struct ConstraintSystem<P: Pairing> {
    /// Constraint system gates
    pub(crate) constraints: Vec<Constraint<P::ScalarField>>,

    /// Sparse representation of the public inputs
    pub(crate) instance: HashMap<usize, P::ScalarField>,

    /// Witness values
    pub(crate) witness: Vec<P::ScalarField>,

    /// Permutation argument.
    pub(crate) perm: Permutation<P>,
}

impl<P: Pairing> ops::Index<PrivateWire> for ConstraintSystem<P> {
    type Output = P::ScalarField;

    fn index(&self, w: PrivateWire) -> &Self::Output {
        &self.witness[w.index()]
    }
}

impl<P: Pairing> ConstraintSystem<P> {
    /// Zero representation inside the constraint system.
    ///
    /// A turbo composer expects the first witness to be always present and to
    /// be zero.
    pub const ZERO: PrivateWire = PrivateWire::new(0);

    /// `One` representation inside the constraint system.
    ///
    /// A turbo composer expects the 2nd witness to be always present and to
    /// be one.
    const ONE: PrivateWire = PrivateWire::new(1);

    /// Identity point representation inside the constraint system
    const IDENTITY: WitnessPoint = WitnessPoint::new(Self::ZERO, Self::ONE);

    pub(crate) fn public_input_indexes(&self) -> Vec<usize> {
        let mut public_input_indexes: Vec<_> =
            self.instance.keys().copied().collect();

        public_input_indexes.as_mut_slice().sort();

        public_input_indexes
    }

    pub(crate) fn public_inputs(&self) -> Vec<P::ScalarField> {
        self.public_input_indexes()
            .iter()
            .filter_map(|idx| self.instance.get(idx).copied())
            .collect()
    }

    pub(crate) fn dense_public_inputs(
        public_input_indexes: &[usize],
        public_inputs: &[P::ScalarField],
        size: usize,
    ) -> Vec<P::ScalarField> {
        let mut dense_public_inputs = vec![P::ScalarField::zero(); size];

        public_input_indexes
            .iter()
            .zip(public_inputs.iter())
            .for_each(|(idx, pi)| dense_public_inputs[*idx] = *pi);

        dense_public_inputs
    }

    fn uninitialized(capacity: usize) -> Self {
        Self {
            constraints: Vec::with_capacity(capacity),
            instance: HashMap::new(),
            witness: Vec::with_capacity(capacity),
            perm: Permutation::new(),
        }
    }

    pub(crate) fn constraints(&self) -> usize {
        self.constraints.len()
    }

    /// Allocate a witness value into the composer and return its index.
    pub fn append_witness<W: Into<P::ScalarField>>(
        &mut self,
        witness: W,
    ) -> PrivateWire {
        self.append_witness_internal(witness.into())
    }

    /// Append a new width-4 poly gate/constraint.
    pub fn append_custom_gate(
        &mut self,
        constraint: Constraint<P::ScalarField>,
    ) {
        #[allow(deprecated)]
        self.append_custom_gate_internal(constraint)
    }

    ///
    pub fn append_witness_internal(
        &mut self,
        witness: P::ScalarField,
    ) -> PrivateWire {
        let n = self.witness.len();

        // Get a new Witness from the permutation
        self.perm.new_witness();

        // Bind the allocated witness
        self.witness.push(witness);

        PrivateWire::new(n)
    }

    ///
    pub fn append_custom_gate_internal(
        &mut self,
        constraint: Constraint<P::ScalarField>,
    ) {
        let n = self.constraints.len();

        self.constraints.push(constraint);

        if let Some(pi) = constraint.public_input {
            self.instance.insert(n, pi);
        }

        self.perm.add_witnesses_to_map(
            constraint.w_a,
            constraint.w_b,
            constraint.w_o,
            constraint.w_d,
            n,
        );
    }

    /// Performs a logical AND or XOR op between the inputs provided for the
    /// specified number of bits (counting from the least significant bit).
    ///
    /// Each logic gate adds `(num_bits / 2) + 1` gates to the circuit to
    /// perform the whole operation.
    ///
    /// ## Constraint
    /// - is_component_xor = 1 -> Performs XOR between the first `num_bits` for
    ///   `a` and `b`.
    /// - is_component_xor = 0 -> Performs AND between the first `num_bits` for
    ///   `a` and `b`.
    ///
    /// # Panics
    /// This function will panic if the num_bits specified is not even, ie.
    /// `num_bits % 2 != 0`.
    fn append_logic_component(
        &mut self,
        a: PrivateWire,
        b: PrivateWire,
        num_bits: usize,
        is_component_xor: bool,
    ) -> PrivateWire {
        let num_bits = cmp::min(num_bits, 256);
        let num_quads = num_bits >> 1;

        let bls_four = P::ScalarField::from(4u64);
        let mut left_acc = P::ScalarField::zero();
        let mut right_acc = P::ScalarField::zero();
        let mut out_acc = P::ScalarField::zero();

        // skip bits outside of argument `num_bits`
        let a_bit_iter = BitIterator8::new(self[a].to_bytes());
        let a_bits: Vec<_> = a_bit_iter.skip(256 - num_bits).collect();
        let b_bit_iter = BitIterator8::new(self[b].to_bytes());
        let b_bits: Vec<_> = b_bit_iter.skip(256 - num_bits).collect();

        //
        // * +-----+-----+-----+-----+
        // * |  A  |  B  |  C  |  D  |
        // * +-----+-----+-----+-----+
        // * | 0   | 0   | w1  | 0   |
        // * | a1  | b1  | w2  | d1  |
        // * | a2  | b2  | w3  | d2  |
        // * |  :  |  :  |  :  |  :  |
        // * | an  | bn  | 0   | dn  |
        // * +-----+-----+-----+-----+
        // `an`, `bn` and `dn` are accumulators: `an [& OR ^] bd = dn`
        //
        // each step will shift last computation two bits to the left and add
        // current quad.
        //
        // `wn` product accumulators will safeguard the quotient polynomial.

        let mut constraint = if is_component_xor {
            Constraint::logic_xor(Constraint::default())
        } else {
            Constraint::logic(Constraint::default())
        };

        for i in 0..num_quads {
            // commit every accumulator
            let idx = i * 2;

            let l = (a_bits[idx] as u8) << 1;
            let r = a_bits[idx + 1] as u8;
            let left_quad = l + r;
            let left_quad_bls = P::ScalarField::from(left_quad as u64);

            let l = (b_bits[idx] as u8) << 1;
            let r = b_bits[idx + 1] as u8;
            let right_quad = l + r;
            let right_quad_bls = P::ScalarField::from(right_quad as u64);

            let out_quad_bls = if is_component_xor {
                left_quad ^ right_quad
            } else {
                left_quad & right_quad
            } as u64;
            let out_quad_bls = P::ScalarField::from(out_quad_bls);

            // `w` argument to safeguard the quotient polynomial
            let prod_quad_bls = (left_quad * right_quad) as u64;
            let prod_quad_bls = P::ScalarField::from(prod_quad_bls);

            // Now that we've computed this round results, we need to apply the
            // logic transition constraint that will check that
            //   a_{i+1} - (a_i << 2) < 4
            //   b_{i+1} - (b_i << 2) < 4
            //   d_{i+1} - (d_i << 2) < 4   with d_i = a_i [& OR ^] b_i
            // Note that multiplying by four is the equivalent of shifting the
            // bits two positions to the left.

            left_acc = left_acc * bls_four + left_quad_bls;
            right_acc = right_acc * bls_four + right_quad_bls;
            out_acc = out_acc * bls_four + out_quad_bls;

            let wit_a = self.append_witness(left_acc);
            let wit_b = self.append_witness(right_acc);
            let wit_c = self.append_witness(prod_quad_bls);
            let wit_d = self.append_witness(out_acc);

            constraint = constraint.o(wit_c);

            self.append_custom_gate(constraint);

            constraint = constraint.a(wit_a).b(wit_b).d(wit_d);
        }

        // pad last output with `0`
        // | an  | bn  | 0   | dn  |
        let a = constraint.w_a;
        let b = constraint.w_b;
        let d = constraint.w_d;

        let constraint = Constraint::default().a(a).b(b).d(d);

        self.append_custom_gate(constraint);

        d
    }

    /// Evaluate `jubjub · Generator` as a [`WitnessPoint`]
    ///
    /// `generator` will be appended to the circuit description as constant
    ///
    /// Will error if `jubjub` doesn't fit `Fr`
    pub fn component_mul_generator<A: Into<P::JubjubExtended>>(
        &mut self,
        jubjub: PrivateWire,
        generator: A,
    ) -> Result<WitnessPoint, Error> {
        let generator = generator.into();

        // the number of bits is truncated to the maximum possible. however, we
        // could slice off 3 bits from the top of wnaf since Fr price is
        // 252 bits. Alternatively, we could move to base4 and halve the
        // number of gates considering that the product of wnaf adjacent
        // entries is zero.
        let bits: usize = 256;

        // compute 2^iG
        let mut wnaf_point_multiples: Vec<_> = {
            let mut multiples =
                vec![P::JubjubExtended::ADDITIVE_IDENTITY; bits];

            multiples[0] = generator;

            for i in 1..bits {
                multiples[i] = multiples[i - 1].double();
            }

            multiples
                .iter()
                .map(|point| P::JubjubAffine::from(*point))
                .collect::<Vec<_>>()
        };

        wnaf_point_multiples.reverse();

        // we should error instead of producing invalid proofs - otherwise this
        // can easily become an attack vector to either shutdown prover
        // services or create malicious statements
        let scalar = match P::JubjubScalar::from_bytes(self[jubjub].to_bytes())
        {
            Some(scalar) => scalar,
            None => panic!("Failed to deserialize jubjub scalar"),
        };

        let width = 2;
        let wnaf_entries = compute_windowed_naf(scalar, width);

        debug_assert_eq!(wnaf_entries.len(), bits);

        // initialize the accumulators
        let mut scalar_acc = vec![P::ScalarField::zero()];
        let mut point_acc =
            vec![P::JubjubAffine::from(P::JubjubExtended::ADDITIVE_IDENTITY)];

        // auxillary point to help with checks on the backend
        let two = P::ScalarField::from(2u64);
        let xy_alphas: Vec<_> = wnaf_entries
            .iter()
            .rev()
            .enumerate()
            .map(|(i, entry)| {
                let (scalar_to_add, point_to_add) = match entry {
                    0 => (
                        P::ScalarField::zero(),
                        P::JubjubExtended::ADDITIVE_IDENTITY,
                    ),
                    -1 => (
                        P::ScalarField::one().neg(),
                        -P::JubjubExtended::from(wnaf_point_multiples[i]),
                    ),
                    1 => (
                        P::ScalarField::one(),
                        P::JubjubExtended::from(wnaf_point_multiples[i]),
                    ),
                    _ => return Err(Error::UnsupportedWNAF2k),
                };

                let prev_accumulator = two * scalar_acc[i];
                let scalar = prev_accumulator + scalar_to_add;
                scalar_acc.push(scalar);

                let point =
                    P::JubjubExtended::from(point_acc[i]) + point_to_add;
                point_acc.push(P::JubjubAffine::from(point));

                let point_to_add: P::JubjubAffine = point_to_add.into();

                let x_alpha = point_to_add.get_x();
                let y_alpha = point_to_add.get_y();

                Ok(x_alpha * y_alpha)
            })
            .collect::<Result<_, Error>>()?;

        for i in 0..bits {
            let acc_x = self.append_witness(point_acc[i].get_x());
            let acc_y = self.append_witness(point_acc[i].get_y());
            let accumulated_bit = self.append_witness(scalar_acc[i]);

            // the point accumulator must start from identity and its scalar
            // from zero
            if i == 0 {
                self.assert_equal_constant(acc_x, P::ScalarField::zero(), None);
                self.assert_equal_constant(acc_y, P::ScalarField::one(), None);
                self.assert_equal_constant(
                    accumulated_bit,
                    P::ScalarField::zero(),
                    None,
                );
            }

            let x_beta = wnaf_point_multiples[i].get_x();
            let y_beta = wnaf_point_multiples[i].get_y();

            let xy_alpha = self.append_witness(xy_alphas[i]);
            let xy_beta = x_beta * y_beta;

            let wnaf_round = WnafRound::<PrivateWire, P::ScalarField> {
                acc_x,
                acc_y,
                accumulated_bit,
                xy_alpha,
                x_beta: x_beta.into(),
                y_beta: y_beta.into(),
                xy_beta: xy_beta.into(),
            };

            let constraint =
                Constraint::group_add_curve_scalar(Constraint::default())
                    .left(wnaf_round.x_beta)
                    .right(wnaf_round.y_beta)
                    .constant(wnaf_round.xy_beta)
                    .a(wnaf_round.acc_x)
                    .b(wnaf_round.acc_y)
                    .o(wnaf_round.xy_alpha)
                    .d(wnaf_round.accumulated_bit);

            self.append_custom_gate(constraint)
        }

        // last gate isn't activated for ecc
        let acc_x = self.append_witness(point_acc[bits].get_x());
        let acc_y = self.append_witness(point_acc[bits].get_y());

        // FIXME this implementation presents a plethora of vulnerabilities and
        // requires reworking
        //
        // we are accepting any scalar argument and trusting it to be the
        // expected input. it happens to be correct in this
        // implementation, but can be exploited by malicious provers who
        // might just input anything here
        let last_accumulated_bit = self.append_witness(scalar_acc[bits]);

        // FIXME the gate isn't checking anything. maybe remove?
        let constraint = Constraint::default()
            .a(acc_x)
            .b(acc_y)
            .d(last_accumulated_bit);
        self.append_gate(constraint);

        // constrain the last element in the accumulator to be equal to the
        // input jubjub scalar
        self.assert_equal(last_accumulated_bit, jubjub);

        Ok(WitnessPoint::new(acc_x, acc_y))
    }

    /// Initialize the constraint system with dummy gates
    pub(crate) fn initialized(capacity: usize) -> Self {
        #[allow(deprecated)]
        let mut slf = Self::uninitialized(capacity);

        let zero = slf.append_witness(0);
        let one = slf.append_witness(1);

        slf.assert_equal_constant(zero, 0, None);
        slf.assert_equal_constant(one, 1, None);

        slf.append_dummy_gates();
        slf.append_dummy_gates();

        slf
    }

    /// Append a new width-4 poly gate/constraint.
    ///
    /// The constraint added will enforce the following:
    /// `q_m · a · b  + q_l · a + q_r · b + q_o · o + q_4 · d + q_c + PI = 0`.
    pub fn append_gate(&mut self, constraint: Constraint<P::ScalarField>) {
        let constraint = Constraint::arithmetic(constraint);

        self.append_custom_gate(constraint)
    }

    /// Evaluate the polynomial and append an output that satisfies the equation
    ///
    /// Return `None` if the output selector is zero
    pub fn append_evaluated_output(
        &mut self,
        s: Constraint<P::ScalarField>,
    ) -> Option<PrivateWire> {
        let a = s.w_a;
        let b = s.w_b;
        let d = s.w_d;

        let a = self[a];
        let b = self[b];
        let d = self[d];

        let qm = s.q_m;
        let ql = s.q_l;
        let qr = s.q_r;
        let qd = s.q_d;
        let qc = s.q_c;
        let pi = s.public_input.unwrap_or_else(P::ScalarField::zero);

        let x = qm * a * b + ql * a + qr * b + qd * d + qc + pi;

        let y = s.q_o;

        // Invert is an expensive operation; in most cases, `qo` is going to be
        // either 1 or -1, so we can optimize these
        #[allow(dead_code)]
        let o = {
            const ONE: BlsScalar = BlsScalar::one();
            const MINUS_ONE: BlsScalar = BlsScalar([
                0xfffffffd00000003,
                0xfb38ec08fffb13fc,
                0x99ad88181ce5880f,
                0x5bc8f5f97cd877d8,
            ]);

            // Can't use a match pattern here since `BlsScalar` doesn't derive
            // `PartialEq`
            if y == P::ScalarField::one() {
                Some(-x)
            } else if y == -P::ScalarField::one() {
                Some(x)
            } else {
                y.invert().map(|y| x * (-y))
            }
        };

        o.map(|o| self.append_witness(o))
    }

    /// Adds blinding factors to the witness polynomials with two dummy
    /// arithmetic constraints
    pub fn append_dummy_gates(&mut self) {
        let six = self.append_witness(P::ScalarField::from(6));
        let one = self.append_witness(P::ScalarField::from(1));
        let seven = self.append_witness(P::ScalarField::from(7));
        let min_twenty = self.append_witness(-P::ScalarField::from(20));

        // Add a dummy constraint so that we do not have zero polynomials
        let constraint = Constraint::default()
            .mult(1)
            .left(2)
            .right(3)
            .fourth(1)
            .constant(4)
            .output(4)
            .a(six)
            .b(seven)
            .d(one)
            .o(min_twenty);

        self.append_gate(constraint);

        // Add another dummy constraint so that we do not get the identity
        // permutation
        let constraint = Constraint::default()
            .mult(1)
            .left(1)
            .right(1)
            .constant(127)
            .output(1)
            .a(min_twenty)
            .b(six)
            .o(seven);

        self.append_gate(constraint);
    }

    /// Constrain a scalar into the circuit description and return an allocated
    /// [`PrivateWire`] with its value
    pub fn append_constant<C: Into<P::ScalarField>>(
        &mut self,
        constant: C,
    ) -> PrivateWire {
        let constant = constant.into();
        let witness = self.append_witness(constant);

        self.assert_equal_constant(witness, constant, None);

        witness
    }

    /// Appends a point in affine form as [`WitnessPoint`]
    pub fn append_point<A: Into<P::JubjubAffine>>(
        &mut self,
        affine: A,
    ) -> WitnessPoint {
        let affine = affine.into();

        let x = self.append_witness(affine.get_x());
        let y = self.append_witness(affine.get_y());

        WitnessPoint::new(x, y)
    }

    /// Constrain a point into the circuit description and return an allocated
    /// [`WitnessPoint`] with its coordinates
    pub fn append_constant_point<A: Into<P::JubjubAffine>>(
        &mut self,
        affine: A,
    ) -> WitnessPoint {
        let affine = affine.into();

        let x = self.append_constant(affine.get_x());
        let y = self.append_constant(affine.get_y());

        WitnessPoint::new(x, y)
    }

    /// Appends a point in affine form as [`WitnessPoint`]
    ///
    /// Creates two public inputs as `(x, y)`
    pub fn append_public_point<A: Into<P::JubjubAffine>>(
        &mut self,
        affine: A,
    ) -> WitnessPoint {
        let affine = affine.into();
        let point = self.append_point(affine);

        self.assert_equal_constant(
            *point.x(),
            P::ScalarField::zero(),
            Some(<<<P as zkstd::behave::Pairing>::JubjubAffine as CurveGroup>::Range>::into(-affine.get_x())),
        );

        self.assert_equal_constant(
            *point.y(),
            P::ScalarField::zero(),
            Some(<<<P as zkstd::behave::Pairing>::JubjubAffine as CurveGroup>::Range>::into(-affine.get_y())),
        );

        point
    }

    /// Allocate a witness value into the composer and return its index.
    ///
    /// Create a public input with the scalar
    pub fn append_public<A: Into<P::ScalarField>>(
        &mut self,
        public: A,
    ) -> PrivateWire {
        let public = public.into();
        let witness = self.append_witness(public);

        self.assert_equal_constant(witness, 0, Some(-public));

        witness
    }

    /// Asserts `a == b` by appending a gate
    pub fn assert_equal(&mut self, a: PrivateWire, b: PrivateWire) {
        let constraint = Constraint::default()
            .left(1)
            .right(-P::ScalarField::one())
            .a(a)
            .b(b);

        self.append_gate(constraint);
    }

    /// Adds a logical AND gate that performs the bitwise AND between two values
    /// for the specified first `num_bits` returning a [`PrivateWire`]
    /// holding the result.
    ///
    /// # Panics
    ///
    /// If the `num_bits` specified in the fn params is odd.
    pub fn append_logic_and(
        &mut self,
        a: PrivateWire,
        b: PrivateWire,
        num_bits: usize,
    ) -> PrivateWire {
        self.append_logic_component(a, b, num_bits, false)
    }

    /// Adds a logical XOR gate that performs the XOR between two values for the
    /// specified first `num_bits` returning a [`PrivateWire`] holding the
    /// result.
    ///
    /// # Panics
    ///
    /// If the `num_bits` specified in the fn params is odd.
    pub fn append_logic_xor(
        &mut self,
        a: PrivateWire,
        b: PrivateWire,
        num_bits: usize,
    ) -> PrivateWire {
        self.append_logic_component(a, b, num_bits, true)
    }

    /// Constrain `a` to be equal to `constant + pi`.
    ///
    /// `constant` will be defined as part of the public circuit description.
    pub fn assert_equal_constant<C: Into<P::ScalarField>>(
        &mut self,
        a: PrivateWire,
        constant: C,
        public: Option<P::ScalarField>,
    ) {
        let constant = constant.into();
        let constraint = Constraint::default().left(1).constant(-constant).a(a);
        let constraint =
            public.map(|p| constraint.public(p)).unwrap_or(constraint);

        self.append_gate(constraint);
    }

    /// Asserts `a == b` by appending two gates
    pub fn assert_equal_point(&mut self, a: WitnessPoint, b: WitnessPoint) {
        self.assert_equal(*a.x(), *b.x());
        self.assert_equal(*b.y(), *b.y());
    }

    /// Asserts `point == public`.
    ///
    /// Will add `public` affine coordinates `(x,y)` as public inputs
    pub fn assert_equal_public_point<A: Into<P::JubjubAffine>>(
        &mut self,
        point: WitnessPoint,
        public: A,
    ) {
        let public = public.into();

        self.assert_equal_constant(
            *point.x(),
            P::ScalarField::zero(),
            Some(<<<P as zkstd::behave::Pairing>::JubjubAffine as CurveGroup>::Range>::into(-public.get_x())),
        );

        self.assert_equal_constant(
            *point.y(),
            P::ScalarField::zero(),
            Some(<<<P as zkstd::behave::Pairing>::JubjubAffine as CurveGroup>::Range>::into(-public.get_y())),
        );
    }

    /// Adds two curve points by consuming 2 gates.
    pub fn component_add_point(
        &mut self,
        a: WitnessPoint,
        b: WitnessPoint,
    ) -> WitnessPoint {
        // In order to verify that two points were correctly added
        // without going over a degree 4 polynomial, we will need
        // x_1, y_1, x_2, y_2
        // x_3, y_3, x_1 * y_2

        let x_1 = *a.x();
        let y_1 = *a.y();
        let x_2 = *b.x();
        let y_2 = *b.y();

        let p1 = P::JubjubAffine::from_raw_unchecked(
            self[x_1].into(),
            self[y_1].into(),
        );
        let p2 = P::JubjubAffine::from_raw_unchecked(
            self[x_2].into(),
            self[y_2].into(),
        );

        let point = P::JubjubAffine::from(p1 + p2);

        let x_3: P::ScalarField = point.get_x().into();
        let y_3: P::ScalarField = point.get_y().into();

        let x1_y2 = self[x_1] * self[y_2];

        let x_1_y_2 = self.append_witness(x1_y2);
        let x_3 = self.append_witness(x_3);
        let y_3 = self.append_witness(y_3);

        // Add the rest of the prepared points into the composer
        let constraint = Constraint::default().a(x_1).b(y_1).o(x_2).d(y_2);
        let constraint = Constraint::group_add_curve_addtion(constraint);

        self.append_custom_gate(constraint);

        let constraint = Constraint::default().a(x_3).b(y_3).d(x_1_y_2);

        self.append_custom_gate(constraint);

        WitnessPoint::new(x_3, y_3)
    }

    /// Adds a boolean constraint (also known as binary constraint) where the
    /// gate eq. will enforce that the [`PrivateWire`] received is either `0` or
    /// `1` by adding a constraint in the circuit.
    ///
    /// Note that using this constraint with whatever [`PrivateWire`] that
    /// is not representing a value equalling 0 or 1, will always force the
    /// equation to fail.
    pub fn component_boolean(&mut self, a: PrivateWire) {
        let zero = Self::ZERO;
        let constraint = Constraint::default()
            .mult(1)
            .output(-P::ScalarField::one())
            .a(a)
            .b(a)
            .o(a)
            .d(zero);

        self.append_gate(constraint);
    }

    /// Decomposes `scalar` into an array truncated to `N` bits (max 256).
    ///
    /// Asserts the reconstruction of the bits to be equal to `scalar`.
    ///
    /// Consume `2 · N + 1` gates
    pub fn component_decomposition<const N: usize>(
        &mut self,
        scalar: PrivateWire,
    ) -> [PrivateWire; N] {
        // Static assertion
        assert!(0 < N && N <= 256);

        let mut decomposition = [Self::ZERO; N];

        let acc = Self::ZERO;
        let acc = self[scalar]
            .to_bits()
            .iter()
            .rev()
            .enumerate()
            .zip(decomposition.iter_mut())
            .fold(acc, |acc, ((i, w), d)| {
                *d = self.append_witness(P::ScalarField::from(*w as u64));

                self.component_boolean(*d);

                let constraint = Constraint::default()
                    .left(P::ScalarField::pow_of_2(i as u64))
                    .right(1)
                    .a(*d)
                    .b(acc);

                self.gate_add(constraint)
            });

        self.assert_equal(acc, scalar);

        decomposition
    }

    /// Conditionally selects identity as [`WitnessPoint`] based on an input
    /// bit.
    ///
    /// bit == 1 => a,
    /// bit == 0 => identity,
    ///
    /// `bit` is expected to be constrained by
    /// [`Composer::component_boolean`]
    pub fn component_select_identity(
        &mut self,
        bit: PrivateWire,
        a: WitnessPoint,
    ) -> WitnessPoint {
        let x = self.component_select_zero(bit, *a.x());
        let y = self.component_select_one(bit, *a.y());

        WitnessPoint::new(x, y)
    }

    /// Evaluate `jubjub · point` as a [`WitnessPoint`]
    pub fn component_mul_point(
        &mut self,
        jubjub: PrivateWire,
        point: WitnessPoint,
    ) -> WitnessPoint {
        // Turn scalar into bits
        let scalar_bits = self.component_decomposition::<252>(jubjub);

        let mut result = Self::IDENTITY;

        for bit in scalar_bits.iter().rev() {
            result = self.component_add_point(result, result);

            let point_to_add = self.component_select_identity(*bit, point);
            result = self.component_add_point(result, point_to_add);
        }

        result
    }

    /// Conditionally selects a [`PrivateWire`] based on an input bit.
    ///
    /// bit == 1 => a,
    /// bit == 0 => b,
    ///
    /// `bit` is expected to be constrained by
    /// [`Composer::component_boolean`]
    pub fn component_select(
        &mut self,
        bit: PrivateWire,
        a: PrivateWire,
        b: PrivateWire,
    ) -> PrivateWire {
        // bit * a
        let constraint = Constraint::default().mult(1).a(bit).b(a);
        let bit_times_a = self.gate_mul(constraint);

        // 1 - bit
        let constraint = Constraint::default()
            .left(-P::ScalarField::one())
            .constant(1)
            .a(bit);
        let one_min_bit = self.gate_add(constraint);

        // (1 - bit) * b
        let constraint = Constraint::default().mult(1).a(one_min_bit).b(b);
        let one_min_bit_b = self.gate_mul(constraint);

        // [ (1 - bit) * b ] + [ bit * a ]
        let constraint = Constraint::default()
            .left(1)
            .right(1)
            .a(one_min_bit_b)
            .b(bit_times_a);
        self.gate_add(constraint)
    }

    /// Conditionally selects a [`PrivateWire`] based on an input bit.
    ///
    /// bit == 1 => value,
    /// bit == 0 => 1,
    ///
    /// `bit` is expected to be constrained by
    /// [`Composer::component_boolean`]
    pub fn component_select_one(
        &mut self,
        bit: PrivateWire,
        value: PrivateWire,
    ) -> PrivateWire {
        let b = self[bit];
        let v = self[value];

        let f_x = P::ScalarField::one() - b + (b * v);
        let f_x = self.append_witness(f_x);

        let constraint = Constraint::default()
            .mult(1)
            .left(-P::ScalarField::one())
            .output(-P::ScalarField::one())
            .constant(1)
            .a(bit)
            .b(value)
            .o(f_x);

        self.append_gate(constraint);

        f_x
    }

    /// Conditionally selects a [`WitnessPoint`] based on an input bit.
    ///
    /// bit == 1 => a,
    /// bit == 0 => b,
    ///
    /// `bit` is expected to be constrained by
    /// [`Composer::component_boolean`]
    pub fn component_select_point(
        &mut self,
        bit: PrivateWire,
        a: WitnessPoint,
        b: WitnessPoint,
    ) -> WitnessPoint {
        let x = self.component_select(bit, *a.x(), *b.x());
        let y = self.component_select(bit, *a.y(), *b.y());

        WitnessPoint::new(x, y)
    }

    /// Conditionally selects a [`PrivateWire`] based on an input bit.
    ///
    /// bit == 1 => value,
    /// bit == 0 => 0,
    ///
    /// `bit` is expected to be constrained by
    /// [`Composer::component_boolean`]
    pub fn component_select_zero(
        &mut self,
        bit: PrivateWire,
        value: PrivateWire,
    ) -> PrivateWire {
        let constraint = Constraint::default().mult(1).a(bit).b(value);

        self.gate_mul(constraint)
    }

    /// Adds a range-constraint gate that checks and constrains a
    /// [`PrivateWire`] to be inside of the range \[0,num_bits\].
    ///
    /// This function adds `num_bits/4` gates to the circuit description in
    /// order to add the range constraint.
    ///
    ///# Panics
    /// This function will panic if the num_bits specified is not even, ie.
    /// `num_bits % 2 != 0`.
    pub fn component_range(&mut self, witness: PrivateWire, num_bits: usize) {
        // convert witness to bit representation and reverse
        let bits = self[witness];
        let bit_iter = BitIterator8::new(bits.to_bytes());
        let mut bits: Vec<_> = bit_iter.collect();
        bits.reverse();

        // considering this is a width-4 program, one gate will contain 4
        // accumulators. each accumulator proves that a single quad is a
        // base-4 digit. accumulators are bijective to quads, and these
        // are 2-bits each. given that, one gate accumulates 8 bits.
        let mut num_gates = num_bits >> 3;

        // given each gate accumulates 8 bits, its count must be padded
        if num_bits % 8 != 0 {
            num_gates += 1;
        }

        // a gate holds 4 quads
        let num_quads = num_gates * 4;

        // the wires are left-padded with the difference between the quads count
        // and the bits argument
        let pad = 1 + (((num_quads << 1) - num_bits) >> 1);

        // last gate is reserved for either the genesis quad or the padding
        let used_gates = num_gates + 1;

        let base = Constraint::<P::ScalarField>::default();
        let base = Constraint::range(base);
        let mut constraints = vec![base; used_gates];

        // We collect the set of accumulators to return back to the user
        // and keep a running count of the current accumulator
        let mut accumulators: Vec<PrivateWire> = Vec::new();
        let mut accumulator = P::ScalarField::zero();
        let four = P::ScalarField::from(4);

        for i in pad..=num_quads {
            // convert each pair of bits to quads
            let bit_index = (num_quads - i) << 1;
            let q_0 = bits[bit_index] as u64;
            let q_1 = bits[bit_index + 1] as u64;
            let quad = q_0 + (2 * q_1);

            accumulator = four * accumulator;
            accumulator += P::ScalarField::from(quad);

            let accumulator_var = self.append_witness(accumulator);

            accumulators.push(accumulator_var);

            let idx = i / 4;
            match i % 4 {
                0 => {
                    constraints[idx].w_d = accumulator_var;
                }
                1 => {
                    constraints[idx].w_o = accumulator_var;
                }
                2 => {
                    constraints[idx].w_b = accumulator_var;
                }
                3 => {
                    constraints[idx].w_a = accumulator_var;
                }
                _ => unreachable!(),
            };
        }

        // last constraint is zeroed as it is reserved for the genesis quad or
        // padding
        if let Some(c) = constraints.last_mut() {
            *c = Constraint::default()
        }

        // the accumulators count is a function to the number of quads. hence,
        // this optional gate will not cause different circuits depending on the
        // witness because this computation is bound to the constant bits count
        // alone.
        if let Some(accumulator) = accumulators.last() {
            if let Some(c) = constraints.last_mut() {
                c.w_d = *accumulator
            }
        }

        constraints
            .into_iter()
            .for_each(|c| self.append_custom_gate(c));

        // the accumulators count is a function to the number of quads. hence,
        // this optional gate will not cause different circuits depending on the
        // witness because this computation is bound to the constant bits count
        // alone.
        if let Some(accumulator) = accumulators.last() {
            self.assert_equal(*accumulator, witness);
        }
    }

    /// Evaluate and return `o` by appending a new constraint into the circuit.
    ///
    /// Set `q_o = (-1)` and override the output of the constraint with:
    /// `o := q_l · a + q_r · b + q_4 · d + q_c + PI`
    pub fn gate_add(&mut self, s: Constraint<P::ScalarField>) -> PrivateWire {
        let s = Constraint::arithmetic(s).output(-P::ScalarField::one());

        let o = self
            .append_evaluated_output(s)
            .expect("output selector is -1");
        let s = s.o(o);

        self.append_gate(s);

        o
    }

    /// Evaluate and return `o` by appending a new constraint into the circuit.
    ///
    /// Set `q_o = (-1)` and override the output of the constraint with:
    /// `o := q_m · a · b + q_4 · d + q_c + PI`
    pub fn gate_mul(&mut self, s: Constraint<P::ScalarField>) -> PrivateWire {
        let s = Constraint::arithmetic(s).output(-P::ScalarField::one());

        let o = self
            .append_evaluated_output(s)
            .expect("output selector is -1");
        let s = s.o(o);

        self.append_gate(s);

        o
    }

    /// Prove a circuit with a builder initialized with `constraints` capacity.
    pub(crate) fn prove<C>(
        constraints: usize,
        circuit: &C,
    ) -> Result<Self, Error>
    where
        C: Circuit<P>,
    {
        let mut builder = Self::initialized(constraints);

        circuit.synthesize(&mut builder)?;

        Ok(builder)
    }
}
