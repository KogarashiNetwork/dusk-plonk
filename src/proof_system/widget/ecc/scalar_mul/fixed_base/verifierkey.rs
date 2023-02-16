// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct VerifierKey<P: Pairing> {
    pub(crate) q_l: Commitment<P>,
    pub(crate) q_r: Commitment<P>,
    pub(crate) q_fixed_group_add: Commitment<P>,
}

use crate::proof_system::linearization_poly::ProofEvaluations;
use crate::proof_system::widget::ecc::scalar_mul::fixed_base::proverkey::{
    check_bit_consistency, extract_bit,
};
#[rustfmt::skip]
    use ::alloc::vec::Vec;
use zero_crypto::behave::FftField;
use zero_crypto::behave::PrimeField;
use zero_crypto::behave::Ring;
use zero_crypto::common::Pairing;
use zero_kzg::Commitment;

impl<P: Pairing> VerifierKey<P> {
    pub(crate) fn compute_linearization_commitment(
        &self,
        ecc_separation_challenge: &P::ScalarField,
        scalars: &mut Vec<P::ScalarField>,
        points: &mut Vec<P::G1Affine>,
        evaluations: &ProofEvaluations<P>,
    ) {
        let kappa = ecc_separation_challenge.square();
        let kappa_sq = kappa.square();
        let kappa_cu = kappa_sq * kappa;

        let x_beta_poly = evaluations.q_l_eval;
        let y_beta_eval = evaluations.q_r_eval;

        let acc_x = evaluations.a_eval;
        let acc_x_next = evaluations.a_next_eval;
        let acc_y = evaluations.b_eval;
        let acc_y_next = evaluations.b_next_eval;

        let xy_alpha = evaluations.c_eval;

        let accumulated_bit = evaluations.d_eval;
        let accumulated_bit_next = evaluations.d_next_eval;
        let bit = extract_bit::<P>(&accumulated_bit, &accumulated_bit_next);

        // Check bit consistency
        let bit_consistency = check_bit_consistency::<P>(bit);

        let y_alpha = (bit.square() * (y_beta_eval - P::ScalarField::one()))
            + P::ScalarField::one();

        let x_alpha = x_beta_poly * bit;

        // xy_alpha consistency check
        let xy_consistency = ((bit * evaluations.q_c_eval) - xy_alpha) * kappa;

        // x accumulator consistency check
        let x_3 = acc_x_next;
        let lhs =
            x_3 + (x_3 * xy_alpha * acc_x * acc_y * P::ScalarField::EDWARDS_D);
        let rhs = (x_alpha * acc_y) + (y_alpha * acc_x);
        let x_acc_consistency = (lhs - rhs) * kappa_sq;

        // y accumulator consistency check
        let y_3 = acc_y_next;
        let lhs =
            y_3 - (y_3 * xy_alpha * acc_x * acc_y * P::ScalarField::EDWARDS_D);
        let rhs = (x_alpha * acc_x) + (y_alpha * acc_y);
        let y_acc_consistency = (lhs - rhs) * kappa_cu;

        let a = bit_consistency
            + x_acc_consistency
            + y_acc_consistency
            + xy_consistency;

        scalars.push(a * ecc_separation_challenge);
        points.push(self.q_fixed_group_add.0);
    }
}
