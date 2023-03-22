// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct VerifierKey<P: Pairing> {
    pub(crate) q_c: Commitment<P>,
    pub(crate) q_logic: Commitment<P>,
}

use crate::proof_system::linearization_poly::ProofEvaluations;
use crate::proof_system::widget::logic::proverkey::{delta, delta_xor_and};
#[rustfmt::skip]
    use ::alloc::vec::Vec;
use zero_crypto::behave::PrimeField;
use zero_crypto::common::Pairing;
use zero_kzg::Commitment;

impl<P: Pairing> VerifierKey<P> {
    pub(crate) fn compute_linearization_commitment(
        &self,
        logic_separation_challenge: &P::ScalarField,
        scalars: &mut Vec<P::ScalarField>,
        points: &mut Vec<P::G1Affine>,
        evaluations: &ProofEvaluations<P>,
    ) {
        let four = P::ScalarField::from(4);

        let kappa = logic_separation_challenge.square();
        let kappa_sq = kappa.square();
        let kappa_cu = kappa_sq * kappa;
        let kappa_qu = kappa_cu * kappa;

        let a = evaluations.a_next_eval - four * evaluations.a_eval;
        let c_0 = delta::<P>(a);

        let b = evaluations.b_next_eval - four * evaluations.b_eval;
        let c_1 = delta::<P>(b) * kappa;

        let d = evaluations.d_next_eval - four * evaluations.d_eval;
        let c_2 = delta::<P>(d) * kappa_sq;

        let w = evaluations.c_eval;
        let c_3 = (w - a * b) * kappa_cu;

        let c_4 = delta_xor_and::<P>(&a, &b, &w, &d, &evaluations.q_c_eval)
            * kappa_qu;
        scalars
            .push((c_0 + c_1 + c_2 + c_3 + c_4) * logic_separation_challenge);
        points.push(self.q_logic.0);
    }
}
