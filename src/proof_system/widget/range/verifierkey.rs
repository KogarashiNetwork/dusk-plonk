// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct VerifierKey<P: Pairing> {
    pub(crate) q_range: Commitment<P::G1Affine>,
}

use crate::proof_system::widget::range::proverkey::delta;
use zksnarks::Evaluations as ProofEvaluations;
#[rustfmt::skip]
    use ::alloc::vec::Vec;
use poly_commit::Commitment;
use zkstd::{behave::PrimeField, common::Pairing};

impl<P: Pairing> VerifierKey<P> {
    pub(crate) fn compute_linearization_commitment(
        &self,
        range_separation_challenge: &P::ScalarField,
        scalars: &mut Vec<P::ScalarField>,
        points: &mut Vec<P::G1Affine>,
        evaluations: &ProofEvaluations<P::ScalarField>,
    ) {
        let four = P::ScalarField::from(4);

        let kappa = range_separation_challenge.square();
        let kappa_sq = kappa.square();
        let kappa_cu = kappa_sq * kappa;

        let b_1 = delta::<P>(evaluations.c_eval - (four * evaluations.d_eval));
        let b_2 =
            delta::<P>(evaluations.b_eval - four * evaluations.c_eval) * kappa;
        let b_3 = delta::<P>(evaluations.a_eval - four * evaluations.b_eval)
            * kappa_sq;
        let b_4 =
            delta::<P>(evaluations.d_next_eval - (four * evaluations.a_eval))
                * kappa_cu;

        scalars.push((b_1 + b_2 + b_3 + b_4) * range_separation_challenge);
        points.push(self.q_range.0);
    }
}
