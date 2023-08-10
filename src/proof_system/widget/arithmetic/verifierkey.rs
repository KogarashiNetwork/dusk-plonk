// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use poly_commit::Commitment;
use zkstd::common::Pairing;

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct VerifierKey<P: Pairing> {
    pub q_m: Commitment<P::G1Affine>,
    pub q_l: Commitment<P::G1Affine>,
    pub q_r: Commitment<P::G1Affine>,
    pub q_o: Commitment<P::G1Affine>,
    pub q_4: Commitment<P::G1Affine>,
    pub q_c: Commitment<P::G1Affine>,
    pub q_arith: Commitment<P::G1Affine>,
}

mod alloc {
    use super::*;
    use crate::proof_system::linearization_poly::ProofEvaluations;
    #[rustfmt::skip]
    use ::alloc::vec::Vec;

    impl<P: Pairing> VerifierKey<P> {
        pub(crate) fn compute_linearization_commitment(
            &self,
            scalars: &mut Vec<P::ScalarField>,
            points: &mut Vec<P::G1Affine>,
            evaluations: &ProofEvaluations<P>,
        ) {
            let q_arith_eval = evaluations.q_arith_eval;

            scalars
                .push(evaluations.a_eval * evaluations.b_eval * q_arith_eval);
            points.push(self.q_m.0);

            scalars.push(evaluations.a_eval * q_arith_eval);
            points.push(self.q_l.0);

            scalars.push(evaluations.b_eval * q_arith_eval);
            points.push(self.q_r.0);

            scalars.push(evaluations.c_eval * q_arith_eval);
            points.push(self.q_o.0);

            scalars.push(evaluations.d_eval * q_arith_eval);
            points.push(self.q_4.0);

            scalars.push(q_arith_eval);
            points.push(self.q_c.0);
        }
    }
}
