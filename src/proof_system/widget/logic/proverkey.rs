// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use crate::fft::Evaluations;
use zero_crypto::behave::Ring;
use zero_crypto::common::{Pairing, PrimeField};
use zero_kzg::Polynomial as ZeroPoly;

#[derive(Debug, Eq, PartialEq, Clone)]
pub(crate) struct ProverKey<P: Pairing> {
    pub(crate) q_c: (ZeroPoly<P::ScalarField>, Evaluations<P>),
    pub(crate) q_logic: (ZeroPoly<P::ScalarField>, Evaluations<P>),
}

impl<P: Pairing> ProverKey<P> {
    pub(crate) fn compute_quotient_i(
        &self,
        index: usize,
        logic_separation_challenge: &P::ScalarField,
        a_w_i: &P::ScalarField,
        a_w_i_next: &P::ScalarField,
        b_w_i: &P::ScalarField,
        b_w_i_next: &P::ScalarField,
        c_w_i: &P::ScalarField,
        d_w_i: &P::ScalarField,
        d_w_i_next: &P::ScalarField,
    ) -> P::ScalarField {
        let four = P::ScalarField::from(4);

        let q_logic_i = &self.q_logic.1[index];
        let q_c_i = &self.q_c.1[index];

        let kappa = logic_separation_challenge.square();
        let kappa_sq = kappa.square();
        let kappa_cu = kappa_sq * kappa;
        let kappa_qu = kappa_cu * kappa;

        let a = *a_w_i_next - four * a_w_i;
        let c_0 = delta::<P>(a);

        let b = *b_w_i_next - four * b_w_i;
        let c_1 = delta::<P>(b) * kappa;

        let d = *d_w_i_next - four * d_w_i;
        let c_2 = delta::<P>(d) * kappa_sq;

        let w = c_w_i;
        let c_3 = (*w - a * b) * kappa_cu;

        let c_4 = delta_xor_and::<P>(&a, &b, w, &d, q_c_i) * kappa_qu;

        *q_logic_i * (c_3 + c_0 + c_1 + c_2 + c_4) * logic_separation_challenge
    }

    pub(crate) fn compute_linearization(
        &self,
        logic_separation_challenge: &P::ScalarField,
        a_eval: &P::ScalarField,
        a_next_eval: &P::ScalarField,
        b_eval: &P::ScalarField,
        b_next_eval: &P::ScalarField,
        c_eval: &P::ScalarField,
        d_eval: &P::ScalarField,
        d_next_eval: &P::ScalarField,
        q_c_eval: &P::ScalarField,
    ) -> ZeroPoly<P::ScalarField> {
        let four = P::ScalarField::from(4);
        let q_logic_poly = &self.q_logic.0;

        let kappa = logic_separation_challenge.square();
        let kappa_sq = kappa.square();
        let kappa_cu = kappa_sq * kappa;
        let kappa_qu = kappa_cu * kappa;

        let a = *a_next_eval - four * a_eval;
        let c_0 = delta::<P>(a);

        let b = *b_next_eval - four * b_eval;
        let c_1 = delta::<P>(b) * kappa;

        let d = *d_next_eval - four * d_eval;
        let c_2 = delta::<P>(d) * kappa_sq;

        let w = c_eval;
        let c_3 = (*w - a * b) * kappa_cu;

        let c_4 = delta_xor_and::<P>(&a, &b, w, &d, q_c_eval) * kappa_qu;

        let t = (c_0 + c_1 + c_2 + c_3 + c_4) * logic_separation_challenge;

        q_logic_poly * &t
    }
}

// Computes f(f-1)(f-2)(f-3)
pub(crate) fn delta<P: Pairing>(f: P::ScalarField) -> P::ScalarField {
    let f_1 = f - P::ScalarField::one();
    let f_2 = f - P::ScalarField::from(2);
    let f_3 = f - P::ScalarField::from(3);
    f * f_1 * f_2 * f_3
}

// The identity we want to check is q_logic * A = 0
// A = B + E
// B = q_c * [9c - 3(a+b)]
// E = 3(a+b+c) - 2F
// F = w[w(4w - 18(a+b) + 81) + 18(a^2 + b^2) - 81(a+b) + 83]
#[allow(non_snake_case)]
pub(crate) fn delta_xor_and<P: Pairing>(
    a: &P::ScalarField,
    b: &P::ScalarField,
    w: &P::ScalarField,
    c: &P::ScalarField,
    q_c: &P::ScalarField,
) -> P::ScalarField {
    let nine = P::ScalarField::from(9);
    let two = P::ScalarField::from(2);
    let three = P::ScalarField::from(3);
    let four = P::ScalarField::from(4);
    let eighteen = P::ScalarField::from(18);
    let eighty_one = P::ScalarField::from(81);
    let eighty_three = P::ScalarField::from(83);

    let F = *w
        * (*w * (four * w - eighteen * (*a + b) + eighty_one)
            + eighteen * (a.square() + b.square())
            - eighty_one * (*a + b)
            + eighty_three);
    let E = three * (*a + b + c) - (two * F);
    let B = *q_c * ((nine * c) - three * (*a + b));
    B + E
}
