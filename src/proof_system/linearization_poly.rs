// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use crate::proof_system::ProvingKey;

use poly_commit::Polynomial;
use zksnarks::Evaluations as ProofEvaluations;
use zkstd::common::Pairing;

/// Evaluations at points `z` or and `z * root of unity`
#[allow(dead_code)]
pub(crate) struct Evaluations<P: Pairing> {
    pub(crate) proof: ProofEvaluations<P::ScalarField>,
    // Evaluation of the linearization sigma polynomial at `z`
    pub(crate) t_eval: P::ScalarField,
}

/// Compute the linearization polynomial.
// TODO: Improve the method signature
#[allow(clippy::type_complexity)]
pub(crate) fn compute<P: Pairing>(
    group_generator: P::ScalarField,
    prover_key: &ProvingKey<P>,
    (
        alpha,
        beta,
        gamma,
        range_separation_challenge,
        logic_separation_challenge,
        fixed_base_separation_challenge,
        var_base_separation_challenge,
        z_challenge,
    ): &(
        P::ScalarField,
        P::ScalarField,
        P::ScalarField,
        P::ScalarField,
        P::ScalarField,
        P::ScalarField,
        P::ScalarField,
        P::ScalarField,
    ),
    a_w_poly: &Polynomial<P::ScalarField>,
    b_w_poly: &Polynomial<P::ScalarField>,
    c_w_poly: &Polynomial<P::ScalarField>,
    d_w_poly: &Polynomial<P::ScalarField>,
    t_x_poly: &Polynomial<P::ScalarField>,
    z_poly: &Polynomial<P::ScalarField>,
) -> (Polynomial<P::ScalarField>, Evaluations<P>) {
    // Compute evaluations
    let t_eval = t_x_poly.evaluate(z_challenge);
    let a_eval = a_w_poly.evaluate(z_challenge);
    let b_eval = b_w_poly.evaluate(z_challenge);
    let c_eval = c_w_poly.evaluate(z_challenge);
    let d_eval = d_w_poly.evaluate(z_challenge);

    let s_sigma_1_eval =
        prover_key.permutation.s_sigma_1.0.evaluate(z_challenge);
    let s_sigma_2_eval =
        prover_key.permutation.s_sigma_2.0.evaluate(z_challenge);
    let s_sigma_3_eval =
        prover_key.permutation.s_sigma_3.0.evaluate(z_challenge);

    let q_arith_eval = prover_key.arithmetic.q_arith.0.evaluate(z_challenge);
    let q_c_eval = prover_key.logic.q_c.0.evaluate(z_challenge);
    let q_l_eval = prover_key.fixed_base.q_l.0.evaluate(z_challenge);
    let q_r_eval = prover_key.fixed_base.q_r.0.evaluate(z_challenge);

    let a_next_eval = a_w_poly.evaluate(&(*z_challenge * group_generator));
    let b_next_eval = b_w_poly.evaluate(&(*z_challenge * group_generator));
    let d_next_eval = d_w_poly.evaluate(&(*z_challenge * group_generator));
    let perm_eval = z_poly.evaluate(&(*z_challenge * group_generator));

    let f_1 = compute_circuit_satisfiability(
        (
            range_separation_challenge,
            logic_separation_challenge,
            fixed_base_separation_challenge,
            var_base_separation_challenge,
        ),
        &a_eval,
        &b_eval,
        &c_eval,
        &d_eval,
        &a_next_eval,
        &b_next_eval,
        &d_next_eval,
        &q_arith_eval,
        &q_c_eval,
        &q_l_eval,
        &q_r_eval,
        prover_key,
    );

    let f_2 = prover_key.permutation.compute_linearization(
        z_challenge,
        (alpha, beta, gamma),
        (&a_eval, &b_eval, &c_eval, &d_eval),
        (&s_sigma_1_eval, &s_sigma_2_eval, &s_sigma_3_eval),
        &perm_eval,
        z_poly,
    );

    let r_poly = f_1 + f_2;

    // Evaluate linearization polynomial at challenge `z`
    let r_poly_eval = r_poly.evaluate(z_challenge);

    (
        r_poly,
        Evaluations {
            proof: ProofEvaluations {
                a_eval,
                b_eval,
                c_eval,
                d_eval,
                a_next_eval,
                b_next_eval,
                d_next_eval,
                q_arith_eval,
                q_c_eval,
                q_l_eval,
                q_r_eval,
                s_sigma_1_eval,
                s_sigma_2_eval,
                s_sigma_3_eval,
                r_poly_eval,
                perm_eval,
            },
            t_eval,
        },
    )
}

fn compute_circuit_satisfiability<P: Pairing>(
    (
        range_separation_challenge,
        logic_separation_challenge,
        fixed_base_separation_challenge,
        var_base_separation_challenge,
    ): (
        &P::ScalarField,
        &P::ScalarField,
        &P::ScalarField,
        &P::ScalarField,
    ),
    a_eval: &P::ScalarField,
    b_eval: &P::ScalarField,
    c_eval: &P::ScalarField,
    d_eval: &P::ScalarField,
    a_next_eval: &P::ScalarField,
    b_next_eval: &P::ScalarField,
    d_next_eval: &P::ScalarField,
    q_arith_eval: &P::ScalarField,
    q_c_eval: &P::ScalarField,
    q_l_eval: &P::ScalarField,
    q_r_eval: &P::ScalarField,
    prover_key: &ProvingKey<P>,
) -> Polynomial<P::ScalarField> {
    let a = prover_key.arithmetic.linearize(
        a_eval,
        b_eval,
        c_eval,
        d_eval,
        q_arith_eval,
    );

    let b = prover_key.range.compute_linearization(
        range_separation_challenge,
        a_eval,
        b_eval,
        c_eval,
        d_eval,
        d_next_eval,
    );

    let c = prover_key.logic.compute_linearization(
        logic_separation_challenge,
        a_eval,
        a_next_eval,
        b_eval,
        b_next_eval,
        c_eval,
        d_eval,
        d_next_eval,
        q_c_eval,
    );

    let d = prover_key.fixed_base.compute_linearization(
        fixed_base_separation_challenge,
        a_eval,
        a_next_eval,
        b_eval,
        b_next_eval,
        c_eval,
        d_eval,
        d_next_eval,
        q_l_eval,
        q_r_eval,
        q_c_eval,
    );

    let e = prover_key.variable_base.linearize(
        var_base_separation_challenge,
        a_eval,
        a_next_eval,
        b_eval,
        b_next_eval,
        c_eval,
        d_eval,
        d_next_eval,
    );

    let mut linearization_poly = a + b;
    // TODO FIX
    // linearization_poly += &c;
    // linearization_poly += &d;
    // linearization_poly += &e;
    linearization_poly = linearization_poly + c;
    linearization_poly = linearization_poly + d;
    linearization_poly = linearization_poly + e;

    linearization_poly
}
