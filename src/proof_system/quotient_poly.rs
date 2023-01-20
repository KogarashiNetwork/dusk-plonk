// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use crate::{error::Error, fft::Polynomial, proof_system::ProverKey};
#[cfg(feature = "std")]
use rayon::prelude::*;
use sp_std::vec;
use sp_std::vec::Vec;
use zero_bls12_381::Fr as BlsScalar;
use zero_crypto::behave::*;
use zero_kzg::{Fft, Polynomial as ZeroPoly};

/// Computes the Quotient [`Polynomial`] given the [`EvaluationDomain`], a
/// [`ProverKey`] and some other info.
pub(crate) fn compute(
    fft: &Fft<BlsScalar>,
    prover_key: &ProverKey,
    z_poly: &Polynomial,
    (a_w_poly, b_w_poly, c_w_poly, d_w_poly): (
        &Polynomial,
        &Polynomial,
        &Polynomial,
        &Polynomial,
    ),
    public_inputs_poly: &Polynomial,
    (
        alpha,
        beta,
        gamma,
        range_challenge,
        logic_challenge,
        fixed_base_challenge,
        var_base_challenge,
    ): &(
        BlsScalar,
        BlsScalar,
        BlsScalar,
        BlsScalar,
        BlsScalar,
        BlsScalar,
        BlsScalar,
    ),
) -> Result<Polynomial, Error> {
    // Compute 8n evals
    let n = (8 * fft.size()).next_power_of_two();
    let k = n.trailing_zeros();
    let fft_8n = Fft::<BlsScalar>::new(k as usize);

    let mut z_poly = ZeroPoly::new(z_poly.coeffs.clone());
    let mut a_w_poly = ZeroPoly::new(a_w_poly.coeffs.clone());
    let mut b_w_poly = ZeroPoly::new(b_w_poly.coeffs.clone());
    let mut c_w_poly = ZeroPoly::new(c_w_poly.coeffs.clone());
    let mut d_w_poly = ZeroPoly::new(d_w_poly.coeffs.clone());

    fft_8n.coset_dft(&mut z_poly);

    fft_8n.coset_dft(&mut a_w_poly);
    fft_8n.coset_dft(&mut b_w_poly);
    fft_8n.coset_dft(&mut c_w_poly);
    fft_8n.coset_dft(&mut d_w_poly);

    for i in 0..8 {
        z_poly.0.push(z_poly.0[i]);
        a_w_poly.0.push(a_w_poly.0[i]);
        b_w_poly.0.push(b_w_poly.0[i]);
        // c_w_eval_8n push not required
        d_w_poly.0.push(d_w_poly.0[i]);
    }

    let z_eval_8n = Polynomial::from_coefficients_vec(z_poly.0);
    let a_w_eval_8n = Polynomial::from_coefficients_vec(a_w_poly.0);
    let b_w_eval_8n = Polynomial::from_coefficients_vec(b_w_poly.0);
    let c_w_eval_8n = Polynomial::from_coefficients_vec(c_w_poly.0);
    let d_w_eval_8n = Polynomial::from_coefficients_vec(d_w_poly.0);

    let t_1 = compute_circuit_satisfiability_equation(
        &fft_8n,
        (
            range_challenge,
            logic_challenge,
            fixed_base_challenge,
            var_base_challenge,
        ),
        prover_key,
        (&a_w_eval_8n, &b_w_eval_8n, &c_w_eval_8n, &d_w_eval_8n),
        public_inputs_poly,
    );

    let t_2 = compute_permutation_checks(
        fft,
        &fft_8n,
        prover_key,
        (&a_w_eval_8n, &b_w_eval_8n, &c_w_eval_8n, &d_w_eval_8n),
        &z_eval_8n,
        (alpha, beta, gamma),
    );

    let range = (0..fft_8n.size()).into_iter();

    let quotient: Vec<_> = range
        .map(|i| {
            let numerator = t_1[i] + t_2[i];
            let denominator = prover_key.v_h_coset_8n()[i];
            numerator * denominator.invert().unwrap()
        })
        .collect();
    let mut quotient = ZeroPoly::new(quotient);
    fft_8n.coset_idft(&mut quotient);

    Ok(Polynomial::from_coefficients_vec(quotient.0))
}

// Ensures that the circuit is satisfied
// Ensures that the circuit is satisfied
fn compute_circuit_satisfiability_equation(
    fft: &Fft<BlsScalar>,
    (
        range_challenge,
        logic_challenge,
        fixed_base_challenge,
        var_base_challenge,
    ): (&BlsScalar, &BlsScalar, &BlsScalar, &BlsScalar),
    prover_key: &ProverKey,
    (a_w_eval_8n, b_w_eval_8n, c_w_eval_8n, d_w_eval_8n): (
        &[BlsScalar],
        &[BlsScalar],
        &[BlsScalar],
        &[BlsScalar],
    ),
    pi_poly: &Polynomial,
) -> Vec<BlsScalar> {
    let mut pi_poly = ZeroPoly::new(pi_poly.coeffs.clone());
    fft.coset_dft(&mut pi_poly);
    let public_eval_8n = pi_poly.0;

    #[cfg(not(feature = "std"))]
    let range = (0..fft.size()).into_iter();

    #[cfg(feature = "std")]
    let range = (0..fft.size()).into_par_iter();

    let t: Vec<_> = range
        .map(|i| {
            let a_w = &a_w_eval_8n[i];
            let b_w = &b_w_eval_8n[i];
            let c_w = &c_w_eval_8n[i];
            let d_w = &d_w_eval_8n[i];
            let a_w_next = &a_w_eval_8n[i + 8];
            let b_w_next = &b_w_eval_8n[i + 8];
            let d_w_next = &d_w_eval_8n[i + 8];
            let pi = &public_eval_8n[i];

            let a = prover_key
                .arithmetic
                .compute_quotient_i(i, a_w, b_w, c_w, d_w);

            let b = prover_key.range.compute_quotient_i(
                i,
                range_challenge,
                a_w,
                b_w,
                c_w,
                d_w,
                d_w_next,
            );

            let c = prover_key.logic.compute_quotient_i(
                i,
                logic_challenge,
                a_w,
                a_w_next,
                b_w,
                b_w_next,
                c_w,
                d_w,
                d_w_next,
            );

            let d = prover_key.fixed_base.compute_quotient_i(
                i,
                fixed_base_challenge,
                a_w,
                a_w_next,
                b_w,
                b_w_next,
                c_w,
                d_w,
                d_w_next,
            );

            let e = prover_key.variable_base.compute_quotient_i(
                i,
                var_base_challenge,
                a_w,
                a_w_next,
                b_w,
                b_w_next,
                c_w,
                d_w,
                d_w_next,
            );

            (a + pi) + b + c + d + e
        })
        .collect();
    t
}

fn compute_permutation_checks(
    fft: &Fft<BlsScalar>,
    fft_n8: &Fft<BlsScalar>,
    prover_key: &ProverKey,
    (a_w_eval_8n, b_w_eval_8n, c_w_eval_8n, d_w_eval_8n): (
        &[BlsScalar],
        &[BlsScalar],
        &[BlsScalar],
        &[BlsScalar],
    ),
    z_eval_8n: &[BlsScalar],
    (alpha, beta, gamma): (&BlsScalar, &BlsScalar, &BlsScalar),
) -> Vec<BlsScalar> {
    let l1_poly_alpha = compute_first_lagrange_poly_scaled(fft, alpha.square());
    let mut l1_poly_alpha = ZeroPoly::new(l1_poly_alpha.coeffs);
    fft_n8.coset_dft(&mut l1_poly_alpha);
    let l1_alpha_sq_evals = l1_poly_alpha.0;

    #[cfg(not(feature = "std"))]
    let range = (0..fft_n8.size()).into_iter();

    #[cfg(feature = "std")]
    let range = (0..fft_n8.size()).into_par_iter();

    let t: Vec<_> = range
        .map(|i| {
            prover_key.permutation.compute_quotient_i(
                i,
                &a_w_eval_8n[i],
                &b_w_eval_8n[i],
                &c_w_eval_8n[i],
                &d_w_eval_8n[i],
                &z_eval_8n[i],
                &z_eval_8n[i + 8],
                alpha,
                &l1_alpha_sq_evals[i],
                beta,
                gamma,
            )
        })
        .collect();
    t
}

fn compute_first_lagrange_poly_scaled(
    fft: &Fft<BlsScalar>,
    scale: BlsScalar,
) -> Polynomial {
    let mut x_evals = ZeroPoly::new(vec![BlsScalar::zero(); fft.size()]);
    x_evals.0[0] = scale;
    fft.idft(&mut x_evals);
    Polynomial::from_coefficients_vec(x_evals.0)
}
