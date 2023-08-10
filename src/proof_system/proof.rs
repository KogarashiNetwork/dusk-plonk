// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! A Proof stores the commitments to all of the elements that
//! are needed to univocally identify a prove of some statement.

use codec::{Decode, Encode};
use poly_commit::{Commitment, Polynomial};
use zksnarks::Evaluations as ProofEvaluations;
use zkstd::behave::Ring;

/// A Proof is a composition of `Commitment`s to the Witness, Permutation,
/// Quotient, Shifted and Opening polynomials as well as the
/// `ProofEvaluations`.
///
/// It's main goal is to allow the `Verifier` to
/// formally verify that the secret witnesses used to generate the [`Proof`]
/// satisfy a circuit that both [`Builder`](crate::prelude::Builder) and
/// [`Verifier`](crate::prelude::Verifier) have in common succintly
/// and without any capabilities of adquiring any kind of knowledge about the
/// witness used to construct the Proof.
#[derive(Debug, Eq, PartialEq, Clone, Decode, Encode)]

pub struct Proof<P: Pairing> {
    /// Commitment to the witness polynomial for the left wires.
    pub(crate) a_comm: Commitment<P::G1Affine>,
    /// Commitment to the witness polynomial for the right wires.
    pub(crate) b_comm: Commitment<P::G1Affine>,
    /// Commitment to the witness polynomial for the output wires.
    pub(crate) c_comm: Commitment<P::G1Affine>,
    /// Commitment to the witness polynomial for the fourth wires.
    pub(crate) d_comm: Commitment<P::G1Affine>,

    /// Commitment to the permutation polynomial.
    pub(crate) z_comm: Commitment<P::G1Affine>,

    /// Commitment to the quotient polynomial.
    pub(crate) t_low_comm: Commitment<P::G1Affine>,
    /// Commitment to the quotient polynomial.
    pub(crate) t_mid_comm: Commitment<P::G1Affine>,
    /// Commitment to the quotient polynomial.
    pub(crate) t_high_comm: Commitment<P::G1Affine>,
    /// Commitment to the quotient polynomial.
    pub(crate) t_4_comm: Commitment<P::G1Affine>,

    /// Commitment to the opening polynomial.
    pub(crate) w_z_chall_comm: Commitment<P::G1Affine>,
    /// Commitment to the shifted opening polynomial.
    pub(crate) w_z_chall_w_comm: Commitment<P::G1Affine>,
    /// Subset of all of the evaluations added to the proof.
    pub(crate) evaluations: ProofEvaluations<P::ScalarField>,
}

use crate::{
    commitment_scheme::{AggregateProof, OpeningKey},
    error::Error,
    fft::EvaluationDomain,
    proof_system::widget::VerificationKey,
    transcript::TranscriptProtocol,
    util::batch_inversion,
};
#[rustfmt::skip]
    use ::alloc::vec::Vec;
use ec_pairing::msm_variable_base;
use merlin::Transcript;
#[cfg(feature = "std")]
use rayon::prelude::*;
use zkstd::{
    behave::{FftField, Group, PrimeField},
    common::Pairing,
};

impl<P: Pairing> Proof<P> {
    /// Performs the verification of a [`Proof`] returning a boolean result.
    pub(crate) fn verify(
        &self,
        verifier_key: &VerificationKey<P>,
        transcript: &mut Transcript,
        opening_key: &OpeningKey<P>,
        pub_inputs: &[P::ScalarField],
    ) -> Result<(), Error> {
        let n = verifier_key.n.next_power_of_two();
        let domain = EvaluationDomain::new(verifier_key.n)?;

        // Subgroup checks are done when the proof is deserialized.

        // In order for the Verifier and Prover to have the same view in the
        // non-interactive setting Both parties must commit the same
        // elements into the transcript Below the verifier will simulate
        // an interaction with the prover by adding the same elements
        // that the prover added into the transcript, hence generating the
        // same challenges
        //
        // Add commitment to witness polynomials to transcript
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            transcript,
            b"a_w",
            &self.a_comm,
        );
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            transcript,
            b"b_w",
            &self.b_comm,
        );
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            transcript,
            b"c_w",
            &self.c_comm,
        );
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            transcript,
            b"d_w",
            &self.d_comm,
        );

        // Compute beta and gamma challenges
        let beta = <Transcript as TranscriptProtocol<P>>::challenge_scalar(
            transcript, b"beta",
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript, b"beta", &beta,
        );
        let gamma = <Transcript as TranscriptProtocol<P>>::challenge_scalar(
            transcript, b"gamma",
        );

        // Add commitment to permutation polynomial to transcript
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            transcript,
            b"z",
            &self.z_comm,
        );

        // Compute quotient challenge
        let alpha = <Transcript as TranscriptProtocol<P>>::challenge_scalar(
            transcript, b"alpha",
        );
        let range_sep_challenge =
            <Transcript as TranscriptProtocol<P>>::challenge_scalar(
                transcript,
                b"range separation challenge",
            );
        let logic_sep_challenge =
            <Transcript as TranscriptProtocol<P>>::challenge_scalar(
                transcript,
                b"logic separation challenge",
            );
        let fixed_base_sep_challenge =
            <Transcript as TranscriptProtocol<P>>::challenge_scalar(
                transcript,
                b"fixed base separation challenge",
            );
        let var_base_sep_challenge =
            <Transcript as TranscriptProtocol<P>>::challenge_scalar(
                transcript,
                b"variable base separation challenge",
            );

        // Add commitment to quotient polynomial to transcript
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            transcript,
            b"t_low",
            &self.t_low_comm,
        );
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            transcript,
            b"t_mid",
            &self.t_mid_comm,
        );
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            transcript,
            b"t_high",
            &self.t_high_comm,
        );
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            transcript,
            b"t_4",
            &self.t_4_comm,
        );

        // Compute evaluation challenge z
        let z_challenge =
            <Transcript as TranscriptProtocol<P>>::challenge_scalar(
                transcript,
                b"z_challenge",
            );

        // Compute zero polynomial evaluated at challenge `z`
        let z_h_eval = Polynomial::t(n as u64, z_challenge);

        // Compute first lagrange polynomial evaluated at challenge `z`
        let l1_eval =
            compute_first_lagrange_evaluation(&domain, &z_h_eval, &z_challenge);

        // Compute quotient polynomial evaluated at challenge `z`
        let t_eval = self.compute_quotient_evaluation(
            &domain,
            pub_inputs,
            &alpha,
            &beta,
            &gamma,
            &z_challenge,
            &z_h_eval,
            &l1_eval,
            &self.evaluations.perm_eval,
        );

        // Compute commitment to quotient polynomial
        // This method is necessary as we pass the `un-splitted` variation
        // to our commitment scheme
        let t_comm = self.compute_quotient_commitment(&z_challenge, n);

        // Add evaluations to transcript
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"a_eval",
            &self.evaluations.a_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"b_eval",
            &self.evaluations.b_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"c_eval",
            &self.evaluations.c_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"d_eval",
            &self.evaluations.d_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"a_next_eval",
            &self.evaluations.a_next_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"b_next_eval",
            &self.evaluations.b_next_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"d_next_eval",
            &self.evaluations.d_next_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"s_sigma_1_eval",
            &self.evaluations.s_sigma_1_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"s_sigma_2_eval",
            &self.evaluations.s_sigma_2_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"s_sigma_3_eval",
            &self.evaluations.s_sigma_3_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"q_arith_eval",
            &self.evaluations.q_arith_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"q_c_eval",
            &self.evaluations.q_c_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"q_l_eval",
            &self.evaluations.q_l_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"q_r_eval",
            &self.evaluations.q_r_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"perm_eval",
            &self.evaluations.perm_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript, b"t_eval", &t_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            transcript,
            b"r_eval",
            &self.evaluations.r_poly_eval,
        );

        // Compute linearization commitment
        let r_comm = self.compute_linearization_commitment(
            &alpha,
            &beta,
            &gamma,
            (
                &range_sep_challenge,
                &logic_sep_challenge,
                &fixed_base_sep_challenge,
                &var_base_sep_challenge,
            ),
            &z_challenge,
            l1_eval,
            verifier_key,
        );

        // Commitment Scheme
        // Now we delegate computation to the commitment scheme by batch
        // checking two proofs The `AggregateProof`, which is a
        // proof that all the necessary polynomials evaluated at
        // challenge `z` are correct and a `SingleProof` which
        // is proof that the permutation polynomial evaluated at the shifted
        // root of unity is correct

        // Compose the Aggregated Proof
        //
        let mut aggregate_proof =
            AggregateProof::with_witness(self.w_z_chall_comm.clone());
        aggregate_proof.add_part((t_eval, t_comm));
        aggregate_proof.add_part((self.evaluations.r_poly_eval, r_comm));
        aggregate_proof
            .add_part((self.evaluations.a_eval, self.a_comm.clone()));
        aggregate_proof
            .add_part((self.evaluations.b_eval, self.b_comm.clone()));
        aggregate_proof
            .add_part((self.evaluations.c_eval, self.c_comm.clone()));
        aggregate_proof
            .add_part((self.evaluations.d_eval, self.d_comm.clone()));
        aggregate_proof.add_part((
            self.evaluations.s_sigma_1_eval,
            verifier_key.permutation.s_sigma_1.clone(),
        ));
        aggregate_proof.add_part((
            self.evaluations.s_sigma_2_eval,
            verifier_key.permutation.s_sigma_2.clone(),
        ));
        aggregate_proof.add_part((
            self.evaluations.s_sigma_3_eval,
            verifier_key.permutation.s_sigma_3.clone(),
        ));
        // Flatten proof with opening challenge
        let flattened_proof_a = aggregate_proof.flatten(transcript);

        // Compose the shifted aggregate proof
        let mut shifted_aggregate_proof =
            AggregateProof::with_witness(self.w_z_chall_w_comm.clone());
        shifted_aggregate_proof
            .add_part((self.evaluations.perm_eval, self.z_comm.clone()));
        shifted_aggregate_proof
            .add_part((self.evaluations.a_next_eval, self.a_comm.clone()));
        shifted_aggregate_proof
            .add_part((self.evaluations.b_next_eval, self.b_comm.clone()));
        shifted_aggregate_proof
            .add_part((self.evaluations.d_next_eval, self.d_comm.clone()));

        let flattened_proof_b = shifted_aggregate_proof.flatten(transcript);
        // Add commitment to openings to transcript
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            transcript,
            b"w_z",
            &self.w_z_chall_comm,
        );
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            transcript,
            b"w_z_w",
            &self.w_z_chall_w_comm,
        );
        // Batch check
        if opening_key
            .batch_check(
                &[z_challenge, (z_challenge * domain.group_gen)],
                &[flattened_proof_a, flattened_proof_b],
                transcript,
            )
            .is_err()
        {
            return Err(Error::ProofVerificationError);
        }

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn compute_quotient_evaluation(
        &self,
        domain: &EvaluationDomain<P>,
        pub_inputs: &[P::ScalarField],
        alpha: &P::ScalarField,
        beta: &P::ScalarField,
        gamma: &P::ScalarField,
        z_challenge: &P::ScalarField,
        z_h_eval: &P::ScalarField,
        l1_eval: &P::ScalarField,
        z_hat_eval: &P::ScalarField,
    ) -> P::ScalarField {
        // Compute the public input polynomial evaluated at challenge `z`
        let pi_eval = compute_barycentric_eval(pub_inputs, z_challenge, domain);

        // Compute powers of alpha_0
        let alpha_sq = alpha.square();

        // r + PI(z)
        let a = self.evaluations.r_poly_eval + pi_eval;

        // a + beta * sigma_1 + gamma
        let beta_sig1 = *beta * self.evaluations.s_sigma_1_eval;
        let b_0 = self.evaluations.a_eval + beta_sig1 + gamma;

        // b + beta * sigma_2 + gamma
        let beta_sig2 = *beta * self.evaluations.s_sigma_2_eval;
        let b_1 = self.evaluations.b_eval + beta_sig2 + gamma;

        // c + beta * sigma_3 + gamma
        let beta_sig3 = *beta * self.evaluations.s_sigma_3_eval;
        let b_2 = self.evaluations.c_eval + beta_sig3 + gamma;

        // ((d + gamma) * z_hat) * alpha_0
        let b_3 = (self.evaluations.d_eval + gamma) * z_hat_eval * alpha;

        let b = b_0 * b_1 * b_2 * b_3;

        // l_1(z) * alpha_0^2
        let c = *l1_eval * alpha_sq;

        // Return t_eval
        (
            a - b - c
            //+ d
        ) * z_h_eval.invert().unwrap()
    }

    fn compute_quotient_commitment(
        &self,
        z_challenge: &P::ScalarField,
        n: usize,
    ) -> Commitment<P::G1Affine> {
        let z_n = z_challenge.pow(n as u64);
        let z_two_n = z_challenge.pow(2 * n as u64);
        let z_three_n = z_challenge.pow(3 * n as u64);
        let t_comm = self.t_low_comm.0
            + self.t_mid_comm.0 * z_n
            + self.t_high_comm.0 * z_two_n
            + self.t_4_comm.0 * z_three_n;
        Commitment::new(t_comm)
    }

    // Commitment to [r]_1
    #[allow(clippy::too_many_arguments)]
    fn compute_linearization_commitment(
        &self,
        alpha: &P::ScalarField,
        beta: &P::ScalarField,
        gamma: &P::ScalarField,
        (
            range_sep_challenge,
            logic_sep_challenge,
            fixed_base_sep_challenge,
            var_base_sep_challenge,
        ): (
            &P::ScalarField,
            &P::ScalarField,
            &P::ScalarField,
            &P::ScalarField,
        ),
        z_challenge: &P::ScalarField,
        l1_eval: P::ScalarField,
        verifier_key: &VerificationKey<P>,
    ) -> Commitment<P::G1Affine> {
        let mut scalars: Vec<_> = Vec::with_capacity(6);
        let mut points: Vec<P::G1Affine> = Vec::with_capacity(6);

        let (arithmetic_scalars, arithmetic_points) =
            verifier_key.arithmetic.linearize(&self.evaluations);
        arithmetic_scalars
            .iter()
            .zip(arithmetic_points.iter())
            .for_each(|(scalar, point)| {
                scalars.push(*scalar);
                points.push(*point);
            });

        verifier_key.range.compute_linearization_commitment(
            range_sep_challenge,
            &mut scalars,
            &mut points,
            &self.evaluations,
        );

        let (logic_scalars, logic_points) = verifier_key
            .logic
            .linearize(logic_sep_challenge, &self.evaluations);
        logic_scalars.iter().zip(logic_points.iter()).for_each(
            |(scalar, point)| {
                scalars.push(*scalar);
                points.push(*point);
            },
        );

        let (scalar_scalars, scalar_points) = verifier_key
            .fixed_base
            .linearize(fixed_base_sep_challenge, &self.evaluations);
        scalar_scalars.iter().zip(scalar_points.iter()).for_each(
            |(scalar, point)| {
                scalars.push(*scalar);
                points.push(*point);
            },
        );

        let (addition_scalars, addition_points) = verifier_key
            .variable_base
            .linearize(var_base_sep_challenge, &self.evaluations);
        addition_scalars
            .iter()
            .zip(addition_points.iter())
            .for_each(|(scalar, point)| {
                scalars.push(*scalar);
                points.push(*point);
            });

        let (permutation_scalars, permutation_points) =
            verifier_key.permutation.linearize(
                z_challenge,
                (alpha, beta, gamma),
                &l1_eval,
                self.z_comm.0,
                &self.evaluations,
            );
        permutation_scalars
            .iter()
            .zip(permutation_points.iter())
            .for_each(|(scalar, point)| {
                scalars.push(*scalar);
                points.push(*point);
            });

        Commitment::new(msm_variable_base::<P>(&points, &scalars))
    }
}

fn compute_first_lagrange_evaluation<P: Pairing>(
    domain: &EvaluationDomain<P>,
    z_h_eval: &P::ScalarField,
    z_challenge: &P::ScalarField,
) -> P::ScalarField {
    let n_fr = P::ScalarField::from(domain.size() as u64);
    let denom = n_fr * (*z_challenge - P::ScalarField::one());
    *z_h_eval * denom.invert().unwrap()
}

fn compute_barycentric_eval<P: Pairing>(
    evaluations: &[P::ScalarField],
    point: &P::ScalarField,
    domain: &EvaluationDomain<P>,
) -> P::ScalarField {
    let numerator = (point.pow(domain.size() as u64) - P::ScalarField::one())
        * domain.size_inv;

    // Indices with non-zero evaluations
    #[cfg(not(feature = "std"))]
    let range = (0..evaluations.len()).into_iter();

    #[cfg(feature = "std")]
    let range = (0..evaluations.len()).into_par_iter();

    let non_zero_evaluations: Vec<usize> = range
        .filter(|&i| {
            let evaluation = &evaluations[i];
            evaluation != &P::ScalarField::zero()
        })
        .collect();

    // Only compute the denominators with non-zero evaluations
    #[cfg(not(feature = "std"))]
    let range = (0..non_zero_evaluations.len()).into_iter();

    #[cfg(feature = "std")]
    let range = (0..non_zero_evaluations.len()).into_par_iter();

    let mut denominators: Vec<P::ScalarField> = range
        .clone()
        .map(|i| {
            // index of non-zero evaluation
            let index = non_zero_evaluations[i];

            (domain.group_gen_inv.pow(index as u64) * point)
                - P::ScalarField::one()
        })
        .collect();
    batch_inversion::<P>(&mut denominators);

    let result: P::ScalarField = range
        .map(|i| {
            let eval_index = non_zero_evaluations[i];
            let eval = evaluations[eval_index];

            denominators[i] * eval
        })
        .sum();

    result * numerator
}
