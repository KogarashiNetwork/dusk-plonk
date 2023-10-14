// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Ideally we should cleanly abstract away the polynomial commitment scheme
//! We note that PLONK makes use of the linearization technique
//! conceived in SONIC [Mary Maller].
//!
//! This technique implicitly requires the
//! commitment scheme to be homomorphic. `Merkle Tree like` techniques such as
//! FRI are not homomorphic and therefore for PLONK to be usable with all
//! commitment schemes without modification, one would need to remove the
//! linearizer

use poly_commit::{powers_of, Commitment, EvaluationKey, Proof};
#[cfg(feature = "std")]
use rayon::prelude::*;
use zksnarks::error::Error;
use zksnarks::plonk::{Transcript, TranscriptProtocol};
use zkstd::common::{CurveGroup, Group, Pairing, PairingRange, Vec};

pub(crate) fn batch_check<P: Pairing>(
    evaluation_key: &EvaluationKey<P>,
    points: &[P::ScalarField],
    proofs: &[Proof<P>],
    transcript: &mut Transcript,
) -> Result<(), Error> {
    let mut total_c = P::G1Projective::ADDITIVE_IDENTITY;
    let mut total_w = P::G1Projective::ADDITIVE_IDENTITY;

    let u_challenge = <Transcript as TranscriptProtocol<P>>::challenge_scalar(
        transcript, b"batch",
    ); // XXX: Verifier can add their own randomness at this point
    let powers = powers_of(&u_challenge, proofs.len() - 1);
    // Instead of multiplying g and gamma_g in each turn, we simply
    // accumulate their coefficients and perform a final
    // multiplication at the end.
    let mut g_multiplier = P::ScalarField::zero();

    for ((proof, u_challenge), point) in proofs.iter().zip(powers).zip(points) {
        let mut c = P::G1Projective::from(proof.commitment_to_polynomial.0);
        let w = P::G1Projective::from(proof.commitment_to_witness.0);
        c += w * *point;
        g_multiplier += u_challenge * proof.evaluated_point;

        total_c += c * u_challenge;
        total_w += w * u_challenge;
    }
    total_c -= P::G1Projective::from(evaluation_key.g) * g_multiplier;

    let affine_total_w = P::G1Affine::from(-total_w);
    let affine_total_c = P::G1Affine::from(total_c);

    let pairing = P::multi_miller_loop(&[
        (affine_total_w, evaluation_key.prepared_beta_h.clone()),
        (affine_total_c, evaluation_key.prepared_h.clone()),
    ])
    .final_exp();

    if pairing != <<P as zkstd::behave::Pairing>::PairingRange as PairingRange>::Gt::ADDITIVE_IDENTITY {
        return Err(Error::PairingCheckFailure);
    };
    Ok(())
}

/// Proof that multiple polynomials were correctly evaluated at a point `z`,
/// each producing their respective evaluated points p_i(z).
#[derive(Debug)]
pub(crate) struct AggregateProof<P: Pairing> {
    /// This is a commitment to the aggregated witness polynomial.
    pub(crate) commitment_to_witness: Commitment<P::G1Affine>,
    /// These are the results of the evaluating each polynomial at the
    /// point `z`.
    pub(crate) evaluated_points: Vec<P::ScalarField>,
    /// These are the commitments to the polynomials which you want to
    /// prove a statement about.
    pub(crate) commitments_to_polynomials: Vec<Commitment<P::G1Affine>>,
}

impl<P: Pairing> AggregateProof<P> {
    /// Initializes an `AggregatedProof` with the commitment to the witness.
    pub(crate) fn with_witness(
        witness: Commitment<P::G1Affine>,
    ) -> AggregateProof<P> {
        AggregateProof {
            commitment_to_witness: witness,
            evaluated_points: Vec::new(),
            commitments_to_polynomials: Vec::new(),
        }
    }

    /// Adds an evaluated point with the commitment to the polynomial which
    /// produced it.
    pub(crate) fn add_part(
        &mut self,
        part: (P::ScalarField, Commitment<P::G1Affine>),
    ) {
        self.evaluated_points.push(part.0);
        self.commitments_to_polynomials.push(part.1);
    }

    /// Flattens an `AggregateProof` into a `Proof`.
    /// The transcript must have the same view as the transcript that was
    /// used to aggregate the witness in the proving stage.
    pub(crate) fn flatten(&self, transcript: &mut Transcript) -> Proof<P> {
        let v_challenge: P::ScalarField = <Transcript as TranscriptProtocol<
            P,
        >>::challenge_scalar(
            transcript, b"v_challenge"
        );
        let powers =
            powers_of(&v_challenge, self.commitments_to_polynomials.len() - 1);

        #[cfg(not(feature = "std"))]
        let flattened_poly_commitments_iter =
            self.commitments_to_polynomials.iter().zip(powers.iter());
        #[cfg(not(feature = "std"))]
        let flattened_poly_evaluations_iter =
            self.evaluated_points.iter().zip(powers.iter());

        #[cfg(feature = "std")]
        let flattened_poly_commitments_iter = self
            .commitments_to_polynomials
            .par_iter()
            .zip(powers.par_iter());
        #[cfg(feature = "std")]
        let flattened_poly_evaluations_iter =
            self.evaluated_points.par_iter().zip(powers.par_iter());

        // Flattened polynomial commitments using challenge `v`
        let flattened_poly_commitments: P::G1Projective =
            flattened_poly_commitments_iter
                .map(|(poly, v_challenge)| {
                    P::G1Projective::from(poly.0) * *v_challenge
                })
                .sum();
        // Flattened evaluation points
        let flattened_poly_evaluations: P::ScalarField =
            flattened_poly_evaluations_iter
                .map(|(eval, v_challenge)| *eval * *v_challenge)
                .sum();

        Proof {
            commitment_to_witness: self.commitment_to_witness,
            evaluated_point: flattened_poly_evaluations,
            commitment_to_polynomial: Commitment::new(
                flattened_poly_commitments,
            ),
        }
    }
}

#[cfg(feature = "std")]
#[cfg(test)]
mod test {
    // #[test]
    // fn test_batch_verification() -> Result<(), Error> {
    //     let degree = 25;
    //     let (ck, vk) = setup_test(degree)?;

    //     let point_a = BlsScalar::from(10);
    //     let point_b = BlsScalar::from(11);

    //     // Compute secret polynomial a
    //     let poly_a = Coefficients::rand(degree, &mut OsRng);
    //     let value_a = poly_a.evaluate(&point_a);
    //     let proof_a = open_single(&ck, &poly_a, &value_a, &point_a)?;
    //     assert!(check(&vk, point_a, proof_a));

    //     // Compute secret polynomial b
    //     let poly_b = Coefficients::rand(degree, &mut OsRng);
    //     let value_b = poly_b.evaluate(&point_b);
    //     let proof_b = open_single(&ck, &poly_b, &value_b, &point_b)?;
    //     assert!(check(&vk, point_b, proof_b));

    //     vk.batch_check(
    //         &[point_a, point_b],
    //         &[proof_a, proof_b],
    //         &mut Transcript::new(b""),
    //     )
    // }

    // #[test]
    // fn test_aggregate_witness() -> Result<(), Error> {
    //     let max_degree = 27;
    //     let (ck, opening_key) = setup_test(max_degree)?;
    //     let point = BlsScalar::from(10);

    //     // Committer's View
    //     let aggregated_proof = {
    //         // Compute secret polynomials and their evaluations
    //         let poly_a = Coefficients::rand(25, &mut OsRng);
    //         let poly_a_eval = poly_a.evaluate(&point);

    //         let poly_b = Coefficients::rand(26 + 1, &mut OsRng);
    //         let poly_b_eval = poly_b.evaluate(&point);

    //         let poly_c = Coefficients::rand(27, &mut OsRng);
    //         let poly_c_eval = poly_c.evaluate(&point);

    //         open_multiple(
    //             &ck,
    //             &[poly_a, poly_b, poly_c],
    //             vec![poly_a_eval, poly_b_eval, poly_c_eval],
    //             &point,
    //             &mut Transcript::new(b"agg_flatten"),
    //         )?
    //     };

    //     // Verifier's View
    //     let ok = {
    //         let flattened_proof =
    //             aggregated_proof.flatten(&mut
    // Transcript::new(b"agg_flatten"));         check(&opening_key, point,
    // flattened_proof)     };

    //     assert!(ok);
    //     Ok(())
    // }

    // #[test]
    // fn test_batch_with_aggregation() -> Result<(), Error> {
    //     let max_degree = 28;
    //     let (ck, opening_key) = setup_test(max_degree)?;
    //     let point_a = BlsScalar::from(10);
    //     let point_b = BlsScalar::from(11);

    //     // Committer's View
    //     let (aggregated_proof, single_proof) = {
    //         // Compute secret polynomial and their evaluations
    //         let poly_a = Coefficients::rand(25, &mut OsRng);
    //         let poly_a_eval = poly_a.evaluate(&point_a);

    //         let poly_b = Coefficients::rand(26, &mut OsRng);
    //         let poly_b_eval = poly_b.evaluate(&point_a);

    //         let poly_c = Coefficients::rand(27, &mut OsRng);
    //         let poly_c_eval = poly_c.evaluate(&point_a);

    //         let poly_d = Coefficients::rand(28, &mut OsRng);
    //         let poly_d_eval = poly_d.evaluate(&point_b);

    //         let aggregated_proof = open_multiple(
    //             &ck,
    //             &[poly_a, poly_b, poly_c],
    //             vec![poly_a_eval, poly_b_eval, poly_c_eval],
    //             &point_a,
    //             &mut Transcript::new(b"agg_batch"),
    //         )?;

    //         let single_proof =
    //             open_single(&ck, &poly_d, &poly_d_eval, &point_b)?;

    //         (aggregated_proof, single_proof)
    //     };

    //     // Verifier's View

    //     let mut transcript = Transcript::new(b"agg_batch");
    //     let flattened_proof = aggregated_proof.flatten(&mut transcript);

    //     opening_key.batch_check(
    //         &[point_a, point_b],
    //         &[flattened_proof, single_proof],
    //         &mut transcript,
    //     )
    // }
}
