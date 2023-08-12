// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Key module contains the utilities and data structures
//! that support the generation and usage of Commit and
//! Opening keys.
use super::proof::Proof;
use crate::error::Error;
use codec::{Decode, Encode};
use poly_commit::powers_of;
use zksnarks::{Transcript, TranscriptProtocol};
use zkstd::behave::{CurveGroup, Group, Pairing, PairingRange};

/// Opening Key is used to verify opening proofs made about a committed
/// polynomial.
#[derive(Clone, Debug, Eq, Decode, Encode)]
// TODO remove the `Sized` bound on the serializer
pub struct OpeningKey<P: Pairing> {
    /// The generator of G1.
    pub(crate) g: P::G1Affine,
    /// The generator of G2.
    pub(crate) h: P::G2Affine,
    /// \beta times the above generator of G2.
    pub(crate) beta_h: P::G2Affine,
    /// The generator of G2, prepared for use in pairings.
    pub(crate) prepared_h: P::G2PairngRepr,
    /// \beta times the above generator of G2, prepared for use in pairings.
    pub(crate) prepared_beta_h: P::G2PairngRepr,
}

impl<P: Pairing> OpeningKey<P> {
    pub(crate) fn new(
        g: P::G1Affine,
        h: P::G2Affine,
        beta_h: P::G2Affine,
    ) -> OpeningKey<P> {
        let prepared_h = P::G2PairngRepr::from(h);
        let prepared_beta_h = P::G2PairngRepr::from(beta_h);
        OpeningKey {
            g,
            h,
            beta_h,
            prepared_h,
            prepared_beta_h,
        }
    }

    /// Checks whether a batch of polynomials evaluated at different points,
    /// returned their specified value.
    pub(crate) fn batch_check(
        &self,
        points: &[P::ScalarField],
        proofs: &[Proof<P>],
        transcript: &mut Transcript,
    ) -> Result<(), Error> {
        let mut total_c = P::G1Projective::ADDITIVE_IDENTITY;
        let mut total_w = P::G1Projective::ADDITIVE_IDENTITY;

        let u_challenge =
            <Transcript as TranscriptProtocol<P>>::challenge_scalar(
                transcript, b"batch",
            ); // XXX: Verifier can add their own randomness at this point
        let powers = powers_of(&u_challenge, proofs.len() - 1);
        // Instead of multiplying g and gamma_g in each turn, we simply
        // accumulate their coefficients and perform a final
        // multiplication at the end.
        let mut g_multiplier = P::ScalarField::zero();

        for ((proof, u_challenge), point) in
            proofs.iter().zip(powers).zip(points)
        {
            let mut c = P::G1Projective::from(proof.commitment_to_polynomial.0);
            let w = P::G1Projective::from(proof.commitment_to_witness.0);
            c += w * *point;
            g_multiplier += u_challenge * proof.evaluated_point;

            total_c += c * u_challenge;
            total_w += w * u_challenge;
        }
        total_c -= P::G1Projective::from(self.g) * g_multiplier;

        let affine_total_w = P::G1Affine::from(-total_w);
        let affine_total_c = P::G1Affine::from(total_c);

        let pairing = P::multi_miller_loop(&[
            (affine_total_w, self.prepared_beta_h.clone()),
            (affine_total_c, self.prepared_h.clone()),
        ])
        .final_exp();

        if pairing != <<P as zkstd::behave::Pairing>::PairingRange as PairingRange>::Gt::ADDITIVE_IDENTITY {
            return Err(Error::PairingCheckFailure);
        };
        Ok(())
    }
}

impl<P: Pairing> PartialEq for OpeningKey<P> {
    fn eq(&self, other: &Self) -> bool {
        self.g == other.g
            && self.h == other.h
            && self.beta_h == other.beta_h
            && self.prepared_h == other.prepared_h
            && self.prepared_beta_h == other.prepared_beta_h
    }
}

#[cfg(feature = "std")]
#[cfg(test)]
mod test {
    use super::*;
    use bls_12_381::Fr as BlsScalar;
    use ec_pairing::TatePairing;
    use poly_commit::{Coefficients, KeyPair};
    use rand_core::OsRng;

    #[test]
    fn test_basic_commit() -> Result<(), Error> {
        let degree = 2;
        let r = BlsScalar::random(OsRng);
        let keypair = KeyPair::<TatePairing>::setup(degree as u64, r);
        let point = BlsScalar::from(10);

        let z_poly = Coefficients::rand(degree, &mut OsRng);

        let witness = keypair.create_witness(&z_poly, point);

        let z_ok = witness.verify();
        assert!(z_ok);
        Ok(())
    }

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
