// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Key module contains the utilities and data structures
//! that support the generation and usage of Commit and
//! Opening keys.
use super::proof::Proof;
use crate::{error::Error, transcript::TranscriptProtocol, util};
use codec::{Decode, Encode};
use merlin::Transcript;
use zero_crypto::behave::{Group, Pairing, PairingRange};

// /// CommitKey is used to commit to a polynomial which is bounded by the
// /// max_degree.
// #[derive(Debug, Clone, PartialEq, Eq, Decode, Encode)]
// pub struct CommitKey {
//     pub(crate) powers_of_g: Vec<G1Affine>,
// }

// impl CommitKey {
//     /// Returns the maximum degree polynomial that you can commit to.
//     pub(crate) fn max_degree(&self) -> usize {
//         self.powers_of_g.len() - 1
//     }

//     /// Truncates the commit key to a lower max degree.
//     /// Returns an error if the truncated degree is zero or if the truncated
//     /// degree is larger than the max degree of the commit key.
//     pub(crate) fn truncate(
//         &self,
//         mut truncated_degree: usize,
//     ) -> Result<CommitKey, Error> {
//         match truncated_degree {
//             // Check that the truncated degree is not zero
//             0 => Err(Error::TruncatedDegreeIsZero),
//             // Check that max degree is less than truncated degree
//             i if i > self.max_degree() =>
// Err(Error::TruncatedDegreeTooLarge),             i => {
//                 if i == 1 {
//                     truncated_degree += 1
//                 };
//                 let truncated_powers = Self {
//                     powers_of_g:
// self.powers_of_g[..=truncated_degree].to_vec(),                 };
//                 Ok(truncated_powers)
//             }
//         }
//     }

//     /// Checks whether the polynomial we are committing to:
//     /// - Has zero degree
//     /// - Has a degree which is more than the max supported degree
//     ///
//     /// Returns an error if any of the above conditions are true.
//     fn check_commit_degree_is_within_bounds(
//         &self,
//         poly_degree: usize,
//     ) -> Result<(), Error> {
//         match (poly_degree == 0, poly_degree > self.max_degree()) {
//             (true, _) => Err(Error::PolynomialDegreeIsZero),
//             (false, true) => Err(Error::PolynomialDegreeTooLarge),
//             (false, false) => Ok(()),
//         }
//     }

//     pub(crate) fn commit(
//         &self,
//         polynomial: &Polynomial,
//     ) -> Result<Commitment, Error> {
//         // Check whether we can safely commit to this polynomial
//         self.check_commit_degree_is_within_bounds(polynomial.degree())?;

//         // Compute commitment
//         Ok(Commitment::from(msm_variable_base(
//             &self.powers_of_g,
//             &polynomial.coeffs,
//         )))
//     }

//     pub(crate) fn compute_aggregate_witness(
//         &self,
//         polynomials: &[Polynomial],
//         point: &BlsScalar,
//         transcript: &mut Transcript,
//     ) -> Polynomial {
//         let v_challenge = transcript.challenge_scalar(b"v_challenge");
//         let powers = util::powers_of(&v_challenge, polynomials.len() - 1);

//         assert_eq!(powers.len(), polynomials.len());

//         let numerator: Polynomial = polynomials
//             .iter()
//             .zip(powers.iter())
//             .map(|(poly, v_challenge)| poly * v_challenge)
//             .sum();
//         numerator.ruffini(*point)
//     }
// }

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

// impl<P: Pairing> Serializable<{ G1Affine::SIZE + G2Affine::SIZE * 2 }>
//     for OpeningKey<P>
// {
//     type Error = dusk_bytes::Error;
//     #[allow(unused_must_use)]
//     fn to_bytes(&self) -> [u8; Self::SIZE] {
//         use dusk_bytes::Write;
//         let mut buf = [0u8; Self::SIZE];
//         let mut writer = &mut buf[..];
//         // This can't fail therefore we don't care about the Result nor use
// it.         writer.write(&self.g.to_bytes());
//         writer.write(&self.h.to_bytes());
//         writer.write(&self.beta_h.to_bytes());

//         buf
//     }

//     fn from_bytes(buf: &[u8; Self::SIZE]) -> Result<Self, Self::Error> {
//         let mut buffer = &buf[..];
//         let g = G1Affine::from_reader(&mut buffer)?;
//         let h = G2Affine::from_reader(&mut buffer)?;
//         let beta_h = G2Affine::from_reader(&mut buffer)?;

//         Ok(Self::new(g, h, beta_h))
//     }
// }

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
        let powers = util::powers_of::<P>(&u_challenge, proofs.len() - 1);
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
            (affine_total_w, self.prepared_beta_h),
            (affine_total_c, self.prepared_h),
        ])
        .final_exp();

        if pairing != <<P as zero_crypto::behave::Pairing>::PairingRange as PairingRange>::Gt::ADDITIVE_IDENTITY {
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
    use crate::fft::Polynomial;
    use rand_core::OsRng;
    use zero_bls12_381::Fr as BlsScalar;
    use zero_kzg::{KeyPair, Polynomial as ZeroPoly};
    use zero_pairing::TatePairing;

    // Checks that a polynomial `p` was evaluated at a point `z` and returned
    // the value specified `v`. ie. v = p(z).
    // fn check(op_key: &OpeningKey, point: BlsScalar, proof: Proof) -> bool {
    //     let inner_a: G1Affine = (proof.commitment_to_polynomial.0
    //         - (op_key.g * proof.evaluated_point))
    //         .into();

    //     let inner_b: G2Affine = (op_key.beta_h - (op_key.h * point)).into();
    //     let prepared_inner_b = G2Prepared::from(-inner_b);

    //     let pairing = TatePairing::multi_miller_loop(&[
    //         (inner_a, op_key.prepared_h.clone()),
    //         (proof.commitment_to_witness.0, prepared_inner_b),
    //     ])
    //     .final_exp();

    //     pairing == zero_bls12_381::Gt::ADDITIVE_IDENTITY
    // }

    // Creates an opening proof that a polynomial `p` was correctly evaluated at
    // p(z) and produced the value `v`. ie v = p(z).
    // Returns an error if the polynomials degree is too large.
    // fn open_single(
    //     ck: &CommitKey,
    //     polynomial: &Polynomial,
    //     value: &BlsScalar,
    //     point: &BlsScalar,
    // ) -> Result<Proof, Error> {
    //     let witness_poly = compute_single_witness(polynomial, point);
    //     Ok(Proof {
    //         commitment_to_witness: ck.commit(&witness_poly)?,
    //         evaluated_point: *value,
    //         commitment_to_polynomial: ck.commit(polynomial)?,
    //     })
    // }

    // Creates an opening proof that multiple polynomials were evaluated at the
    // same point and that each evaluation produced the correct evaluation
    // point. Returns an error if any of the polynomial's degrees are too
    // large.
    // fn open_multiple(
    //     ck: &CommitKey,
    //     polynomials: &[Polynomial],
    //     evaluations: Vec<BlsScalar>,
    //     point: &BlsScalar,
    //     transcript: &mut Transcript,
    // ) -> Result<AggregateProof, Error> {
    //     // Commit to polynomials
    //     let mut polynomial_commitments =
    // Vec::with_capacity(polynomials.len());     for poly in
    // polynomials.iter() {         polynomial_commitments.push(ck.
    // commit(poly)?)     }

    //     // Compute the aggregate witness for polynomials
    //     let witness_poly =
    //         ck.compute_aggregate_witness(polynomials, point, transcript);

    //     // Commit to witness polynomial
    //     let witness_commitment = ck.commit(&witness_poly)?;

    //     let aggregate_proof = AggregateProof {
    //         commitment_to_witness: witness_commitment,
    //         evaluated_points: evaluations,
    //         commitments_to_polynomials: polynomial_commitments,
    //     };
    //     Ok(aggregate_proof)
    // }

    // For a given polynomial `p` and a point `z`, compute the witness
    // for p(z) using Ruffini's method for simplicity.
    // The Witness is the quotient of f(x) - f(z) / x-z.
    // However we note that the quotient polynomial is invariant under the value
    // f(z) ie. only the remainder changes. We can therefore compute the
    // witness as f(x) / x - z and only use the remainder term f(z) during
    // verification.
    // fn compute_single_witness(
    //     polynomial: &Polynomial,
    //     point: &BlsScalar,
    // ) -> Polynomial {
    //     // Computes `f(x) / x-z`, returning it as the witness poly
    //     polynomial.ruffini(*point)
    // }

    // Creates a proving key and verifier key based on a specified degree
    // fn setup_test(degree: usize) -> Result<(CommitKey, OpeningKey), Error> {
    //     let srs = PublicParameters::setup(degree, &mut OsRng)?;
    //     srs.trim(degree)
    // }
    #[test]
    fn test_basic_commit() -> Result<(), Error> {
        let degree = 2;
        let r = BlsScalar::from(255);
        // let (ck, opening_key) = setup_test(degree)?;
        let keypair = KeyPair::<TatePairing>::setup(degree as u64, r);
        let point = BlsScalar::from(10);

        let poly = Polynomial::rand(degree, &mut OsRng);
        let z_poly = ZeroPoly(poly.coeffs.clone());
        // let value = poly.evaluate(&point);

        // let proof = open_single(&ck, &poly, &value, &point)?;
        let witness = keypair.create_witness(&z_poly, point);

        // let ok = check(&opening_key, point, proof);
        let z_ok = witness.verify();
        // assert!(ok);
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
    //     let poly_a = Polynomial::rand(degree, &mut OsRng);
    //     let value_a = poly_a.evaluate(&point_a);
    //     let proof_a = open_single(&ck, &poly_a, &value_a, &point_a)?;
    //     assert!(check(&vk, point_a, proof_a));

    //     // Compute secret polynomial b
    //     let poly_b = Polynomial::rand(degree, &mut OsRng);
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
    //         let poly_a = Polynomial::rand(25, &mut OsRng);
    //         let poly_a_eval = poly_a.evaluate(&point);

    //         let poly_b = Polynomial::rand(26 + 1, &mut OsRng);
    //         let poly_b_eval = poly_b.evaluate(&point);

    //         let poly_c = Polynomial::rand(27, &mut OsRng);
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
    //         let poly_a = Polynomial::rand(25, &mut OsRng);
    //         let poly_a_eval = poly_a.evaluate(&point_a);

    //         let poly_b = Polynomial::rand(26, &mut OsRng);
    //         let poly_b_eval = poly_b.evaluate(&point_a);

    //         let poly_c = Polynomial::rand(27, &mut OsRng);
    //         let poly_c_eval = poly_c.evaluate(&point_a);

    //         let poly_d = Polynomial::rand(28, &mut OsRng);
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
