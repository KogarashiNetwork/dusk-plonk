// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use codec::{Decode, Encode};
use zero_crypto::common::Pairing;
use zero_kzg::Commitment;

/// Proof that a polynomial `p` was correctly evaluated at a point `z`
/// producing the evaluated point p(z).
#[derive(Clone, Debug, Decode, Encode)]
#[allow(dead_code)]
pub(crate) struct Proof<P: Pairing> {
    /// This is a commitment to the witness polynomial.
    pub(crate) commitment_to_witness: Commitment<P>,
    /// This is the result of evaluating a polynomial at the point `z`.
    pub(crate) evaluated_point: P::ScalarField,
    /// This is the commitment to the polynomial that you want to prove a
    /// statement about.
    pub(crate) commitment_to_polynomial: Commitment<P>,
}

use crate::transcript::TranscriptProtocol;
use crate::util::powers_of;
#[rustfmt::skip]
    use ::alloc::vec::Vec;
use merlin::Transcript;
#[cfg(feature = "std")]
use rayon::prelude::*;

/// Proof that multiple polynomials were correctly evaluated at a point `z`,
/// each producing their respective evaluated points p_i(z).
#[derive(Debug)]
pub(crate) struct AggregateProof<P: Pairing> {
    /// This is a commitment to the aggregated witness polynomial.
    pub(crate) commitment_to_witness: Commitment<P>,
    /// These are the results of the evaluating each polynomial at the
    /// point `z`.
    pub(crate) evaluated_points: Vec<P::ScalarField>,
    /// These are the commitments to the polynomials which you want to
    /// prove a statement about.
    pub(crate) commitments_to_polynomials: Vec<Commitment<P>>,
}

impl<P: Pairing> AggregateProof<P> {
    /// Initializes an `AggregatedProof` with the commitment to the witness.
    pub(crate) fn with_witness(witness: Commitment<P>) -> AggregateProof<P> {
        AggregateProof {
            commitment_to_witness: witness,
            evaluated_points: Vec::new(),
            commitments_to_polynomials: Vec::new(),
        }
    }

    /// Adds an evaluated point with the commitment to the polynomial which
    /// produced it.
    pub(crate) fn add_part(&mut self, part: (P::ScalarField, Commitment<P>)) {
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
            &mut transcript, b"v_challenge"
        );
        let powers: Vec<P::ScalarField> = powers_of::<P>(
            &v_challenge,
            self.commitments_to_polynomials.len() - 1,
        );

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
