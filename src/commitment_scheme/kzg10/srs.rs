// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! The Public Parameters can also be referred to as the Structured Reference
//! String (SRS).
use super::key::{CommitKey, OpeningKey};
use crate::{error::Error, util};
use alloc::vec::Vec;
use codec::{Decode, Encode};
use rand_core::RngCore;
use sp_std::vec;
use zero_bls12_381::{G1Affine, G1Projective, G2Affine};

/// The Public Parameters can also be referred to as the Structured Reference
/// String (SRS). It is available to both the prover and verifier and allows the
/// verifier to efficiently verify and make claims about polynomials up to and
/// including a configured degree.
#[derive(Debug, Clone, Encode, Eq, Decode)]
// TODO remove the `Sized` bound on the serializer
pub struct PublicParameters {
    /// Key used to generate proofs for composed circuits.
    pub(crate) commit_key: CommitKey,
    /// Key used to verify proofs for composed circuits.
    pub(crate) opening_key: OpeningKey,
}

impl PublicParameters {
    /// The maximum degree is the degree of the constraint system + 6,
    /// because adding the blinding factors requires some extra elements
    /// for the SRS: +1 per each wire (we have 4 wires), plus +2 for the
    /// permutation polynomial
    const ADDED_BLINDING_DEGREE: usize = 6;

    /// Setup generates the public parameters using a random number generator.
    /// This method will in most cases be used for testing and exploration.
    /// In reality, a `Trusted party` or a `Multiparty Computation` will be used
    /// to generate the SRS. Returns an error if the configured degree is less
    /// than one.
    pub fn setup<R: RngCore>(
        mut max_degree: usize,
        mut rng: &mut R,
    ) -> Result<PublicParameters, Error> {
        // Cannot commit to constants
        if max_degree < 1 {
            return Err(Error::DegreeIsZero);
        }

        // we update the degree to match the required one (n + 6)
        max_degree += Self::ADDED_BLINDING_DEGREE;

        // Generate the secret scalar x
        let x = util::random_scalar(&mut rng);

        // Compute powers of x up to and including x^max_degree
        let powers_of_x = util::powers_of(&x, max_degree);

        // Powers of G1 that will be used to commit to a specified polynomial
        let g = util::random_g1_point(&mut rng);
        let powers_of_g: Vec<G1Projective> =
            util::slow_multiscalar_mul_single_base(&powers_of_x, g);
        assert_eq!(powers_of_g.len(), max_degree + 1);

        // Normalize all projective points
        let mut normalized_g =
            vec![G1Affine::ADDITIVE_IDENTITY; max_degree + 1];
        G1Projective::batch_normalize(&powers_of_g, &mut normalized_g);

        // Compute x_2 = x*h element and stored cached elements for verifying
        // multiple proofs.
        let h: G2Affine = util::random_g2_point(&mut rng).into();
        let x_2: G2Affine = (h * x).into();

        Ok(PublicParameters {
            commit_key: CommitKey {
                powers_of_g: normalized_g,
            },
            opening_key: OpeningKey::new(g.into(), h, x_2),
        })
    }

    /// Trim truncates the [`PublicParameters`] to allow the prover to commit to
    /// polynomials up to the and including the truncated degree.
    /// Returns the [`CommitKey`] and [`OpeningKey`] used to generate and verify
    /// proofs.
    ///
    /// Returns an error if the truncated degree is larger than the public
    /// parameters configured degree.
    pub(crate) fn trim(
        &self,
        truncated_degree: usize,
    ) -> Result<(CommitKey, OpeningKey), Error> {
        let truncated_prover_key = self
            .commit_key
            .truncate(truncated_degree + Self::ADDED_BLINDING_DEGREE)?;
        let opening_key = self.opening_key.clone();
        Ok((truncated_prover_key, opening_key))
    }

    /// Max degree specifies the largest Polynomial
    /// that this prover key can commit to.
    pub fn max_degree(&self) -> usize {
        self.commit_key.max_degree()
    }
}

impl PartialEq for PublicParameters {
    fn eq(&self, other: &Self) -> bool {
        self.commit_key == other.commit_key
            && self.opening_key == other.opening_key
    }
}

#[cfg(feature = "std")]
#[cfg(test)]
mod test {
    use super::*;
    use zero_bls12_381::Fr as BlsScalar;
    use zero_crypto::behave::FftField;

    #[test]
    fn test_powers_of() {
        let x = BlsScalar::from(10u64);
        let degree = 100u64;

        let powers_of_x = util::powers_of(&x, degree as usize);

        for (i, x_i) in powers_of_x.iter().enumerate() {
            assert_eq!(*x_i, x.pow(i as u64))
        }

        let last_element = powers_of_x.last().unwrap();
        assert_eq!(*last_element, x.pow(degree))
    }
}
