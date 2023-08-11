// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! In pairing-based SNARKs like GM17, we need to calculate
//! a quotient polynomial over a target polynomial with roots
//! at distinct points associated with each constraint of the
//! constraint system. In order to be efficient, we choose these
//! roots to be the powers of a 2^n root of unity in the field.
//! This allows us to perform polynomial operations in O(n)
//! by performing an O(n log n) FFT over such a domain.

/// Defines a domain over which finite field (I)FFTs can be performed. Works
/// only for fields that have a large multiplicative subgroup of size that is
/// a power-of-2.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub(crate) struct EvaluationDomain<P: Pairing> {
    /// The size of the domain.
    pub(crate) size: u64,
    /// `log_2(self.size)`.
    pub(crate) log_size_of_group: u32,
    /// Size of the domain as a field element.
    pub(crate) size_as_field_element: P::ScalarField,
    /// Inverse of the size in the field.
    pub(crate) size_inv: P::ScalarField,
    /// A generator of the subgroup.
    pub(crate) group_gen: P::ScalarField,
    /// Inverse of the generator of the subgroup.
    pub(crate) group_gen_inv: P::ScalarField,
    /// Multiplicative generator of the finite field.
    pub(crate) generator_inv: P::ScalarField,
}

use crate::error::Error;
use crate::fft::Evaluations;
#[rustfmt::skip]
    use ::alloc::vec::Vec;
use bls_12_381::TWO_ADACITY;
use zkstd::behave::*;

impl<P: Pairing> EvaluationDomain<P> {
    /// Construct a domain that is large enough for evaluations of a
    /// polynomial having `num_coeffs` coefficients.
    pub(crate) fn new(num_coeffs: usize) -> Result<Self, Error> {
        // Compute the size of our evaluation domain
        let size = num_coeffs.next_power_of_two() as u64;
        let log_size_of_group = size.trailing_zeros();

        if log_size_of_group >= TWO_ADACITY {
            return Err(Error::InvalidEvalDomainSize {
                log_size_of_group,
                adacity: TWO_ADACITY,
            });
        }

        // Compute the generator for the multiplicative subgroup.
        // It should be 2^(log_size_of_group) root of unity.

        let mut group_gen = P::ScalarField::ROOT_OF_UNITY;
        for _ in log_size_of_group..TWO_ADACITY {
            group_gen = group_gen.square();
        }
        let size_as_field_element = P::ScalarField::from(size);
        let size_inv = size_as_field_element.invert().unwrap();

        Ok(EvaluationDomain {
            size,
            log_size_of_group,
            size_as_field_element,
            size_inv,
            group_gen,
            group_gen_inv: group_gen.invert().unwrap(),
            generator_inv: P::ScalarField::MULTIPLICATIVE_GENERATOR
                .invert()
                .unwrap(),
        })
    }

    /// Return the size of `self`.
    pub(crate) fn size(&self) -> usize {
        self.size as usize
    }

    /// Given that the domain size is `D`  
    /// This function computes the `D` evaluation points for
    /// the vanishing polynomial of degree `n` over a coset
    pub(crate) fn compute_vanishing_poly_over_coset(
        &self,            // domain to evaluate over
        poly_degree: u64, // degree of the vanishing polynomial
    ) -> Evaluations<P> {
        assert!((self.size() as u64) > poly_degree);
        let coset_gen =
            P::ScalarField::MULTIPLICATIVE_GENERATOR.pow(poly_degree);
        let v_h: Vec<_> = (0..self.size())
            .map(|i| {
                (coset_gen * self.group_gen.pow(poly_degree * i as u64))
                    - P::ScalarField::one()
            })
            .collect();
        Evaluations::from_vec_and_domain(v_h, self.clone())
    }
}
