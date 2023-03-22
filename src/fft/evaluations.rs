// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! A polynomial represented in evaluations form over a domain of size 2^n.

use super::domain::EvaluationDomain;
use core::ops::{
    Add, AddAssign, DivAssign, Index, Mul, MulAssign, Sub, SubAssign,
};
use sp_std::vec::Vec;
use zero_crypto::behave::*;

/// Stores a polynomial in evaluation form.
#[derive(PartialEq, Eq, Debug, Clone)]
pub(crate) struct Evaluations<P: Pairing> {
    /// The evaluations of a polynomial over the domain `D`
    pub(crate) evals: Vec<P::ScalarField>,
    // FIXME: We should probably remove this and make it an external object.
    #[doc(hidden)]
    domain: EvaluationDomain<P>,
}

impl<P: Pairing> Evaluations<P> {
    /// Construct `Self` from evaluations and a domain.
    pub(crate) const fn from_vec_and_domain(
        evals: Vec<P::ScalarField>,
        domain: EvaluationDomain<P>,
    ) -> Self {
        Self { evals, domain }
    }
}

impl<P: Pairing> Index<usize> for Evaluations<P> {
    type Output = P::ScalarField;

    fn index(&self, index: usize) -> &P::ScalarField {
        &self.evals[index]
    }
}

impl<'a, 'b, P: Pairing> Mul<&'a Evaluations<P>> for &'b Evaluations<P> {
    type Output = Evaluations<P>;

    #[inline]
    fn mul(self, other: &'a Evaluations<P>) -> Evaluations<P> {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl<'a, P: Pairing> MulAssign<&'a Evaluations<P>> for Evaluations<P> {
    #[inline]
    fn mul_assign(&mut self, other: &'a Evaluations<P>) {
        assert_eq!(self.domain, other.domain, "domains are unequal");
        self.evals
            .iter_mut()
            .zip(&other.evals)
            .for_each(|(a, b)| *a *= b);
    }
}

impl<'a, 'b, P: Pairing> Add<&'a Evaluations<P>> for &'b Evaluations<P> {
    type Output = Evaluations<P>;

    #[inline]
    fn add(self, other: &'a Evaluations<P>) -> Evaluations<P> {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl<'a, P: Pairing> AddAssign<&'a Evaluations<P>> for Evaluations<P> {
    #[inline]
    fn add_assign(&mut self, other: &'a Evaluations<P>) {
        assert_eq!(self.domain, other.domain, "domains are unequal");
        self.evals
            .iter_mut()
            .zip(&other.evals)
            .for_each(|(a, b)| *a += b);
    }
}

impl<'a, 'b, P: Pairing> Sub<&'a Evaluations<P>> for &'b Evaluations<P> {
    type Output = Evaluations<P>;

    #[inline]
    fn sub(self, other: &'a Evaluations<P>) -> Evaluations<P> {
        let mut result = self.clone();
        result -= other;
        result
    }
}

impl<'a, P: Pairing> SubAssign<&'a Evaluations<P>> for Evaluations<P> {
    #[inline]
    fn sub_assign(&mut self, other: &'a Evaluations<P>) {
        assert_eq!(self.domain, other.domain, "domains are unequal");
        self.evals
            .iter_mut()
            .zip(&other.evals)
            .for_each(|(a, b)| *a -= b);
    }
}

impl<'a, P: Pairing> DivAssign<&'a Evaluations<P>> for Evaluations<P> {
    #[inline]
    fn div_assign(&mut self, other: &'a Evaluations<P>) {
        assert_eq!(self.domain, other.domain, "domains are unequal");
        self.evals
            .iter_mut()
            .zip(&other.evals)
            .for_each(|(a, b)| *a *= b.invert().unwrap());
    }
}
