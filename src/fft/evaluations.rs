// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! A polynomial represented in evaluations form over a domain of size 2^n.

use super::domain::EvaluationDomain;
use core::ops::Index;
use sp_std::vec::Vec;
use zkstd::behave::*;

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
