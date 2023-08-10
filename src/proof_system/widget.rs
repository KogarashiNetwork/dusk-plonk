// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

pub mod permutation;
pub mod range;

use crate::fft::Evaluations;
use zksnarks::key::{arithmetic, curve, logic};
use zkstd::common::Pairing;

/// PLONK circuit Proving Key.
///
/// This structure is used by the Prover in order to construct a
/// [`Proof`](crate::proof_system::Proof).
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ProvingKey<P: Pairing> {
    /// Circuit size
    pub(crate) n: usize,
    /// ProvingKey for arithmetic gate
    pub(crate) arithmetic: arithmetic::ProvingKey<P::ScalarField>,
    /// ProvingKey for logic gate
    pub(crate) logic: logic::ProvingKey<P::ScalarField>,
    /// ProvingKey for range gate
    pub(crate) range: range::ProvingKey<P>,
    /// ProvingKey for fixed base curve addition gates
    pub(crate) fixed_base: curve::scalar::ProvingKey<P>,
    /// ProvingKey for variable base curve addition gates
    pub(crate) variable_base: curve::add::ProvingKey<P>,
    /// ProvingKey for permutation checks
    pub(crate) permutation: permutation::ProvingKey<P>,
    // Pre-processes the 8n Evaluations for the vanishing polynomial, so
    // they do not need to be computed at the proving stage.
    // Note: With this, we can combine all parts of the quotient polynomial
    // in their evaluation phase and divide by the quotient
    // polynomial without having to perform IFFT
    pub(crate) v_h_coset_8n: Evaluations<P>,
}

impl<P: Pairing> ProvingKey<P> {
    pub(crate) fn v_h_coset_8n(&self) -> &Evaluations<P> {
        &self.v_h_coset_8n
    }
}
