// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

pub mod ecc;
pub mod logic;
pub mod permutation;
pub mod range;

use crate::fft::Evaluations;
use zksnarks::key::arithmetic;
use zkstd::common::Pairing;

/// PLONK circuit Proving Key.
///
/// This structure is used by the Prover in order to construct a
/// [`Proof`](crate::proof_system::Proof).
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ProverKey<P: Pairing> {
    /// Circuit size
    pub(crate) n: usize,
    /// ProverKey for arithmetic gate
    pub(crate) arithmetic: arithmetic::ProverKey<P::ScalarField>,
    /// ProverKey for logic gate
    pub(crate) logic: logic::ProverKey<P>,
    /// ProverKey for range gate
    pub(crate) range: range::ProverKey<P>,
    /// ProverKey for fixed base curve addition gates
    pub(crate) fixed_base: ecc::scalar_mul::fixed_base::ProverKey<P>,
    /// ProverKey for variable base curve addition gates
    pub(crate) variable_base: ecc::curve_addition::ProverKey<P>,
    /// ProverKey for permutation checks
    pub(crate) permutation: permutation::ProverKey<P>,
    // Pre-processes the 8n Evaluations for the vanishing polynomial, so
    // they do not need to be computed at the proving stage.
    // Note: With this, we can combine all parts of the quotient polynomial
    // in their evaluation phase and divide by the quotient
    // polynomial without having to perform IFFT
    pub(crate) v_h_coset_8n: Evaluations<P>,
}

impl<P: Pairing> ProverKey<P> {
    pub(crate) fn v_h_coset_8n(&self) -> &Evaluations<P> {
        &self.v_h_coset_8n
    }
}
