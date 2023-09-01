// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use alloc::vec::Vec;
use core::ops;
use hashbrown::HashMap;
use sp_std::vec;
use zksnarks::{Gate, Witness};
use zkstd::{behave::Group, common::Pairing};

use crate::permutation::Permutation;
use crate::runtime::Runtime;

use super::Composer;

/// Construct and prove circuits
#[derive(Debug, Clone)]
pub struct Builder<P: Pairing> {
    /// Constraint system gates
    pub(crate) constraints: Vec<Gate<P::ScalarField>>,

    /// Sparse representation of the public inputs
    pub(crate) public_inputs: HashMap<usize, P::ScalarField>,

    /// Witness values
    pub(crate) witnesses: Vec<P::ScalarField>,

    /// Permutation argument.
    pub(crate) perm: Permutation<P>,

    /// PLONK runtime controller
    pub(crate) runtime: Runtime<P>,
}

impl<P: Pairing> Builder<P> {
    pub(crate) fn public_input_indexes(&self) -> Vec<usize> {
        let mut public_input_indexes: Vec<_> =
            self.public_inputs.keys().copied().collect();

        public_input_indexes.as_mut_slice().sort();

        public_input_indexes
    }

    pub(crate) fn public_inputs(&self) -> Vec<P::ScalarField> {
        self.public_input_indexes()
            .iter()
            .filter_map(|idx| self.public_inputs.get(idx).copied())
            .collect()
    }

    pub(crate) fn dense_public_inputs(
        public_input_indexes: &[usize],
        public_inputs: &[P::ScalarField],
        size: usize,
    ) -> Vec<P::ScalarField> {
        let mut dense_public_inputs = vec![P::ScalarField::zero(); size];

        public_input_indexes
            .iter()
            .zip(public_inputs.iter())
            .for_each(|(idx, pi)| dense_public_inputs[*idx] = *pi);

        dense_public_inputs
    }
}

impl<P: Pairing> ops::Index<Witness> for Builder<P> {
    type Output = P::ScalarField;

    fn index(&self, w: Witness) -> &Self::Output {
        &self.witnesses[w.index()]
    }
}

impl<P: Pairing> Composer<P> for Builder<P> {
    fn uninitialized(capacity: usize) -> Self {
        Self {
            constraints: Vec::with_capacity(capacity),
            public_inputs: HashMap::new(),
            witnesses: Vec::with_capacity(capacity),
            perm: Permutation::new(),
            runtime: Runtime::with_capacity(capacity),
        }
    }

    fn constraints(&self) -> usize {
        self.constraints.len()
    }

    fn append_witness_internal(&mut self, witness: P::ScalarField) -> Witness {
        let n = self.witnesses.len();

        // Get a new Witness from the permutation
        self.perm.new_witness();

        // Bind the allocated witness
        self.witnesses.push(witness);

        Witness::new(n)
    }

    fn append_custom_gate_internal(
        &mut self,
        constraint: Gate<P::ScalarField>,
    ) {
        let n = self.constraints.len();

        self.constraints.push(constraint);

        match constraint.public_input {
            Some(pi) => {
                self.public_inputs.insert(n, pi);
            }
            _ => {}
        }

        self.perm.add_witnesses_to_map(
            constraint.w_a,
            constraint.w_b,
            constraint.w_o,
            constraint.w_d,
            n,
        );
    }

    fn runtime(&mut self) -> &mut Runtime<P> {
        &mut self.runtime
    }
}
