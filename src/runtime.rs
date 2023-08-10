// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! PLONK runtime controller

use core::marker::PhantomData;
use zksnarks::Witness;
use zkstd::common::Pairing;

use crate::constraint_system::Constraint;

#[cfg(feature = "debug")]
use crate::debugger::Debugger;

/// Runtime events
#[derive(Debug, Clone, Copy)]
pub enum RuntimeEvent<P: Pairing> {
    /// A witness was appended to the constraint system
    WitnessAppended {
        /// Appended witness
        w: Witness,
        /// Witness value
        v: P::ScalarField,
    },

    /// A constraint was appended
    ConstraintAppended {
        /// Appended constraint
        c: Constraint<P>,
    },

    /// The proof construction was finished
    ProofFinished,
}

/// Runtime structure with debugger
#[derive(Debug, Clone)]
pub struct Runtime<P: Pairing> {
    #[cfg(feature = "debug")]
    debugger: Debugger<P>,
    _marker: PhantomData<P>,
}

impl<P: Pairing> Runtime<P> {
    /// Create a new PLONK runtime with the provided capacity
    #[allow(unused_variables)]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            #[cfg(feature = "debug")]
            debugger: Debugger::with_capacity(capacity),
            _marker: PhantomData,
        }
    }

    #[allow(unused_variables)]
    pub(crate) fn event(&mut self, event: RuntimeEvent<P>) {
        #[cfg(feature = "debug")]
        self.debugger.event(event);
    }
}
