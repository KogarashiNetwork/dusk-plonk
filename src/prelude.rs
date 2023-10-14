// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Collection of functions needed to use plonk library.
//!
//! Use this as the only import that you need to interact
//! with the principal data structures of the plonk library.

pub use crate::{
    constraint_system::{
        Circuit, Compiler, ConstraintSystem, Prover, Verifier,
    },
    gadget::WitnessPoint,
};

pub use crate::prover::Proof;
pub use bls_12_381::Fr as BlsScalar;
pub use jub_jub::{Fp as JubjubScalar, JubjubAffine, JubjubExtended};
pub use zksnarks::error::Error;
pub use zksnarks::Constraint;
