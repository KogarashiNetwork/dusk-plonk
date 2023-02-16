// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Methods to preprocess the constraint system for use in a proof

use zero_crypto::common::Pairing;
use zero_kzg::Polynomial;

/// Struct that contains all selector and permutation [`Polynomials`]s
pub(crate) struct Polynomials<P: Pairing> {
    // selector polynomials defining arithmetic circuits
    pub(crate) q_m: Polynomial<P::ScalarField>,
    pub(crate) q_l: Polynomial<P::ScalarField>,
    pub(crate) q_r: Polynomial<P::ScalarField>,
    pub(crate) q_o: Polynomial<P::ScalarField>,
    pub(crate) q_c: Polynomial<P::ScalarField>,

    // additional selector for 3-input gates added for efficiency of
    // implementation
    pub(crate) q_4: Polynomial<P::ScalarField>,

    // additional selectors for different kinds of circuits added for
    // efficiency of implementation
    pub(crate) q_arith: Polynomial<P::ScalarField>, // arithmetic circuits
    pub(crate) q_range: Polynomial<P::ScalarField>, // range proofs
    pub(crate) q_logic: Polynomial<P::ScalarField>, // boolean operations
    pub(crate) q_fixed_group_add: Polynomial<P::ScalarField>, // ecc circuits
    pub(crate) q_variable_group_add: Polynomial<P::ScalarField>, // ecc circuits

    // copy permutation polynomials
    pub(crate) s_sigma_1: Polynomial<P::ScalarField>,
    pub(crate) s_sigma_2: Polynomial<P::ScalarField>,
    pub(crate) s_sigma_3: Polynomial<P::ScalarField>,
    pub(crate) s_sigma_4: Polynomial<P::ScalarField>, // for q_4
}
