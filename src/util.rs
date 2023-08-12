// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use alloc::vec::Vec;
use zkstd::common::{Pairing, Ring};

/// Returns a vector of BlsScalars of increasing powers of x from x^0 to x^d.
pub(crate) fn powers_of<P: Pairing>(
    scalar: &P::ScalarField,
    max_degree: usize,
) -> Vec<P::ScalarField> {
    let mut powers = Vec::with_capacity(max_degree + 1);
    powers.push(P::ScalarField::one());
    for i in 1..=max_degree {
        powers.push(powers[i - 1] * scalar);
    }
    powers
}
