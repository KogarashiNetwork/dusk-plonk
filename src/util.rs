// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use alloc::vec::Vec;
use rand_core::RngCore;
use zkstd::common::{Group, Pairing, Ring};

#[cfg(feature = "rkyv-impl")]
#[inline(always)]
pub unsafe fn check_field<F, C>(
    field: *const F,
    context: &mut C,
    field_name: &'static str,
) -> Result<(), bytecheck::StructCheckError>
where
    F: bytecheck::CheckBytes<C>,
{
    F::check_bytes(field, context).map_err(|e| {
        bytecheck::StructCheckError {
            field_name,
            inner: bytecheck::ErrorBox::new(e),
        }
    })?;
    Ok(())
}

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

/// Generates a random BlsScalar using a RNG seed.
pub(crate) fn random_scalar<R: RngCore, P: Pairing>(
    rng: &mut R,
) -> P::ScalarField {
    P::ScalarField::random(rng)
}
