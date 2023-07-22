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

// while we do not have batch inversion for scalars
use core::ops::MulAssign;

pub fn batch_inversion<P: Pairing>(v: &mut [P::ScalarField]) {
    // Montgomery’s Trick and Fast Implementation of Masked AES
    // Genelle, Prouff and Quisquater
    // Section 3.2

    // First pass: compute [a, ab, abc, ...]
    let mut prod = Vec::with_capacity(v.len());
    let mut tmp = P::ScalarField::one();
    for f in v.iter().filter(|f| f != &&P::ScalarField::zero()) {
        tmp.mul_assign(f);
        prod.push(tmp);
    }

    // Invert `tmp`.
    tmp = tmp.invert().unwrap(); // Guaranteed to be nonzero.

    // Second pass: iterate backwards to compute inverses
    for (f, s) in v
        .iter_mut()
        // Backwards
        .rev()
        // Ignore normalized elements
        .filter(|f| f != &&P::ScalarField::zero())
        // Backwards, skip last element, fill in one for last term.
        .zip(
            prod.into_iter()
                .rev()
                .skip(1)
                .chain(Some(P::ScalarField::one())),
        )
    {
        // tmp := tmp * f; f := tmp * s = 1/f
        let new_tmp = tmp * *f;
        *f = tmp * s;
        tmp = new_tmp;
    }
}
#[cfg(test)]
mod test {
    use zero_bls12_381::Fr as BlsScalar;
    use zero_pairing::TatePairing;

    use super::*;
    #[test]
    fn test_batch_inversion() {
        let one = BlsScalar::from(1);
        let two = BlsScalar::from(2);
        let three = BlsScalar::from(3);
        let four = BlsScalar::from(4);
        let five = BlsScalar::from(5);

        let original_scalars = vec![one, two, three, four, five];
        let mut inverted_scalars = vec![one, two, three, four, five];

        batch_inversion::<TatePairing>(&mut inverted_scalars);
        for (x, x_inv) in original_scalars.iter().zip(inverted_scalars.iter()) {
            assert_eq!(x.invert().unwrap(), *x_inv);
        }
    }
}
