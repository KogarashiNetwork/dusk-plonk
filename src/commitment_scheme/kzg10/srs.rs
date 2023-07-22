// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! The Public Parameters can also be referred to as the Structured Reference
//! String (SRS).

#[cfg(feature = "std")]
#[cfg(test)]
mod test {
    use zero_bls12_381::Fr as BlsScalar;
    use zero_pairing::TatePairing;
    use zkstd::behave::FftField;

    use crate::util;

    #[test]
    fn test_powers_of() {
        let x = BlsScalar::from(10u64);
        let degree = 100u64;

        let powers_of_x = util::powers_of::<TatePairing>(&x, degree as usize);

        for (i, x_i) in powers_of_x.iter().enumerate() {
            assert_eq!(*x_i, x.pow(i as u64))
        }

        let last_element = powers_of_x.last().unwrap();
        assert_eq!(*last_element, x.pow(degree))
    }
}
