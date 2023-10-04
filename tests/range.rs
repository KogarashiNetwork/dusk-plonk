// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use ec_pairing::TatePairing;
use poly_commit::PublicParameters;
use rand::rngs::StdRng;
use rand::SeedableRng;
use zero_plonk::prelude::*;
use zksnarks::plonk::PlonkParams;
use zkstd::behave::{FftField, Group};
use zkstd::common::Pairing;

#[test]
fn range_works() {
    let mut rng = StdRng::seed_from_u64(8349u64);

    let n = 5;
    let label = b"demo";
    let mut pp =
        PlonkParams::<TatePairing>::setup(n, BlsScalar::random(&mut rng));

    const DEFAULT_BITS: usize = 76;
    #[derive(Debug)]
    pub struct DummyCircuit<P: Pairing> {
        a: P::ScalarField,
        bits: usize,
    }

    impl DummyCircuit<TatePairing> {
        pub fn new(a: BlsScalar, bits: usize) -> Self {
            Self { a, bits }
        }
    }

    impl Default for DummyCircuit<TatePairing> {
        fn default() -> Self {
            Self::new(7u64.into(), DEFAULT_BITS)
        }
    }

    impl Circuit<TatePairing> for DummyCircuit<TatePairing> {
        fn circuit(
            &self,
            composer: &mut Builder<TatePairing>,
        ) -> Result<(), Error> {
            let w_a = composer.append_witness(self.a);

            composer.component_range(w_a, self.bits);

            Ok(())
        }
    }

    let (prover, verifier) = Compiler::compile::<
        DummyCircuit<TatePairing>,
        TatePairing,
    >(&mut pp, label)
    .expect("failed to compile circuit");

    // default works
    {
        let a = BlsScalar::from(u64::MAX);

        let (proof, public_inputs) = prover
            .prove(&mut rng, &DummyCircuit::new(a, DEFAULT_BITS))
            .expect("failed to prove");

        verifier
            .verify(&proof, &public_inputs)
            .expect("failed to verify proof");
    }

    // negative works
    {
        let a = -BlsScalar::pow_of_2(DEFAULT_BITS as u64 + 1);

        prover
            .prove(&mut rng, &DummyCircuit::new(a, DEFAULT_BITS))
            .expect_err("bits aren't in range");
    }

    // odd bits won't panic
    {
        let a = BlsScalar::one();

        Compiler::compile_with_circuit::<DummyCircuit<TatePairing>,
    TatePairing>(         &mut pp,
            label,
            &DummyCircuit::new(a, DEFAULT_BITS + 1),
        )
        .expect("failed to compile circuit");
    }
}
