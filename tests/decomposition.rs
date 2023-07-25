// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use ec_pairing::TatePairing;
use poly_commit::KeyPair;
use rand::rngs::StdRng;
use rand::SeedableRng;
use zero_plonk::prelude::*;
use zkstd::common::*;

#[test]
fn decomposition_works() {
    let mut rng = StdRng::seed_from_u64(8349u64);

    let n = 10;
    let label = b"demo";
    let mut pp = KeyPair::setup(n, BlsScalar::random(&mut rng));

    #[derive(Debug)]
    pub struct DummyCircuit<const N: usize, P: Pairing> {
        a: P::ScalarField,
        bits: [P::ScalarField; N],
    }

    impl<const N: usize> DummyCircuit<N, TatePairing> {
        pub fn new(a: BlsScalar) -> Self {
            let mut bits = [BlsScalar::zero(); N];

            bits.iter_mut()
                .zip(a.to_bits().iter().rev())
                .for_each(|(b, v)| *b = BlsScalar::from(*v as u64));

            Self { a, bits }
        }
    }

    impl<const N: usize> Default for DummyCircuit<N, TatePairing> {
        fn default() -> Self {
            Self::new(BlsScalar::from(23u64))
        }
    }

    impl<const N: usize> Circuit<TatePairing> for DummyCircuit<N, TatePairing> {
        fn circuit<C>(&self, composer: &mut C) -> Result<(), Error>
        where
            C: Composer<TatePairing>,
        {
            let w_a = composer.append_witness(self.a);
            let mut w_bits: [Witness; N] = [C::ZERO; N];

            w_bits
                .iter_mut()
                .zip(self.bits.iter())
                .for_each(|(w, b)| *w = composer.append_witness(*b));

            let w_x: [Witness; N] = composer.component_decomposition(w_a);

            w_bits.iter().zip(w_x.iter()).for_each(|(w, b)| {
                composer.assert_equal(*w, *b);
            });

            Ok(())
        }
    }

    let (prover, verifier) = Compiler::compile::<
        DummyCircuit<256, TatePairing>,
        TatePairing,
    >(&mut pp, label)
    .expect("failed to compile circuit");

    // default works
    {
        let a = BlsScalar::random(&mut rng);

        let (proof, public_inputs) = prover
            .prove(&mut rng, &DummyCircuit::<256, TatePairing>::new(a))
            .expect("failed to prove");

        verifier
            .verify(&proof, &public_inputs)
            .expect("failed to verify proof");
    }

    // negative works
    {
        let a = BlsScalar::random(&mut rng);

        let mut circuit = DummyCircuit::<256, TatePairing>::new(a);

        circuit.bits[10] = circuit.bits[10] ^ BlsScalar::one();

        prover.prove(&mut rng, &circuit).expect_err("invalid proof");
    }
}
