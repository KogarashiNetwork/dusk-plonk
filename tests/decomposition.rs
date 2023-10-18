// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use ec_pairing::TatePairing;
use rand::rngs::StdRng;
use rand::SeedableRng;
use zero_plonk::prelude::*;
use zksnarks::circuit::Circuit;
use zksnarks::error::Error;
use zksnarks::keypair::Keypair;
use zksnarks::plonk::wire::PrivateWire;
use zksnarks::plonk::PlonkParams;
use zksnarks::public_params::PublicParameters;
use zkstd::common::*;

#[test]
fn decomposition_works() {
    let mut rng = StdRng::seed_from_u64(8349u64);

    let n = 10;
    let mut pp = PlonkParams::<TatePairing>::setup(n, &mut rng);

    #[derive(Debug)]
    pub struct DummyCircuit<const N: usize> {
        a: BlsScalar,
        bits: [BlsScalar; N],
    }

    impl<const N: usize> DummyCircuit<N> {
        pub fn new(a: BlsScalar) -> Self {
            let mut bits = [BlsScalar::zero(); N];

            bits.iter_mut()
                .zip(a.to_bits().iter().rev())
                .for_each(|(b, v)| *b = BlsScalar::from(*v as u64));

            Self { a, bits }
        }
    }

    impl<const N: usize> Default for DummyCircuit<N> {
        fn default() -> Self {
            Self::new(BlsScalar::from(23u64))
        }
    }

    impl<const N: usize> Circuit<JubjubAffine> for DummyCircuit<N> {
        type ConstraintSystem = Plonk<JubjubAffine>;
        fn synthesize(
            &self,
            composer: &mut Plonk<JubjubAffine>,
        ) -> Result<(), Error> {
            let w_a = composer.append_witness(self.a);
            let mut w_bits: [PrivateWire; N] = [Plonk::<JubjubAffine>::ZERO; N];

            w_bits
                .iter_mut()
                .zip(self.bits.iter())
                .for_each(|(w, b)| *w = composer.append_witness(*b));

            let w_x: [PrivateWire; N] = composer.component_decomposition(w_a);

            w_bits.iter().zip(w_x.iter()).for_each(|(w, b)| {
                composer.assert_equal(*w, *b);
            });

            Ok(())
        }
    }

    let (prover, verifier) =
        PlonkKey::<TatePairing, DummyCircuit<256>>::compile(&mut pp)
            .expect("failed to compile circuit");

    // default works
    {
        let a = BlsScalar::random(&mut rng);

        let (proof, public_inputs) = prover
            .create_proof(&mut rng, &DummyCircuit::<256>::new(a))
            .expect("failed to prove");

        verifier
            .verify(&proof, &public_inputs)
            .expect("failed to verify proof");
    }

    // negative works
    {
        let a = BlsScalar::random(&mut rng);

        let mut circuit = DummyCircuit::<256>::new(a);

        circuit.bits[10] = circuit.bits[10] ^ BlsScalar::one();

        prover
            .create_proof(&mut rng, &circuit)
            .expect_err("invalid proof");
    }
}
