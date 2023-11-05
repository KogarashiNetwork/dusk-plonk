// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use bls_12_381::Fr as BlsScalar;
use ec_pairing::TatePairing;
use jub_jub::JubjubAffine;
use rand::rngs::StdRng;
use rand::SeedableRng;
use zkplonk::{Plonk, PlonkKey};
use zksnarks::circuit::Circuit;
use zksnarks::error::Error;
use zksnarks::keypair::Keypair;
use zksnarks::plonk::PlonkParams;
use zksnarks::public_params::PublicParameters;
use zkstd::common::FftField;

#[test]
fn range_works() {
    let mut rng = StdRng::seed_from_u64(8349u64);

    let n = 5;
    let label = b"demo";
    let mut pp = PlonkParams::<TatePairing>::setup(n, &mut rng);

    const DEFAULT_BITS: usize = 76;
    #[derive(Debug)]
    pub struct DummyCircuit {
        a: BlsScalar,
        bits: usize,
    }

    impl DummyCircuit {
        pub fn new(a: BlsScalar, bits: usize) -> Self {
            Self { a, bits }
        }
    }

    impl Default for DummyCircuit {
        fn default() -> Self {
            Self::new(7u64.into(), DEFAULT_BITS)
        }
    }

    impl Circuit<JubjubAffine> for DummyCircuit {
        type ConstraintSystem = Plonk<JubjubAffine>;
        fn synthesize(
            &self,
            composer: &mut Plonk<JubjubAffine>,
        ) -> Result<(), Error> {
            let w_a = composer.append_witness(self.a);

            composer.component_range(w_a, self.bits);

            Ok(())
        }
    }

    let (prover, verifier) =
        PlonkKey::<TatePairing, JubjubAffine, DummyCircuit>::compile(&mut pp)
            .expect("failed to compile circuit");

    // default works
    {
        let a = BlsScalar::from(u64::MAX);

        let (proof, public_inputs) = prover
            .create_proof(&mut rng, &DummyCircuit::new(a, DEFAULT_BITS))
            .expect("failed to prove");

        verifier
            .verify(&proof, &public_inputs)
            .expect("failed to verify proof");
    }

    // negative works
    {
        let a = -BlsScalar::pow_of_2(DEFAULT_BITS as u64 + 1);

        prover
            .create_proof(&mut rng, &DummyCircuit::new(a, DEFAULT_BITS))
            .expect_err("bits aren't in range");
    }

    // odd bits won't panic
    {
        let a = BlsScalar::one();

        PlonkKey::compile_with_circuit(
            &mut pp,
            label,
            &DummyCircuit::new(a, DEFAULT_BITS + 1),
        )
        .expect("failed to compile circuit");
    }
}
