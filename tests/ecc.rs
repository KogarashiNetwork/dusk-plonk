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
use zksnarks::plonk::PlonkParams;
use zksnarks::public_params::PublicParameters;
use zkstd::common::CurveGroup;
use zkstd::common::Group;

#[test]
fn mul_generator_works() {
    let mut rng = StdRng::seed_from_u64(8349u64);

    let n = 9;
    let mut pp = PlonkParams::setup(n, &mut rng);
    #[derive(Debug)]
    pub struct DummyCircuit {
        a: BlsScalar,
        b: JubjubAffine,
    }

    impl DummyCircuit {
        pub fn new(a: BlsScalar) -> Self {
            Self {
                a,
                b: (JubjubAffine::ADDITIVE_GENERATOR * a).into(),
            }
        }
    }

    impl Default for DummyCircuit {
        fn default() -> Self {
            Self::new(BlsScalar::from(7u64))
        }
    }

    impl Circuit<JubjubAffine> for DummyCircuit {
        type ConstraintSystem = Plonk<JubjubAffine>;
        fn synthesize(
            &self,
            composer: &mut Plonk<JubjubAffine>,
        ) -> Result<(), Error> {
            let w_a = composer.append_witness(self.a);
            let w_b = composer.append_point(self.b);
            let w_x = composer.component_mul_generator(
                w_a,
                JubjubAffine::ADDITIVE_GENERATOR,
            )?;

            composer.assert_equal_point(w_b, w_x);

            Ok(())
        }
    }

    let (prover, verifier) =
        PlonkKey::<TatePairing, DummyCircuit>::new(&mut pp)
            .expect("failed to compile circuit");

    // default works
    {
        let a = BlsScalar::random(&mut rng);
        let (proof, public_inputs) = prover
            .create_proof(&mut rng, &DummyCircuit::new(a))
            .expect("failed to prove");

        verifier
            .verify(&proof, &public_inputs)
            .expect("failed to verify proof");
    }

    // negative check
    {
        let a = BlsScalar::from(7u64);
        let b: JubjubAffine = (JubjubAffine::ADDITIVE_GENERATOR * a).into();

        let x = BlsScalar::from(8u64);
        let y = (JubjubAffine::ADDITIVE_GENERATOR * x).into();

        assert_ne!(b, y);

        prover
            .create_proof(&mut rng, &DummyCircuit { a, b: y })
            .expect_err("invalid ecc proof isn't feasible");
    }

    // invalid jubjub won't panic
    {
        let a = -BlsScalar::one();
        let a = BlsScalar::to_mont_form(a.0);

        let x = BlsScalar::from(8u64);
        let y = (JubjubAffine::ADDITIVE_GENERATOR * x).into();

        prover
            .create_proof(&mut rng, &DummyCircuit { a, b: y })
            .expect_err("invalid ecc proof isn't feasible");
    }
}

#[test]
fn add_point_works() {
    let mut rng = StdRng::seed_from_u64(8349u64);

    let n = 4;
    let mut pp = PlonkParams::<TatePairing>::setup(n, &mut rng);
    #[derive(Debug)]
    pub struct DummyCircuit {
        a: JubjubAffine,
        b: JubjubAffine,
        c: JubjubAffine,
    }

    impl DummyCircuit {
        pub fn new(a: &BlsScalar, b: &BlsScalar) -> Self {
            let a: JubjubAffine =
                (JubjubAffine::ADDITIVE_GENERATOR * *a).into();
            let b: JubjubAffine =
                (JubjubAffine::ADDITIVE_GENERATOR * *b).into();
            let c: JubjubAffine = (a + b).into();

            Self { a, b, c }
        }
    }

    impl Default for DummyCircuit {
        fn default() -> Self {
            Self::new(&BlsScalar::from(7u64), &BlsScalar::from(8u64))
        }
    }

    impl Circuit<JubjubAffine> for DummyCircuit {
        type ConstraintSystem = Plonk<JubjubAffine>;
        fn synthesize(
            &self,
            composer: &mut Plonk<JubjubAffine>,
        ) -> Result<(), Error> {
            let w_a = composer.append_point(self.a);
            let w_b = composer.append_point(self.b);
            let w_c = composer.append_point(self.c);

            let w_x = composer.component_add_point(w_a, w_b);

            composer.assert_equal_point(w_c, w_x);

            Ok(())
        }
    }

    let (prover, verifier) =
        PlonkKey::<TatePairing, DummyCircuit>::new(&mut pp)
            .expect("failed to compile circuit");

    // default works
    {
        let a = BlsScalar::random(&mut rng);
        let b = BlsScalar::random(&mut rng);

        let (proof, public_inputs) = prover
            .create_proof(&mut rng, &DummyCircuit::new(&a, &b))
            .expect("failed to prove");

        verifier
            .verify(&proof, &public_inputs)
            .expect("failed to verify proof");
    }

    // identity works
    {
        let a = BlsScalar::random(&mut rng);
        let a = (JubjubAffine::ADDITIVE_GENERATOR * a).into();

        let (proof, public_inputs) = prover
            .create_proof(
                &mut rng,
                &DummyCircuit {
                    a,
                    b: JubjubAffine::ADDITIVE_IDENTITY,
                    c: a,
                },
            )
            .expect("failed to prove");

        verifier
            .verify(&proof, &public_inputs)
            .expect("failed to verify proof");
    }

    // zero works
    {
        let (proof, public_inputs) = prover
            .create_proof(
                &mut rng,
                &DummyCircuit {
                    a: JubjubAffine::ADDITIVE_IDENTITY,
                    b: JubjubAffine::ADDITIVE_IDENTITY,
                    c: JubjubAffine::ADDITIVE_IDENTITY,
                },
            )
            .expect("failed to prove");

        verifier
            .verify(&proof, &public_inputs)
            .expect("failed to verify proof");
    }

    // negative check
    {
        let a = BlsScalar::from(7u64);
        let a: JubjubAffine = (JubjubAffine::ADDITIVE_GENERATOR * a).into();

        let b = BlsScalar::from(8u64);
        let b: JubjubAffine = (JubjubAffine::ADDITIVE_GENERATOR * b).into();

        let c = BlsScalar::from(9u64);
        let c: JubjubAffine = (JubjubAffine::ADDITIVE_GENERATOR * c).into();

        assert_ne!(c, (a + b).into());

        prover
            .create_proof(&mut rng, &DummyCircuit { a, b, c })
            .expect_err("invalid ecc proof isn't feasible");
    }
}

#[test]
fn mul_point_works() {
    let mut rng = StdRng::seed_from_u64(8349u64);

    let n = 13;
    let mut pp = PlonkParams::<TatePairing>::setup(n, &mut rng);
    #[derive(Debug)]
    pub struct DummyCircuit {
        a: BlsScalar,
        b: JubjubAffine,
        c: JubjubAffine,
    }

    impl DummyCircuit {
        pub fn new(a: BlsScalar, b: JubjubAffine) -> Self {
            let c = (b * a).into();

            Self { a, b, c }
        }
    }

    impl Default for DummyCircuit {
        fn default() -> Self {
            let b = BlsScalar::from(8u64);
            let b = (JubjubAffine::ADDITIVE_GENERATOR * b).into();

            Self::new(BlsScalar::from(7u64), b)
        }
    }

    impl Circuit<JubjubAffine> for DummyCircuit {
        type ConstraintSystem = Plonk<JubjubAffine>;
        fn synthesize(
            &self,
            composer: &mut Plonk<JubjubAffine>,
        ) -> Result<(), Error> {
            let w_a = composer.append_witness(self.a);
            let w_b = composer.append_point(self.b);
            let w_c = composer.append_point(self.c);

            let w_x = composer.component_mul_point(w_a, w_b);

            composer.assert_equal_point(w_c, w_x);

            Ok(())
        }
    }

    let (prover, verifier) =
        PlonkKey::<TatePairing, DummyCircuit>::new(&mut pp)
            .expect("failed to compile circuit");

    // default works
    {
        let a = BlsScalar::random(&mut rng);
        let b = BlsScalar::random(&mut rng);
        let b = (JubjubAffine::ADDITIVE_GENERATOR * b).into();

        let (proof, public_inputs) = prover
            .create_proof(&mut rng, &DummyCircuit::new(a, b))
            .expect("failed to prove");

        verifier
            .verify(&proof, &public_inputs)
            .expect("failed to verify proof");
    }

    // negative works
    {
        let a = BlsScalar::random(&mut rng);
        let b = BlsScalar::random(&mut rng);
        let b = (JubjubAffine::ADDITIVE_GENERATOR * b).into();
        let c = b * a;

        let x = BlsScalar::random(&mut rng);
        let x = JubjubAffine::ADDITIVE_GENERATOR * x;

        assert_ne!(c, x);

        prover
            .create_proof(&mut rng, &DummyCircuit { a, b, c: x.into() })
            .expect_err("circuit is not satisfied");
    }
}
