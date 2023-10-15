// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use ec_pairing::TatePairing;
use jub_jub::JubjubAffine;
use rand::rngs::StdRng;
use rand::SeedableRng;
use zero_plonk::prelude::*;
use zksnarks::circuit::Circuit;
use zksnarks::error::Error;
use zksnarks::keypair::Keypair;
use zksnarks::plonk::PlonkParams;
use zksnarks::public_params::PublicParameters;
use zkstd::common::{CurveGroup, Group, Pairing};

#[test]
fn boolean_works() {
    let mut rng = StdRng::seed_from_u64(8349u64);

    let n = 4;
    let mut pp = PlonkParams::<TatePairing>::setup(n, &mut rng);

    #[derive(Debug)]
    pub struct DummyCircuit<P: Pairing> {
        a: P::ScalarField,
    }

    impl DummyCircuit<TatePairing> {
        pub fn new(a: BlsScalar) -> Self {
            Self { a }
        }
    }

    impl Default for DummyCircuit<TatePairing> {
        fn default() -> Self {
            Self::new(1u64.into())
        }
    }

    impl Circuit<JubjubAffine> for DummyCircuit<TatePairing> {
        type ConstraintSystem = Plonk<JubjubAffine>;
        fn synthesize(
            &self,
            composer: &mut Plonk<JubjubAffine>,
        ) -> Result<(), Error> {
            let w_a = composer.append_witness(self.a);

            composer.component_boolean(w_a);

            Ok(())
        }
    }

    let (prover, verifier) =
        PlonkKey::<TatePairing, DummyCircuit<TatePairing>>::new(&mut pp)
            .expect("failed to compile circuit");

    // default works
    {
        let a = BlsScalar::one();

        let (proof, public_inputs) = prover
            .create_proof(&mut rng, &DummyCircuit::new(a))
            .expect("failed to prove");

        verifier
            .verify(&proof, &public_inputs)
            .expect("failed to verify proof");

        let a = BlsScalar::zero();

        let (proof, public_inputs) = prover
            .create_proof(&mut rng, &DummyCircuit::new(a))
            .expect("failed to prove");

        verifier
            .verify(&proof, &public_inputs)
            .expect("failed to verify proof");
    }

    // negative works
    {
        let a = BlsScalar::from(2u64);

        prover
            .create_proof(&mut rng, &DummyCircuit::new(a))
            .expect_err("invalid circuit");
    }
}

#[test]
fn select_works() {
    let mut rng = StdRng::seed_from_u64(8349u64);

    let n = 6;
    let mut pp = PlonkParams::<TatePairing>::setup(n, &mut rng);

    #[derive(Clone, Debug)]
    pub struct DummyCircuit<P: Pairing> {
        bit: P::ScalarField,
        a: P::ScalarField,
        b: P::ScalarField,
        res: P::ScalarField,

        zero_bit: P::ScalarField,
        zero_a: P::ScalarField,
        zero_res: P::ScalarField,

        one_bit: P::ScalarField,
        one_a: P::ScalarField,
        one_res: P::ScalarField,

        point_bit: P::ScalarField,
        point_a: P::JubjubExtended,
        point_b: P::JubjubExtended,
        point_res: P::JubjubExtended,

        identity_bit: P::ScalarField,
        identity_a: P::JubjubExtended,
        identity_res: P::JubjubExtended,
    }

    impl DummyCircuit<TatePairing> {
        #[allow(clippy::too_many_arguments)]
        pub fn new(
            bit: BlsScalar,
            a: BlsScalar,
            b: BlsScalar,
            zero_bit: BlsScalar,
            zero_a: BlsScalar,
            one_bit: BlsScalar,
            one_a: BlsScalar,
            point_bit: BlsScalar,
            point_a: JubjubExtended,
            point_b: JubjubExtended,
            identity_bit: BlsScalar,
            identity_a: JubjubExtended,
        ) -> Self {
            let res = if bit == BlsScalar::one() { a } else { b };

            let zero_res = if zero_bit == BlsScalar::one() {
                zero_a
            } else {
                BlsScalar::zero()
            };

            let one_res = if one_bit == BlsScalar::one() {
                one_a
            } else {
                BlsScalar::one()
            };

            let point_res = if one_bit == BlsScalar::one() {
                point_a
            } else {
                point_b
            };

            let identity_res = if identity_bit == BlsScalar::one() {
                identity_a
            } else {
                JubjubExtended::ADDITIVE_IDENTITY
            };

            Self {
                bit,
                a,
                b,
                res,
                zero_bit,
                zero_a,
                zero_res,
                one_bit,
                one_a,
                one_res,
                point_bit,
                point_a,
                point_b,
                point_res,
                identity_bit,
                identity_a,
                identity_res,
            }
        }
    }

    impl Default for DummyCircuit<TatePairing> {
        fn default() -> Self {
            let bit = BlsScalar::one();
            let a = BlsScalar::from(3u64);
            let b = BlsScalar::from(5u64);
            let zero_bit = BlsScalar::zero();
            let zero_a = BlsScalar::from(7u64);
            let one_bit = BlsScalar::one();
            let one_a = BlsScalar::from(11u64);
            let point_bit = BlsScalar::zero();
            let point_a =
                JubjubExtended::ADDITIVE_GENERATOR * JubjubScalar::from(13u64);
            let point_b =
                JubjubExtended::ADDITIVE_GENERATOR * JubjubScalar::from(17u64);
            let identity_bit = BlsScalar::one();
            let identity_a =
                JubjubExtended::ADDITIVE_GENERATOR * JubjubScalar::from(19u64);

            Self::new(
                bit,
                a,
                b,
                zero_bit,
                zero_a,
                one_bit,
                one_a,
                point_bit,
                point_a,
                point_b,
                identity_bit,
                identity_a,
            )
        }
    }

    impl Circuit<JubjubAffine> for DummyCircuit<TatePairing> {
        type ConstraintSystem = Plonk<JubjubAffine>;
        fn synthesize(
            &self,
            composer: &mut Plonk<JubjubAffine>,
        ) -> Result<(), Error> {
            let w_bit = composer.append_witness(self.bit);
            let w_a = composer.append_witness(self.a);
            let w_b = composer.append_witness(self.b);
            let w_res = composer.append_witness(self.res);
            let w_zero_bit = composer.append_witness(self.zero_bit);
            let w_zero_a = composer.append_witness(self.zero_a);
            let w_zero_res = composer.append_witness(self.zero_res);
            let w_one_bit = composer.append_witness(self.one_bit);
            let w_one_a = composer.append_witness(self.one_a);
            let w_one_res = composer.append_witness(self.one_res);
            let w_point_bit = composer.append_witness(self.point_bit);
            let w_point_a = composer.append_point(self.point_a);
            let w_point_b = composer.append_point(self.point_b);
            let w_point_res = composer.append_point(self.point_res);
            let w_identity_bit = composer.append_witness(self.identity_bit);
            let w_identity_a = composer.append_point(self.identity_a);
            let w_identity_res = composer.append_point(self.identity_res);

            let w_x = composer.component_select(w_bit, w_a, w_b);
            composer.assert_equal(w_x, w_res);

            let w_zero_x = composer.component_select_zero(w_zero_bit, w_zero_a);
            composer.assert_equal(w_zero_x, w_zero_res);

            let w_one_x = composer.component_select_one(w_one_bit, w_one_a);
            composer.assert_equal(w_one_x, w_one_res);

            let w_point_x = composer.component_select_point(
                w_point_bit,
                w_point_a,
                w_point_b,
            );
            composer.assert_equal_point(w_point_x, w_point_res);

            let w_identity_x = composer
                .component_select_identity(w_identity_bit, w_identity_a);
            composer.assert_equal_point(w_identity_x, w_identity_res);

            Ok(())
        }
    }

    let (prover, verifier): (Prover<TatePairing>, Verifier<TatePairing>) =
        PlonkKey::<TatePairing, DummyCircuit<TatePairing>>::new(&mut pp)
            .expect("failed to compile circuit");

    // default works
    {
        let bit = BlsScalar::one();

        let a = BlsScalar::random(&mut rng);
        let b = BlsScalar::random(&mut rng);
        let zero_bit = bit;
        let zero_a = BlsScalar::random(&mut rng);
        let one_bit = bit;
        let one_a = BlsScalar::random(&mut rng);
        let point_bit = bit;
        let point_a = JubjubScalar::random(&mut rng);
        let point_a = JubjubExtended::ADDITIVE_GENERATOR * point_a;
        let point_b = JubjubScalar::random(&mut rng);
        let point_b = JubjubExtended::ADDITIVE_GENERATOR * point_b;
        let identity_bit = bit;
        let identity_a = JubjubScalar::random(&mut rng);
        let identity_a = JubjubExtended::ADDITIVE_GENERATOR * identity_a;

        let circuit = DummyCircuit::new(
            bit,
            a,
            b,
            zero_bit,
            zero_a,
            one_bit,
            one_a,
            point_bit,
            point_a,
            point_b,
            identity_bit,
            identity_a,
        );

        let (proof, public_inputs) = prover
            .create_proof(&mut rng, &circuit)
            .expect("failed to prove");

        verifier
            .verify(&proof, &public_inputs)
            .expect("failed to verify proof");

        let bit = BlsScalar::zero();

        let a = BlsScalar::random(&mut rng);
        let b = BlsScalar::random(&mut rng);
        let zero_bit = bit;
        let zero_a = BlsScalar::random(&mut rng);
        let one_bit = bit;
        let one_a = BlsScalar::random(&mut rng);
        let point_bit = bit;
        let point_a = JubjubScalar::random(&mut rng);
        let point_a = JubjubExtended::ADDITIVE_GENERATOR * point_a;
        let point_b = JubjubScalar::random(&mut rng);
        let point_b = JubjubExtended::ADDITIVE_GENERATOR * point_b;
        let identity_bit = bit;
        let identity_a = JubjubScalar::random(&mut rng);
        let identity_a = JubjubExtended::ADDITIVE_GENERATOR * identity_a;

        let circuit = DummyCircuit::new(
            bit,
            a,
            b,
            zero_bit,
            zero_a,
            one_bit,
            one_a,
            point_bit,
            point_a,
            point_b,
            identity_bit,
            identity_a,
        );

        let (proof, public_inputs) = prover
            .create_proof(&mut rng, &circuit)
            .expect("failed to prove");

        verifier
            .verify(&proof, &public_inputs)
            .expect("failed to verify proof");
    }

    let bit = BlsScalar::one();

    let a = BlsScalar::random(&mut rng);
    let b = BlsScalar::random(&mut rng);
    let zero_bit = bit;
    let zero_a = BlsScalar::random(&mut rng);
    let one_bit = bit;
    let one_a = BlsScalar::random(&mut rng);
    let point_bit = bit;
    let point_a = JubjubScalar::random(&mut rng);
    let point_a = JubjubExtended::ADDITIVE_GENERATOR * point_a;
    let point_b = JubjubScalar::random(&mut rng);
    let point_b = JubjubExtended::ADDITIVE_GENERATOR * point_b;
    let identity_bit = bit;
    let identity_a = JubjubScalar::random(&mut rng);
    let identity_a = JubjubExtended::ADDITIVE_GENERATOR * identity_a;

    let base = DummyCircuit::new(
        bit,
        a,
        b,
        zero_bit,
        zero_a,
        one_bit,
        one_a,
        point_bit,
        point_a,
        point_b,
        identity_bit,
        identity_a,
    );

    // negative select works
    {
        let mut circuit = base.clone();

        circuit.res = -circuit.res;

        prover
            .create_proof(&mut rng, &circuit)
            .expect_err("invalid proof");
    }

    // negative select zero works
    {
        let mut circuit = base.clone();

        circuit.zero_res = -circuit.zero_res;

        prover
            .create_proof(&mut rng, &circuit)
            .expect_err("invalid proof");
    }

    // negative select one works
    {
        let mut circuit = base.clone();

        circuit.one_res = -circuit.one_res;

        prover
            .create_proof(&mut rng, &circuit)
            .expect_err("invalid proof");
    }

    // negative select point works
    {
        let mut circuit = base.clone();

        let x = JubjubExtended::ADDITIVE_GENERATOR * JubjubScalar::one();

        circuit.point_res += x;

        prover
            .create_proof(&mut rng, &circuit)
            .expect_err("invalid proof");
    }

    // negative select identity works
    {
        let mut circuit = base;

        let x = JubjubExtended::ADDITIVE_GENERATOR * JubjubScalar::one();

        circuit.identity_res += x;

        prover
            .create_proof(&mut rng, &circuit)
            .expect_err("invalid proof");
    }
}
