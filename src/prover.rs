// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

mod linearization_poly;
mod proof;
mod quotient_poly;

use crate::constraint_system::{Circuit, ConstraintSystem};
pub use proof::Proof;
use zksnarks::error::Error;

use core::marker::PhantomData;
use core::ops;
use poly_commit::{Coefficients, Fft, PointsValue};
use rand_core::RngCore;
use sp_std::vec;
use zksnarks::plonk::{
    PlonkParams, ProvingKey, Transcript, TranscriptProtocol, VerificationKey,
};
use zkstd::behave::{FftField, Group, Pairing};
use zkstd::common::Vec;

/// Turbo Prover with processed keys
#[derive(Clone)]
pub struct Prover<C, P>
where
    C: Circuit<P>,
    P: Pairing,
{
    pub(crate) prover_key: ProvingKey<P>,
    pub(crate) keypair: PlonkParams<P>,
    pub(crate) transcript: Transcript,
    pub(crate) size: usize,
    pub(crate) constraints: usize,
    circuit: PhantomData<C>,
    pairing: PhantomData<P>,
}

impl<C, P> ops::Deref for Prover<C, P>
where
    C: Circuit<P>,
    P: Pairing,
{
    type Target = ProvingKey<P>;

    fn deref(&self) -> &Self::Target {
        &self.prover_key
    }
}

impl<C, P> Prover<C, P>
where
    C: Circuit<P>,
    P: Pairing,
{
    pub(crate) fn new(
        label: Vec<u8>,
        keypair: PlonkParams<P>,
        prover_key: ProvingKey<P>,
        verifier_key: VerificationKey<P>,
        size: usize,
        constraints: usize,
    ) -> Self {
        let transcript =
            Transcript::base(label.as_slice(), &verifier_key, constraints);

        Self {
            prover_key,
            keypair,
            transcript,
            size,
            constraints,
            circuit: PhantomData,
            pairing: PhantomData,
        }
    }

    /// Prove the circuit
    pub fn create_proof<R>(
        &self,
        rng: &mut R,
        circuit: &C,
    ) -> Result<(Proof<P>, Vec<P::ScalarField>), Error>
    where
        C: Circuit<P>,
        R: RngCore,
    {
        let mut prover = ConstraintSystem::initialized(self.constraints);

        circuit.synthesize(&mut prover)?;

        let size = self.size;
        let k = size.trailing_zeros();

        let fft = Fft::<P::ScalarField>::new(k as usize);

        let mut transcript = self.transcript.clone();

        let public_inputs = prover.public_inputs();
        let public_input_indexes = prover.public_input_indexes();
        let dense_public_inputs =
            PointsValue::new(ConstraintSystem::<P>::dense_public_inputs(
                &public_input_indexes,
                &public_inputs,
                self.size,
            ));

        public_inputs.iter().for_each(|pi| {
            <Transcript as TranscriptProtocol<P>>::append_scalar(
                &mut transcript,
                b"pi",
                pi,
            )
        });

        // round 1
        // convert wires to padded scalars
        let mut a_w_scalar = PointsValue(vec![P::ScalarField::zero(); size]);
        let mut b_w_scalar = PointsValue(vec![P::ScalarField::zero(); size]);
        let mut o_w_scalar = PointsValue(vec![P::ScalarField::zero(); size]);
        let mut d_w_scalar = PointsValue(vec![P::ScalarField::zero(); size]);

        prover.constraints.iter().enumerate().for_each(|(i, c)| {
            a_w_scalar.0[i] = prover[c.w_a];
            b_w_scalar.0[i] = prover[c.w_b];
            o_w_scalar.0[i] = prover[c.w_o];
            d_w_scalar.0[i] = prover[c.w_d];
        });

        let mut a_w_poly = fft.idft(a_w_scalar.clone());
        let mut b_w_poly = fft.idft(b_w_scalar.clone());
        let mut o_w_poly = fft.idft(o_w_scalar.clone());
        let mut d_w_poly = fft.idft(d_w_scalar.clone());

        a_w_poly.blind(1, rng);
        b_w_poly.blind(1, rng);
        o_w_poly.blind(1, rng);
        d_w_poly.blind(1, rng);

        // commit to wire polynomials
        // ([a(x)]_1, [b(x)]_1, [c(x)]_1, [d(x)]_1)
        let a_w_poly_commit = self.keypair.commit(&a_w_poly)?;
        let b_w_poly_commit = self.keypair.commit(&b_w_poly)?;
        let o_w_poly_commit = self.keypair.commit(&o_w_poly)?;
        let d_w_poly_commit = self.keypair.commit(&d_w_poly)?;

        // Add wire polynomial commitments to transcript
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            &mut transcript,
            b"a_w",
            &a_w_poly_commit,
        );
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            &mut transcript,
            b"b_w",
            &b_w_poly_commit,
        );
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            &mut transcript,
            b"c_w",
            &o_w_poly_commit,
        );
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            &mut transcript,
            b"d_w",
            &d_w_poly_commit,
        );

        // round 2
        // permutation challenges
        let beta = <Transcript as TranscriptProtocol<P>>::challenge_scalar(
            &mut transcript,
            b"beta",
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"beta",
            &beta,
        );

        let gamma = <Transcript as TranscriptProtocol<P>>::challenge_scalar(
            &mut transcript,
            b"gamma",
        );
        let sigma = [
            self.prover_key.permutation.s_sigma_1.0.clone(),
            self.prover_key.permutation.s_sigma_2.0.clone(),
            self.prover_key.permutation.s_sigma_3.0.clone(),
            self.prover_key.permutation.s_sigma_4.0.clone(),
        ];
        let wires = [
            a_w_scalar.0.as_slice(),
            b_w_scalar.0.as_slice(),
            o_w_scalar.0.as_slice(),
            d_w_scalar.0.as_slice(),
        ];
        let permutation = prover
            .perm
            .compute_permutation_vec(&fft, wires, &beta, &gamma, sigma);

        let mut z_poly = fft.idft(PointsValue(permutation));
        z_poly.blind(2, rng);
        let z_poly_commit = self.keypair.commit(&z_poly)?;
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            &mut transcript,
            b"z",
            &z_poly_commit,
        );

        // round 3
        // compute quotient challenge alpha
        let alpha = <Transcript as TranscriptProtocol<P>>::challenge_scalar(
            &mut transcript,
            b"alpha",
        );
        let range_sep_challenge =
            <Transcript as TranscriptProtocol<P>>::challenge_scalar(
                &mut transcript,
                b"range separation challenge",
            );
        let logic_sep_challenge =
            <Transcript as TranscriptProtocol<P>>::challenge_scalar(
                &mut transcript,
                b"logic separation challenge",
            );
        let curve_scalar_sep_challenge =
            <Transcript as TranscriptProtocol<P>>::challenge_scalar(
                &mut transcript,
                b"fixed base separation challenge",
            );
        let var_base_sep_challenge =
            <Transcript as TranscriptProtocol<P>>::challenge_scalar(
                &mut transcript,
                b"variable base separation challenge",
            );

        // compute public inputs polynomial
        let pi_poly = fft.idft(dense_public_inputs);

        // compute quotient polynomial
        let wires = (&a_w_poly, &b_w_poly, &o_w_poly, &d_w_poly);
        let args = &(
            alpha,
            beta,
            gamma,
            range_sep_challenge,
            logic_sep_challenge,
            curve_scalar_sep_challenge,
            var_base_sep_challenge,
        );
        let t_poly = quotient_poly::compute(
            &fft,
            &self.prover_key,
            &z_poly,
            wires,
            &pi_poly,
            args,
        )?;

        // split quotient polynomial into 4 degree `n` polynomials
        let domain_size = fft.size();
        let t_low_poly = Coefficients::new(t_poly[0..domain_size].to_vec());
        let t_mid_poly =
            Coefficients::new(t_poly[domain_size..2 * domain_size].to_vec());
        let t_high_poly = Coefficients::new(
            t_poly[2 * domain_size..3 * domain_size].to_vec(),
        );
        let t_4_poly = Coefficients::new(t_poly[3 * domain_size..].to_vec());

        // commit to split quotient polynomial
        let t_low_commit = self.keypair.commit(&t_low_poly)?;
        let t_mid_commit = self.keypair.commit(&t_mid_poly)?;
        let t_high_commit = self.keypair.commit(&t_high_poly)?;
        let t_4_commit = self.keypair.commit(&t_4_poly)?;

        // add quotient polynomial commitments to transcript
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            &mut transcript,
            b"t_low",
            &t_low_commit,
        );
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            &mut transcript,
            b"t_mid",
            &t_mid_commit,
        );
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            &mut transcript,
            b"t_high",
            &t_high_commit,
        );
        <Transcript as TranscriptProtocol<P>>::append_commitment(
            &mut transcript,
            b"t_4",
            &t_4_commit,
        );

        // round 4
        // compute evaluation challenge 'z'
        let z_challenge =
            <Transcript as TranscriptProtocol<P>>::challenge_scalar(
                &mut transcript,
                b"z_challenge",
            );

        // round 5
        // compute linearization polynomial
        let (r_poly, evaluations) = linearization_poly::compute::<P>(
            fft.generator(),
            &self.prover_key,
            &(
                alpha,
                beta,
                gamma,
                range_sep_challenge,
                logic_sep_challenge,
                curve_scalar_sep_challenge,
                var_base_sep_challenge,
                z_challenge,
            ),
            &a_w_poly,
            &b_w_poly,
            &o_w_poly,
            &d_w_poly,
            &t_poly,
            &z_poly,
        );

        // add evaluations to transcript.
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"a_eval",
            &evaluations.proof.a_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"b_eval",
            &evaluations.proof.b_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"c_eval",
            &evaluations.proof.c_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"d_eval",
            &evaluations.proof.d_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"a_next_eval",
            &evaluations.proof.a_next_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"b_next_eval",
            &evaluations.proof.b_next_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"d_next_eval",
            &evaluations.proof.d_next_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"s_sigma_1_eval",
            &evaluations.proof.s_sigma_1_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"s_sigma_2_eval",
            &evaluations.proof.s_sigma_2_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"s_sigma_3_eval",
            &evaluations.proof.s_sigma_3_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"q_arith_eval",
            &evaluations.proof.q_arith_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"q_c_eval",
            &evaluations.proof.q_c_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"q_l_eval",
            &evaluations.proof.q_l_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"q_r_eval",
            &evaluations.proof.q_r_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"perm_eval",
            &evaluations.proof.perm_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"t_eval",
            &evaluations.t_eval,
        );
        <Transcript as TranscriptProtocol<P>>::append_scalar(
            &mut transcript,
            b"r_eval",
            &evaluations.proof.r_poly_eval,
        );

        // compute Openings using KZG10
        let z_n = z_challenge.pow(domain_size as u64);
        let z_two_n = z_challenge.pow(2 * domain_size as u64);
        let z_three_n = z_challenge.pow(3 * domain_size as u64);

        let a = &t_low_poly;
        let b = &t_mid_poly * &z_n;
        let c = &t_high_poly * &z_two_n;
        let d = &t_4_poly * &z_three_n;
        let abc = (a + &b) + c;

        let quot = &abc + &d;

        // compute aggregate witness to polynomials evaluated at the evaluation
        // challenge z. The challenge v is selected inside
        let aggregate_witness = self.keypair.compute_aggregate_witness(
            &[
                quot,
                r_poly,
                a_w_poly.clone(),
                b_w_poly.clone(),
                o_w_poly,
                d_w_poly.clone(),
                self.prover_key.permutation.s_sigma_1.0.clone(),
                self.prover_key.permutation.s_sigma_2.0.clone(),
                self.prover_key.permutation.s_sigma_3.0.clone(),
            ],
            &z_challenge,
            &<Transcript as TranscriptProtocol<P>>::challenge_scalar(
                &mut transcript,
                b"v_challenge",
            ),
        );
        let w_z_chall_comm = self.keypair.commit(&aggregate_witness)?;

        // compute aggregate witness to polynomials evaluated at the shifted
        // evaluation challenge
        let shifted_aggregate_witness = self.keypair.compute_aggregate_witness(
            &[z_poly, a_w_poly, b_w_poly, d_w_poly],
            &(z_challenge * fft.generator()),
            &<Transcript as TranscriptProtocol<P>>::challenge_scalar(
                &mut transcript,
                b"v_challenge",
            ),
        );
        let w_z_chall_w_comm =
            self.keypair.commit(&shifted_aggregate_witness)?;

        let proof = Proof {
            a_comm: a_w_poly_commit,
            b_comm: b_w_poly_commit,
            c_comm: o_w_poly_commit,
            d_comm: d_w_poly_commit,

            z_comm: z_poly_commit,

            t_low_comm: t_low_commit,
            t_mid_comm: t_mid_commit,
            t_high_comm: t_high_commit,
            t_4_comm: t_4_commit,

            w_z_chall_comm,
            w_z_chall_w_comm,

            evaluations: evaluations.proof,
        };

        Ok((proof, public_inputs))
    }
}
