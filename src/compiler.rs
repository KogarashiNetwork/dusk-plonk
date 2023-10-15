// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use core::marker::PhantomData;

use crate::constraint_system::{Plonk, Prover, Verifier};

use poly_commit::{Coefficients as Coeffs, Fft, PointsValue as Points};
use sp_std::vec;
use zksnarks::circuit::Circuit;
use zksnarks::constraint_system::ConstraintSystem;
use zksnarks::error::Error;
use zksnarks::keypair::Keypair;
use zksnarks::plonk::keypair::{
    arithmetic,
    curve::{add, scalar},
    logic, permutation, range, ProvingKey, VerificationKey,
};
use zksnarks::plonk::PlonkParams;
use zkstd::common::{Group, Pairing, Ring};

/// Generate the arguments to prove and verify a circuit
pub struct Compiler<P: Pairing, C: Circuit<P::JubjubAffine>> {
    c: PhantomData<C>,
    p: PhantomData<P>,
}

impl<
        P: Pairing,
        C: Circuit<P::JubjubAffine, ConstraintSystem = Plonk<P::JubjubAffine>>,
    > Keypair<P, C> for Compiler<P, C>
{
    type Prover = Prover<P>;
    type Verifier = Verifier<P>;
    type PublicParameters = PlonkParams<P>;
    type ConstraintSystem = Plonk<P::JubjubAffine>;

    fn new(
        pp: &Self::PublicParameters,
    ) -> Result<(Self::Prover, Self::Verifier), Error> {
        Self::compile_with_circuit(pp, b"plonk", &C::default())
    }
}

impl<
        P: Pairing,
        C: Circuit<P::JubjubAffine, ConstraintSystem = Plonk<P::JubjubAffine>>,
    > Compiler<P, C>
{
    /// Create a new arguments set from a given circuit instance
    ///
    /// Use the provided circuit instead of the default implementation
    pub fn compile_with_circuit(
        keypair: &PlonkParams<P>,
        label: &[u8],
        circuit: &C,
    ) -> Result<
        (
            <Self as Keypair<P, C>>::Prover,
            <Self as Keypair<P, C>>::Verifier,
        ),
        Error,
    > {
        let max_size = keypair.max_degree() >> 1;
        let mut prover = Plonk::initialize(max_size);

        circuit.synthesize(&mut prover)?;

        let n = (prover.m() + 6).next_power_of_two();

        let keypair = keypair.trim(n);

        let (prover, verifier) = Self::preprocess(label, &keypair, &prover)?;

        Ok((prover, verifier))
    }

    fn preprocess(
        label: &[u8],
        keypair: &PlonkParams<P>,
        prover: &C::ConstraintSystem,
    ) -> Result<
        (
            <Self as Keypair<P, C>>::Prover,
            <Self as Keypair<P, C>>::Verifier,
        ),
        Error,
    > {
        let constraints = prover.m();
        let n = constraints.next_power_of_two();
        let k = n.trailing_zeros();
        let fft = Fft::<P::ScalarField>::new(k as usize);

        // 1. pad circuit to a power of two
        //
        // we use allocated vectors because the current ifft api only accepts
        // slices
        let mut q_m = Points::new(vec![P::ScalarField::zero(); n]);
        let mut q_l = Points::new(vec![P::ScalarField::zero(); n]);
        let mut q_r = Points::new(vec![P::ScalarField::zero(); n]);
        let mut q_o = Points::new(vec![P::ScalarField::zero(); n]);
        let mut q_c = Points::new(vec![P::ScalarField::zero(); n]);
        let mut q_d = Points::new(vec![P::ScalarField::zero(); n]);
        let mut q_arith = Points::new(vec![P::ScalarField::zero(); n]);
        let mut q_range = Points::new(vec![P::ScalarField::zero(); n]);
        let mut q_logic = Points::new(vec![P::ScalarField::zero(); n]);
        let mut q_fixed_group_add =
            Points::new(vec![P::ScalarField::zero(); n]);
        let mut q_variable_group_add =
            Points::new(vec![P::ScalarField::zero(); n]);

        prover
            .constraints()
            .into_iter()
            .enumerate()
            .for_each(|(i, c)| {
                q_m.0[i] = c.q_m;
                q_l.0[i] = c.q_l;
                q_r.0[i] = c.q_r;
                q_o.0[i] = c.q_o;
                q_c.0[i] = c.q_c;
                q_d.0[i] = c.q_d;
                q_arith.0[i] = c.q_arith;
                q_range.0[i] = c.q_range;
                q_logic.0[i] = c.q_logic;
                q_fixed_group_add.0[i] = c.q_fixed_group_add;
                q_variable_group_add.0[i] = c.q_variable_group_add;
            });

        let q_m_poly = fft.idft(q_m);
        let q_l_poly = fft.idft(q_l);
        let q_r_poly = fft.idft(q_r);
        let q_o_poly = fft.idft(q_o);
        let q_c_poly = fft.idft(q_c);
        let q_d_poly = fft.idft(q_d);
        let q_arith_poly = fft.idft(q_arith);
        let q_range_poly = fft.idft(q_range);
        let q_logic_poly = fft.idft(q_logic);
        let q_fixed_group_add_poly = fft.idft(q_fixed_group_add);
        let q_variable_group_add_poly = fft.idft(q_variable_group_add);

        // 2. compute the sigma polynomials
        let mut perm = prover.perm.clone();
        let [s_sigma_1_poly, s_sigma_2_poly, s_sigma_3_poly, s_sigma_4_poly] =
            perm.compute_sigma_polynomials(n, &fft);

        let q_m_poly_commit = keypair.commit(&q_m_poly).unwrap_or_default();
        let q_l_poly_commit = keypair.commit(&q_l_poly).unwrap_or_default();
        let q_r_poly_commit = keypair.commit(&q_r_poly).unwrap_or_default();
        let q_o_poly_commit = keypair.commit(&q_o_poly).unwrap_or_default();
        let q_c_poly_commit = keypair.commit(&q_c_poly).unwrap_or_default();
        let q_d_poly_commit = keypair.commit(&q_d_poly).unwrap_or_default();
        let q_arith_poly_commit =
            keypair.commit(&q_arith_poly).unwrap_or_default();
        let q_range_poly_commit =
            keypair.commit(&q_range_poly).unwrap_or_default();
        let q_logic_poly_commit =
            keypair.commit(&q_logic_poly).unwrap_or_default();
        let q_fixed_group_add_poly_commit =
            keypair.commit(&q_fixed_group_add_poly).unwrap_or_default();
        let q_variable_group_add_poly_commit = keypair
            .commit(&q_variable_group_add_poly)
            .unwrap_or_default();

        let s_sigma_1_poly_commit = keypair.commit(&s_sigma_1_poly)?;
        let s_sigma_2_poly_commit = keypair.commit(&s_sigma_2_poly)?;
        let s_sigma_3_poly_commit = keypair.commit(&s_sigma_3_poly)?;
        let s_sigma_4_poly_commit = keypair.commit(&s_sigma_4_poly)?;

        // verifier Key for arithmetic circuits
        let arithmetic_verifier_key = arithmetic::VerificationKey {
            q_m: q_m_poly_commit,
            q_l: q_l_poly_commit,
            q_r: q_r_poly_commit,
            q_o: q_o_poly_commit,
            q_c: q_c_poly_commit,
            q_4: q_d_poly_commit,
            q_arith: q_arith_poly_commit,
        };

        // verifier Key for range circuits
        let range_verifier_key = range::VerificationKey {
            q_range: q_range_poly_commit,
        };

        // verifier Key for logic circuits
        let logic_verifier_key = logic::VerificationKey {
            q_c: q_c_poly_commit,
            q_logic: q_logic_poly_commit,
        };

        // verifier Key for ecc circuits
        let ecc_verifier_key = scalar::VerificationKey {
            q_l: q_l_poly_commit,
            q_r: q_r_poly_commit,
            q_fixed_group_add: q_fixed_group_add_poly_commit,
        };

        // verifier Key for curve addition circuits
        let curve_addition_verifier_key = add::VerificationKey {
            q_variable_group_add: q_variable_group_add_poly_commit,
        };

        // verifier Key for permutation argument
        let permutation_verifier_key = permutation::VerificationKey {
            s_sigma_1: s_sigma_1_poly_commit,
            s_sigma_2: s_sigma_2_poly_commit,
            s_sigma_3: s_sigma_3_poly_commit,
            s_sigma_4: s_sigma_4_poly_commit,
        };

        let verifier_key = VerificationKey {
            n: constraints,
            n_inv: fft.size_inv(),
            generator: fft.generator(),
            generator_inv: fft.generator_inv(),
            arithmetic: arithmetic_verifier_key,
            logic: logic_verifier_key,
            range: range_verifier_key,
            curve_scalar: ecc_verifier_key,
            curve_addtion: curve_addition_verifier_key,
            permutation: permutation_verifier_key,
        };

        // The polynomial needs an evaluation domain of 4n.
        // Plus, adding the blinding factors translates to
        // the polynomial not fitting in 4n, so now we need
        // 8n, the next power of 2
        let x8n = (8 * n).next_power_of_two();
        let x8k = x8n.trailing_zeros();
        let fft_8n = Fft::new(x8k as usize);
        let min_p =
            Coeffs::new(vec![P::ScalarField::zero(), P::ScalarField::one()]);

        let q_m_eval_8n = fft_8n.coset_dft(q_m_poly.clone());
        let q_l_eval_8n = fft_8n.coset_dft(q_l_poly.clone());
        let q_r_eval_8n = fft_8n.coset_dft(q_r_poly.clone());
        let q_o_eval_8n = fft_8n.coset_dft(q_o_poly.clone());
        let q_c_eval_8n = fft_8n.coset_dft(q_c_poly.clone());
        let q_4_eval_8n = fft_8n.coset_dft(q_d_poly.clone());
        let q_arith_eval_8n = fft_8n.coset_dft(q_arith_poly.clone());
        let q_range_eval_8n = fft_8n.coset_dft(q_range_poly.clone());
        let q_logic_eval_8n = fft_8n.coset_dft(q_logic_poly.clone());
        let q_fixed_group_add_eval_8n =
            fft_8n.coset_dft(q_fixed_group_add_poly.clone());
        let q_variable_group_add_eval_8n =
            fft_8n.coset_dft(q_variable_group_add_poly.clone());

        let s_sigma_1_eval_8n = fft_8n.coset_dft(s_sigma_1_poly.clone());
        let s_sigma_2_eval_8n = fft_8n.coset_dft(s_sigma_2_poly.clone());
        let s_sigma_3_eval_8n = fft_8n.coset_dft(s_sigma_3_poly.clone());
        let s_sigma_4_eval_8n = fft_8n.coset_dft(s_sigma_4_poly.clone());

        let linear_eval_8n = fft_8n.coset_dft(min_p.clone());

        let arithmetic_prover_key = arithmetic::ProvingKey {
            q_m: (q_m_poly, q_m_eval_8n),
            q_l: (q_l_poly.clone(), q_l_eval_8n.clone()),
            q_r: (q_r_poly.clone(), q_r_eval_8n.clone()),
            q_o: (q_o_poly, q_o_eval_8n),
            q_c: (q_c_poly.clone(), q_c_eval_8n.clone()),
            q_4: (q_d_poly, q_4_eval_8n),
            q_arith: (q_arith_poly, q_arith_eval_8n),
        };

        let range_prover_key = range::ProvingKey {
            q_range: (q_range_poly, q_range_eval_8n),
        };

        let logic_prover_key = logic::ProvingKey {
            q_c: (q_c_poly.clone(), q_c_eval_8n.clone()),
            q_logic: (q_logic_poly, q_logic_eval_8n),
        };

        let ecc_prover_key = scalar::ProvingKey::<P> {
            q_l: (q_l_poly, q_l_eval_8n),
            q_r: (q_r_poly, q_r_eval_8n),
            q_c: (q_c_poly, q_c_eval_8n),
            q_fixed_group_add: (
                q_fixed_group_add_poly,
                q_fixed_group_add_eval_8n,
            ),
        };

        let permutation_prover_key = permutation::ProvingKey {
            s_sigma_1: (s_sigma_1_poly, s_sigma_1_eval_8n),
            s_sigma_2: (s_sigma_2_poly, s_sigma_2_eval_8n),
            s_sigma_3: (s_sigma_3_poly, s_sigma_3_eval_8n),
            s_sigma_4: (s_sigma_4_poly, s_sigma_4_eval_8n),
            linear_evaluations: linear_eval_8n,
        };

        let curve_addition_prover_key = add::ProvingKey {
            q_variable_group_add: (
                q_variable_group_add_poly,
                q_variable_group_add_eval_8n,
            ),
        };

        let v_h_coset_8n = fft_8n.compute_vanishing_poly_over_coset(n as u64);

        let prover_key = ProvingKey {
            n,
            arithmetic: arithmetic_prover_key,
            logic: logic_prover_key,
            range: range_prover_key,
            permutation: permutation_prover_key,
            curve_addtion: curve_addition_prover_key,
            curve_scalar: ecc_prover_key,
            v_h_coset_8n,
        };

        let public_input_indexes = prover.public_input_indexes();

        let label = label.to_vec();

        let prover = Prover::new(
            label.clone(),
            keypair.clone(),
            prover_key,
            verifier_key.clone(),
            n,
            constraints,
        );

        let verifier = Verifier::new(
            label,
            verifier_key,
            keypair.verification_key(),
            public_input_indexes,
            n,
            constraints,
        );

        Ok((prover, verifier))
    }
}
