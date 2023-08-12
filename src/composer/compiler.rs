// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use poly_commit::{Coefficients, Fft, KeyPair, PointsValue};
use zksnarks::key::{
    arithmetic,
    curve::{add, scalar},
    logic, permutation, range, ProvingKey, VerificationKey,
};
use zkstd::common::{Group, Pairing, Ring};

use super::{Builder, Circuit, Composer, Prover, Verifier};
use crate::commitment_scheme::OpeningKey;
use crate::error::Error;
use crate::proof_system::preprocess::Polynomials;
use sp_std::vec;

/// Generate the arguments to prove and verify a circuit
pub struct Compiler;

type CompilerResult<C, P> = Result<(Prover<C, P>, Verifier<C, P>), Error>;

impl Compiler {
    /// Create a new arguments set from a given circuit instance
    ///
    /// Use the default implementation of the circuit
    pub fn compile<C, P>(
        keypair: &mut KeyPair<P>,
        label: &[u8],
    ) -> CompilerResult<C, P>
    where
        C: Circuit<P>,
        P: Pairing,
    {
        Self::compile_with_circuit::<C, P>(keypair, label, &Default::default())
    }

    /// Create a new arguments set from a given circuit instance
    ///
    /// Use the provided circuit instead of the default implementation
    pub fn compile_with_circuit<C, P>(
        keypair: &mut KeyPair<P>,
        label: &[u8],
        circuit: &C,
    ) -> CompilerResult<C, P>
    where
        C: Circuit<P>,
        P: Pairing,
    {
        let max_size = (keypair.commit_key().len() - 1) >> 1;
        let mut prover = Builder::initialized(max_size);

        circuit.circuit(&mut prover)?;

        let n = (prover.constraints() + 6).next_power_of_two();

        let keypair = keypair.trim(n);

        let (prover, verifier) =
            Self::preprocess::<C, P>(label, &keypair, &prover)?;

        Ok((prover, verifier))
    }

    fn preprocess<C, P>(
        label: &[u8],
        keypair: &KeyPair<P>,
        prover: &Builder<P>,
    ) -> CompilerResult<C, P>
    where
        C: Circuit<P>,
        P: Pairing,
    {
        let mut perm = prover.perm.clone();

        let constraints = prover.constraints();
        let size = constraints.next_power_of_two();
        let k = size.trailing_zeros();
        let fft = Fft::<P::ScalarField>::new(k as usize);

        // 1. pad circuit to a power of two
        //
        // we use allocated vectors because the current ifft api only accepts
        // slices
        let mut q_m =
            Coefficients::new(vec![<P::ScalarField as Group>::zero(); size]);
        let mut q_l =
            Coefficients::new(vec![<P::ScalarField as Group>::zero(); size]);
        let mut q_r =
            Coefficients::new(vec![<P::ScalarField as Group>::zero(); size]);
        let mut q_o =
            Coefficients::new(vec![<P::ScalarField as Group>::zero(); size]);
        let mut q_c =
            Coefficients::new(vec![<P::ScalarField as Group>::zero(); size]);
        let mut q_d =
            Coefficients::new(vec![<P::ScalarField as Group>::zero(); size]);
        let mut q_arith =
            Coefficients::new(vec![<P::ScalarField as Group>::zero(); size]);
        let mut q_range =
            Coefficients::new(vec![<P::ScalarField as Group>::zero(); size]);
        let mut q_logic =
            Coefficients::new(vec![<P::ScalarField as Group>::zero(); size]);
        let mut q_fixed_group_add =
            Coefficients::new(vec![<P::ScalarField as Group>::zero(); size]);
        let mut q_variable_group_add =
            Coefficients::new(vec![<P::ScalarField as Group>::zero(); size]);

        prover.constraints.iter().enumerate().for_each(|(i, c)| {
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

        fft.idft(&mut q_m);
        fft.idft(&mut q_l);
        fft.idft(&mut q_r);
        fft.idft(&mut q_o);
        fft.idft(&mut q_c);
        fft.idft(&mut q_d);
        fft.idft(&mut q_arith);
        fft.idft(&mut q_range);
        fft.idft(&mut q_logic);
        fft.idft(&mut q_fixed_group_add);
        fft.idft(&mut q_variable_group_add);

        let q_m_poly = Coefficients::from_vec(q_m.0.clone());
        let q_l_poly = Coefficients::from_vec(q_l.0.clone());
        let q_r_poly = Coefficients::from_vec(q_r.0.clone());
        let q_o_poly = Coefficients::from_vec(q_o.0.clone());
        let q_c_poly = Coefficients::from_vec(q_c.0.clone());
        let q_d_poly = Coefficients::from_vec(q_d.0.clone());
        let q_arith_poly = Coefficients::from_vec(q_arith.0.clone());
        let q_range_poly = Coefficients::from_vec(q_range.0.clone());
        let q_logic_poly = Coefficients::from_vec(q_logic.0.clone());
        let q_fixed_group_add_poly =
            Coefficients::from_vec(q_fixed_group_add.0.clone());
        let q_variable_group_add_poly =
            Coefficients::from_vec(q_variable_group_add.0.clone());

        // 2. compute the sigma polynomials
        let [s_sigma_1_poly, s_sigma_2_poly, s_sigma_3_poly, s_sigma_4_poly] =
            perm.compute_sigma_polynomials(size, &fft);

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

        let s_sigma_1_poly_commit =
            Coefficients::from_vec(s_sigma_1_poly.0.clone());
        let s_sigma_2_poly_commit =
            Coefficients::from_vec(s_sigma_2_poly.0.clone());
        let s_sigma_3_poly_commit =
            Coefficients::from_vec(s_sigma_3_poly.0.clone());
        let s_sigma_4_poly_commit =
            Coefficients::from_vec(s_sigma_4_poly.0.clone());

        let s_sigma_1_poly_commit = keypair.commit(&s_sigma_1_poly_commit)?;
        let s_sigma_2_poly_commit = keypair.commit(&s_sigma_2_poly_commit)?;
        let s_sigma_3_poly_commit = keypair.commit(&s_sigma_3_poly_commit)?;
        let s_sigma_4_poly_commit = keypair.commit(&s_sigma_4_poly_commit)?;

        // verifier Key for arithmetic circuits
        let arithmetic_verifier_key = arithmetic::VerificationKey {
            q_m: q_m_poly_commit,
            q_l: q_l_poly_commit.clone(),
            q_r: q_r_poly_commit.clone(),
            q_o: q_o_poly_commit,
            q_c: q_c_poly_commit.clone(),
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
            arithmetic: arithmetic_verifier_key,
            logic: logic_verifier_key,
            range: range_verifier_key,
            fixed_base: ecc_verifier_key,
            variable_base: curve_addition_verifier_key,
            permutation: permutation_verifier_key,
        };

        // The polynomial needs an evaluation domain of 4n.
        // Plus, adding the blinding factors translates to
        // the polynomial not fitting in 4n, so now we need
        // 8n, the next power of 2
        let n = (8 * fft.size()).next_power_of_two();
        let k = n.trailing_zeros();
        let fft_8n = Fft::new(k as usize);
        let mut s_sigma_1 = s_sigma_1_poly.clone();
        let mut s_sigma_2 = s_sigma_2_poly.clone();
        let mut s_sigma_3 = s_sigma_3_poly.clone();
        let mut s_sigma_4 = s_sigma_4_poly.clone();
        let mut min_p = Coefficients::new(vec![
            P::ScalarField::zero(),
            P::ScalarField::one(),
        ]);

        fft_8n.coset_dft(&mut q_m);
        fft_8n.coset_dft(&mut q_l);
        fft_8n.coset_dft(&mut q_r);
        fft_8n.coset_dft(&mut q_o);
        fft_8n.coset_dft(&mut q_c);
        fft_8n.coset_dft(&mut q_d);
        fft_8n.coset_dft(&mut q_arith);
        fft_8n.coset_dft(&mut q_range);
        fft_8n.coset_dft(&mut q_logic);
        fft_8n.coset_dft(&mut q_fixed_group_add);
        fft_8n.coset_dft(&mut q_variable_group_add);
        fft_8n.coset_dft(&mut s_sigma_1);
        fft_8n.coset_dft(&mut s_sigma_2);
        fft_8n.coset_dft(&mut s_sigma_3);
        fft_8n.coset_dft(&mut s_sigma_4);
        fft_8n.coset_dft(&mut min_p);

        let q_m_eval_8n = PointsValue::new(q_m.0.clone());
        let q_l_eval_8n = PointsValue::new(q_l.0.clone());
        let q_r_eval_8n = PointsValue::new(q_r.0.clone());
        let q_o_eval_8n = PointsValue::new(q_o.0.clone());
        let q_c_eval_8n = PointsValue::new(q_c.0.clone());
        let q_4_eval_8n = PointsValue::new(q_d.0.clone());
        let q_arith_eval_8n = PointsValue::new(q_arith.0.clone());
        let q_range_eval_8n = PointsValue::new(q_range.0.clone());
        let q_logic_eval_8n = PointsValue::new(q_logic.0.clone());
        let q_fixed_group_add_eval_8n =
            PointsValue::new(q_fixed_group_add.0.clone());
        let q_variable_group_add_eval_8n =
            PointsValue::new(q_variable_group_add.0.clone());

        let s_sigma_1_eval_8n = PointsValue::new(s_sigma_1.0);
        let s_sigma_2_eval_8n = PointsValue::new(s_sigma_2.0);
        let s_sigma_3_eval_8n = PointsValue::new(s_sigma_3.0);
        let s_sigma_4_eval_8n = PointsValue::new(s_sigma_4.0);

        let linear_eval_8n = PointsValue::new(min_p.0);

        let selectors = Polynomials::<P> {
            q_m: q_m_poly,
            q_l: q_l_poly,
            q_r: q_r_poly,
            q_o: q_o_poly,
            q_c: q_c_poly,
            q_4: q_d_poly,
            q_arith: q_arith_poly,
            q_range: q_range_poly,
            q_logic: q_logic_poly,
            q_fixed_group_add: q_fixed_group_add_poly,
            q_variable_group_add: q_variable_group_add_poly,
            s_sigma_1: s_sigma_1_poly,
            s_sigma_2: s_sigma_2_poly,
            s_sigma_3: s_sigma_3_poly,
            s_sigma_4: s_sigma_4_poly,
        };

        let arithmetic_prover_key = arithmetic::ProvingKey {
            q_m: (selectors.q_m, q_m_eval_8n),
            q_l: (selectors.q_l.clone(), q_l_eval_8n.clone()),
            q_r: (selectors.q_r.clone(), q_r_eval_8n.clone()),
            q_o: (selectors.q_o, q_o_eval_8n),
            q_c: (selectors.q_c.clone(), q_c_eval_8n.clone()),
            q_4: (selectors.q_4, q_4_eval_8n),
            q_arith: (selectors.q_arith, q_arith_eval_8n),
        };

        let range_prover_key = range::ProvingKey {
            q_range: (selectors.q_range, q_range_eval_8n),
        };

        let logic_prover_key = logic::ProvingKey {
            q_c: (selectors.q_c.clone(), q_c_eval_8n.clone()),
            q_logic: (selectors.q_logic, q_logic_eval_8n),
        };

        let ecc_prover_key = scalar::ProvingKey::<P> {
            q_l: (selectors.q_l, q_l_eval_8n),
            q_r: (selectors.q_r, q_r_eval_8n),
            q_c: (selectors.q_c, q_c_eval_8n),
            q_fixed_group_add: (
                selectors.q_fixed_group_add,
                q_fixed_group_add_eval_8n,
            ),
        };

        let permutation_prover_key = permutation::ProvingKey {
            s_sigma_1: (selectors.s_sigma_1, s_sigma_1_eval_8n),
            s_sigma_2: (selectors.s_sigma_2, s_sigma_2_eval_8n),
            s_sigma_3: (selectors.s_sigma_3, s_sigma_3_eval_8n),
            s_sigma_4: (selectors.s_sigma_4, s_sigma_4_eval_8n),
            linear_evaluations: linear_eval_8n,
        };

        let curve_addition_prover_key = add::ProvingKey {
            q_variable_group_add: (
                selectors.q_variable_group_add,
                q_variable_group_add_eval_8n,
            ),
        };

        let v_h_coset_8n =
            fft_8n.compute_vanishing_poly_over_coset(fft.size() as u64);

        let prover_key = ProvingKey {
            n: fft.size(),
            arithmetic: arithmetic_prover_key,
            logic: logic_prover_key,
            range: range_prover_key,
            permutation: permutation_prover_key,
            variable_base: curve_addition_prover_key,
            fixed_base: ecc_prover_key,
            v_h_coset_8n,
        };

        let public_input_indexes = prover.public_input_indexes();

        let label = label.to_vec();

        let prover = Prover::new(
            label.clone(),
            keypair.clone(),
            prover_key,
            verifier_key.clone(),
            size,
            constraints,
        );

        let verifier = Verifier::new(
            label,
            verifier_key,
            OpeningKey::new(
                keypair.commit_key()[0],
                keypair.opening_key(),
                keypair.beta_h(),
            ),
            public_input_indexes,
            size,
            constraints,
        );

        Ok((prover, verifier))
    }
}
