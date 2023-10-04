// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use poly_commit::{Coefficients as Coeffs, Fft, PointsValue as Points};
use zksnarks::plonk::key::{
    arithmetic,
    curve::{add, scalar},
    logic, permutation, range, ProvingKey, VerificationKey,
};
use zksnarks::plonk::PlonkParams;
use zkstd::common::{Group, Pairing, Ring};

use super::{Builder, Circuit, Prover, Verifier};
use crate::error::Error;
use sp_std::vec;

/// Generate the arguments to prove and verify a circuit
pub struct Compiler;

type CompilerResult<C, P> = Result<(Prover<C, P>, Verifier<C, P>), Error>;

impl Compiler {
    /// Create a new arguments set from a given circuit instance
    ///
    /// Use the default implementation of the circuit
    pub fn compile<C, P>(
        keypair: &mut PlonkParams<P>,
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
        keypair: &mut PlonkParams<P>,
        label: &[u8],
        circuit: &C,
    ) -> CompilerResult<C, P>
    where
        C: Circuit<P>,
        P: Pairing,
    {
        let max_size = keypair.max_degree() >> 1;
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
        keypair: &PlonkParams<P>,
        prover: &Builder<P>,
    ) -> CompilerResult<C, P>
    where
        C: Circuit<P>,
        P: Pairing,
    {
        let mut perm = prover.perm.clone();

        let constraints = prover.constraints();
        let n = constraints.next_power_of_two();
        let k = n.trailing_zeros();
        let fft = Fft::<P::ScalarField>::new(k as usize);

        // 1. pad circuit to a power of two
        //
        // we use allocated vectors because the current ifft api only accepts
        // slices
        let mut q_m = Coeffs::new(vec![P::ScalarField::zero(); n]);
        let mut q_l = Coeffs::new(vec![P::ScalarField::zero(); n]);
        let mut q_r = Coeffs::new(vec![P::ScalarField::zero(); n]);
        let mut q_o = Coeffs::new(vec![P::ScalarField::zero(); n]);
        let mut q_c = Coeffs::new(vec![P::ScalarField::zero(); n]);
        let mut q_d = Coeffs::new(vec![P::ScalarField::zero(); n]);
        let mut q_arith = Coeffs::new(vec![P::ScalarField::zero(); n]);
        let mut q_range = Coeffs::new(vec![P::ScalarField::zero(); n]);
        let mut q_logic = Coeffs::new(vec![P::ScalarField::zero(); n]);
        let mut q_fixed_group_add =
            Coeffs::new(vec![P::ScalarField::zero(); n]);
        let mut q_variable_group_add =
            Coeffs::new(vec![P::ScalarField::zero(); n]);

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

        let q_m_poly = Coeffs::from_vec(q_m.0.clone());
        let q_l_poly = Coeffs::from_vec(q_l.0.clone());
        let q_r_poly = Coeffs::from_vec(q_r.0.clone());
        let q_o_poly = Coeffs::from_vec(q_o.0.clone());
        let q_c_poly = Coeffs::from_vec(q_c.0.clone());
        let q_d_poly = Coeffs::from_vec(q_d.0.clone());
        let q_arith_poly = Coeffs::from_vec(q_arith.0.clone());
        let q_range_poly = Coeffs::from_vec(q_range.0.clone());
        let q_logic_poly = Coeffs::from_vec(q_logic.0.clone());
        let q_fixed_group_add_poly =
            Coeffs::from_vec(q_fixed_group_add.0.clone());
        let q_variable_group_add_poly =
            Coeffs::from_vec(q_variable_group_add.0.clone());

        // 2. compute the sigma polynomials
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

        let s_sigma_1_poly_commit = Coeffs::from_vec(s_sigma_1_poly.0.clone());
        let s_sigma_2_poly_commit = Coeffs::from_vec(s_sigma_2_poly.0.clone());
        let s_sigma_3_poly_commit = Coeffs::from_vec(s_sigma_3_poly.0.clone());
        let s_sigma_4_poly_commit = Coeffs::from_vec(s_sigma_4_poly.0.clone());

        let s_sigma_1_poly_commit = keypair.commit(&s_sigma_1_poly_commit)?;
        let s_sigma_2_poly_commit = keypair.commit(&s_sigma_2_poly_commit)?;
        let s_sigma_3_poly_commit = keypair.commit(&s_sigma_3_poly_commit)?;
        let s_sigma_4_poly_commit = keypair.commit(&s_sigma_4_poly_commit)?;

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
        let mut s_sigma_1 = s_sigma_1_poly.clone();
        let mut s_sigma_2 = s_sigma_2_poly.clone();
        let mut s_sigma_3 = s_sigma_3_poly.clone();
        let mut s_sigma_4 = s_sigma_4_poly.clone();
        let mut min_p =
            Coeffs::new(vec![P::ScalarField::zero(), P::ScalarField::one()]);

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

        let q_m_eval_8n = Points::new(q_m.0.clone());
        let q_l_eval_8n = Points::new(q_l.0.clone());
        let q_r_eval_8n = Points::new(q_r.0.clone());
        let q_o_eval_8n = Points::new(q_o.0.clone());
        let q_c_eval_8n = Points::new(q_c.0.clone());
        let q_4_eval_8n = Points::new(q_d.0.clone());
        let q_arith_eval_8n = Points::new(q_arith.0.clone());
        let q_range_eval_8n = Points::new(q_range.0.clone());
        let q_logic_eval_8n = Points::new(q_logic.0.clone());
        let q_fixed_group_add_eval_8n =
            Points::new(q_fixed_group_add.0.clone());
        let q_variable_group_add_eval_8n =
            Points::new(q_variable_group_add.0.clone());

        let s_sigma_1_eval_8n = Points::new(s_sigma_1.0);
        let s_sigma_2_eval_8n = Points::new(s_sigma_2.0);
        let s_sigma_3_eval_8n = Points::new(s_sigma_3.0);
        let s_sigma_4_eval_8n = Points::new(s_sigma_4.0);

        let linear_eval_8n = Points::new(min_p.0);

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
