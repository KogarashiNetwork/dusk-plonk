// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use crate::composer::{Builder, Composer};
use zksnarks::{Selector, Wire, Witness};
use zkstd::behave::{Group, Ring};
use zkstd::common::Pairing;

/// Constraint representation containing the coefficients of a polynomial
/// evaluation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Constraint<P: Pairing> {
    coefficients: [P::ScalarField; 13],
    witnesses: [Witness; 4],

    // TODO Workaround solution to keep the sparse public input indexes in the
    // composer
    //
    // The indexes are needed to build the `VerifierData` so it won't contain
    // all the constraints of the circuit.
    //
    // However, the composer uses a dense instance of the public inputs to
    // prove statements. This way, it will need to keep the vector of
    // indexes internally so the `VerifierData` can be properly generated.
    //
    // Whenever `Constraint::public` is called and appended to a composer, the
    // composer must include this constraint index into the sparse set of
    // public input indexes.
    //
    // This workaround can be removed only after the composer replaces the
    // internal `Vec<BlsScalar>` of the selectors by a single
    // `Vec<Constraint>`.
    //
    // Related issue: https://github.com/dusk-network/plonk/issues/607
    has_public_input: bool,
}

impl<P: Pairing> Default for Constraint<P> {
    fn default() -> Self {
        Self {
            coefficients: [P::ScalarField::zero(); 13],
            witnesses: [Builder::<P>::ZERO; 4],
            has_public_input: false,
        }
    }
}

impl<P: Pairing> Constraint<P> {
    fn set<T: Into<P::ScalarField>>(mut self, r: Selector, s: T) -> Self {
        self.coefficients[r as usize] = s.into();

        self
    }

    fn from_external(constraint: &Self) -> Self {
        const EXTERNAL: usize = Selector::Arithmetic as usize;

        let mut s = Self::default();

        let src = &constraint.coefficients[..EXTERNAL];
        let dst = &mut s.coefficients[..EXTERNAL];

        dst.copy_from_slice(src);

        s.has_public_input = constraint.has_public_input();
        s.witnesses.copy_from_slice(&constraint.witnesses);

        s
    }

    /// Replace the value of an indexed witness
    pub(crate) fn set_witness(&mut self, index: Wire, w: Witness) {
        self.witnesses[index as usize] = w;
    }

    /// Return a reference to the specified selector of a circuit constraint.
    pub(crate) const fn coeff(&self, r: Selector) -> &P::ScalarField {
        &self.coefficients[r as usize]
    }

    /// Return the wired witness in the constraint
    pub(crate) const fn witness(&self, w: Wire) -> Witness {
        self.witnesses[w as usize]
    }

    /// Set `s` as the polynomial selector for the multiplication coefficient.
    pub fn mult<T: Into<P::ScalarField>>(self, s: T) -> Self {
        self.set(Selector::Multiplication, s)
    }

    /// Set `s` as the polynomial selector for the left coefficient.
    pub fn left<T: Into<P::ScalarField>>(self, s: T) -> Self {
        self.set(Selector::Left, s)
    }

    /// Set `s` as the polynomial selector for the right coefficient.
    pub fn right<T: Into<P::ScalarField>>(self, s: T) -> Self {
        self.set(Selector::Right, s)
    }

    /// Set `s` as the polynomial selector for the output coefficient.
    pub fn output<T: Into<P::ScalarField>>(self, s: T) -> Self {
        self.set(Selector::Output, s)
    }

    /// Set `s` as the polynomial selector for the fourth (advice) coefficient.
    pub fn fourth<T: Into<P::ScalarField>>(self, s: T) -> Self {
        self.set(Selector::Fourth, s)
    }

    /// Set `s` as the polynomial selector for the constant of the constraint.
    pub fn constant<T: Into<P::ScalarField>>(self, s: T) -> Self {
        self.set(Selector::Constant, s)
    }

    /// Set `s` as the public input of the constraint evaluation.
    pub fn public<T: Into<P::ScalarField>>(mut self, s: T) -> Self {
        self.has_public_input = true;

        self.set(Selector::PublicInput, s)
    }

    /// Set witness `a` wired to `qM` and `qL`
    pub fn a(mut self, w: Witness) -> Self {
        self.set_witness(Wire::A, w);

        self
    }

    /// Set witness `b` wired to `qM` and `qR`
    pub fn b(mut self, w: Witness) -> Self {
        self.set_witness(Wire::B, w);

        self
    }

    /// Set witness `o` wired to `qO`
    pub fn o(mut self, w: Witness) -> Self {
        self.set_witness(Wire::O, w);

        self
    }

    /// Set witness `d` wired to the fourth/advice `q4` coefficient
    pub fn d(mut self, w: Witness) -> Self {
        self.set_witness(Wire::D, w);

        self
    }

    pub(crate) const fn has_public_input(&self) -> bool {
        self.has_public_input
    }

    pub(crate) fn arithmetic(s: &Self) -> Self {
        Self::from_external(s).set(Selector::Arithmetic, 1)
    }

    #[allow(dead_code)]
    // TODO to be used when `ComposerBackend` replaces internal selectors
    // with this struct
    pub(crate) fn range(s: &Self) -> Self {
        Self::from_external(s).set(Selector::Range, 1)
    }

    #[allow(dead_code)]
    // TODO to be used when `ComposerBackend` replaces internal selectors
    // with this struct
    pub(crate) fn logic(s: &Self) -> Self {
        Self::from_external(s)
            .set(Selector::Constant, 1)
            .set(Selector::Logic, 1)
    }

    #[allow(dead_code)]
    // TODO to be used when `ComposerBackend` replaces internal selectors
    // with this struct
    pub(crate) fn logic_xor(s: &Self) -> Self {
        Self::from_external(s)
            .set(Selector::Constant, -P::ScalarField::one())
            .set(Selector::Logic, -P::ScalarField::one())
    }

    #[allow(dead_code)]
    // TODO to be used when `ComposerBackend` replaces internal selectors
    // with this struct
    pub(crate) fn group_add_curve_scalar(s: &Self) -> Self {
        Self::from_external(s).set(Selector::GroupAddFixedBase, 1)
    }

    #[allow(dead_code)]
    // TODO to be used when `ComposerBackend` replaces internal selectors
    // with this struct
    pub(crate) fn group_add_curve_addtion(s: &Self) -> Self {
        Self::from_external(s).set(Selector::GroupAddVariableBase, 1)
    }
}
