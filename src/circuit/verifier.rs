// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use crate::error::Error;
use crate::proof_system::Proof;

use super::Builder;

use core::marker::PhantomData;
use poly_commit::EvaluationKey;
use zksnarks::{Transcript, TranscriptProtocol, VerificationKey};
use zkstd::common::{Pairing, Vec};

/// Verify proofs of a given circuit
pub struct Verifier<C, P: Pairing> {
    verifier_key: VerificationKey<P>,
    opening_key: EvaluationKey<P>,
    public_input_indexes: Vec<usize>,
    transcript: Transcript,
    size: usize,
    circuit: PhantomData<C>,
}

impl<C, P: Pairing> Verifier<C, P> {
    pub(crate) fn new(
        label: Vec<u8>,
        verifier_key: VerificationKey<P>,
        opening_key: EvaluationKey<P>,
        public_input_indexes: Vec<usize>,
        size: usize,
        constraints: usize,
    ) -> Self {
        let transcript =
            Transcript::base(label.as_slice(), &verifier_key, constraints);

        Self {
            verifier_key,
            opening_key,
            public_input_indexes,
            transcript,
            size,
            circuit: PhantomData,
        }
    }

    /// Verify a generated proof
    pub fn verify(
        &self,
        proof: &Proof<P>,
        public_inputs: &[P::ScalarField],
    ) -> Result<(), Error> {
        if public_inputs.len() != self.public_input_indexes.len() {
            return Err(Error::InconsistentPublicInputsLen {
                expected: self.public_input_indexes.len(),
                provided: public_inputs.len(),
            });
        }

        let mut transcript = self.transcript.clone();

        public_inputs.iter().for_each(|pi| {
            <Transcript as TranscriptProtocol<P>>::append_scalar(
                &mut transcript,
                b"pi",
                pi,
            )
        });

        let dense_public_inputs = Builder::<P>::dense_public_inputs(
            &self.public_input_indexes,
            public_inputs,
            self.size,
        );

        proof.verify(
            &self.verifier_key,
            &mut transcript,
            &self.opening_key,
            &dense_public_inputs,
        )
    }
}