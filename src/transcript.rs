// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! This is an extension over the [Merlin Transcript](Transcript)
//! which adds a few extra functionalities.

use core::mem;

use merlin::Transcript;
use zero_kzg::Commitment;
use zkstd::behave::{FftField, SigUtils};
use zkstd::common::Pairing;

use crate::proof_system::VerifierKey;

/// Transcript adds an abstraction over the Merlin transcript
/// For convenience
pub(crate) trait TranscriptProtocol<P: Pairing> {
    /// Append a `commitment` with the given `label`.
    fn append_commitment(&mut self, label: &'static [u8], comm: &Commitment<P>);

    /// Append a `BlsScalar` with the given `label`.
    fn append_scalar(&mut self, label: &'static [u8], s: &P::ScalarField);

    /// Compute a `label`ed challenge variable.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> P::ScalarField;

    /// Append domain separator for the circuit size.
    fn circuit_domain_sep(&mut self, n: u64);

    /// Create a new instance of the base transcript of the protocol
    fn base(
        label: &[u8],
        verifier_key: &VerifierKey<P>,
        constraints: usize,
    ) -> Self;
}

impl<P: Pairing> TranscriptProtocol<P> for Transcript {
    fn append_commitment(
        &mut self,
        label: &'static [u8],
        comm: &Commitment<P>,
    ) {
        self.append_message(label, &comm.0.to_bytes());
    }

    fn append_scalar(&mut self, label: &'static [u8], s: &P::ScalarField) {
        self.append_message(label, &s.to_bytes())
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> P::ScalarField {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);

        P::ScalarField::from_bytes_wide(&buf)
    }

    fn circuit_domain_sep(&mut self, n: u64) {
        self.append_message(b"dom-sep", b"circuit_size");
        self.append_u64(b"n", n);
    }

    fn base(
        label: &[u8],
        verifier_key: &VerifierKey<P>,
        constraints: usize,
    ) -> Self {
        // Transcript can't be serialized/deserialized. One alternative is to
        // fork merlin and implement these functionalities, so we can use custom
        // transcripts for provers and verifiers. However, we don't have a use
        // case for this feature in Dusk.

        // Safety: static lifetime is a pointless requirement from merlin that
        // doesn't add any security but instead restricts a lot the
        // serialization and deserialization of transcripts
        let label = unsafe { mem::transmute(label) };

        let mut transcript = Transcript::new(label);

        <Transcript as TranscriptProtocol<P>>::circuit_domain_sep(
            &mut transcript,
            constraints as u64,
        );

        verifier_key.seed_transcript(&mut transcript);

        transcript
    }
}
