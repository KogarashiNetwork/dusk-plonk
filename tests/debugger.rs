// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use ec_pairing::TatePairing;
use zero_plonk::prelude::*;

#[derive(Debug, Default)]
struct EmptyCircuit;

impl Circuit<TatePairing> for EmptyCircuit {
    fn circuit(
        &self,
        _composer: &mut Builder<TatePairing>,
    ) -> Result<(), Error> {
        Ok(())
    }
}

#[test]
#[cfg(debug_assertions)]
fn generate_cdf_works() -> io::Result<()> {
    use poly_commit::KzgParams;

    let mut rng = rand::thread_rng();

    let dir = tempdir::TempDir::new("plonk-cdf")?;
    let path = dir.path().canonicalize()?.join("test.cdf");

    let label = b"transcript-arguments";
    let mut pp = KzgParams::setup(5, BlsScalar::random(&mut rng));
    // let mut pp = KzgParams::setup(n, BlsScalar::random(&mut rng));

    let (prover, _verifier) =
        Compiler::compile::<EmptyCircuit, TatePairing>(&mut pp, label)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;

    env::set_var("CDF_OUTPUT", &path);

    prover
        .prove(&mut rng, &EmptyCircuit)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;

    path.canonicalize().and_then(CircuitDescription::open)?;

    Ok(())
}
