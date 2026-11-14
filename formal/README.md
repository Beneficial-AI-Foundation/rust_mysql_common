# Formal verification of `mysql_common`

A Lean 4 proof, via Charon and Aeneas, of the wire-protocol and binlog encoding and decoding of
this crate. Coverage, trusted-base details, bugs found and open items: [`docs/STATUS.md`](docs/STATUS.md).

## Where each part lives

| Folder | What it is | Read it? |
|---|---|---|
| [`trusted/`](trusted/) | everything taken on trust | all of it |
| [`specs/`](specs/) | what is claimed: `Defs/` (definitions), `Specs/` (statements, each with its axiom check) | all of it |
| [`translation/`](translation/) | the Aeneas translation of the Rust; generated, never edited | no |
| [`proofs/`](proofs/) | the proofs; checked by Lean | no |

Outside `formal/`: the Charon settings (`[package.metadata.charon]` in `../Cargo.toml`) and the
scripts `../scripts/aeneas-install.sh`, `../scripts/aeneas-translate.sh` (the verified target and
features are fixed in the latter).

## What must be trusted

1. Charon, Aeneas (and its modelling assumptions, e.g. allocation never fails) and Lean's kernel.
2. The configuration: target `x86_64-unknown-linux-gnu` and the features in
   `../scripts/aeneas-translate.sh`; the Charon `exclude`/`opaque` lists in `../Cargo.toml`.
3. `trusted/patches/`: behaviour-preserving edits applied to a copy of the crate before translation.
4. `trusted/MysqlCommon/FunsExternal.lean`, `TypesExternal.lean`: models and axioms of the code
   not translated. Evidence: `trusted/evidence/` (tests), and `proofs/Proofs/Consistency/`
   (models showing some axioms are consistent).
5. `specs/`: the definitions and statements say what is intended.

Check: `cd formal && lake exe cache get && lake build --wfail`.
