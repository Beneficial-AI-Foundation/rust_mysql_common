# Verifying Rust in Lean with Aeneas

This describes how we verify a Rust crate in Lean 4. The Rust code is translated to Lean by
[Charon](https://github.com/AeneasVerif/charon) and [Aeneas](https://github.com/AeneasVerif/aeneas).
We state specs for the public API and prove them against the translation.

This is the simplest version of the process: one crate, translated for **a single target**. (For
the multi-target version, where several configurations are translated and merged, see
`curve25519-dalek-fork`.)

## Layout

```
lakefile.toml                 Lean project; pins the Aeneas version
lean-toolchain                copied from the pinned Aeneas release by the install script
Cargo.toml                    [package.metadata.charon]: what Charon translates, excludes, opaque
scripts/aeneas-install.sh     downloads the pinned charon + aeneas binaries into .aeneas/
scripts/aeneas-translate.sh   applies the patches to a copy of the crate and translates it
translation-patches/*.patch   local Rust edits that work around translation problems
.github/workflows/            CI: translation is current, Lean project builds
lean/
  <Crate>/                    the Aeneas translation (Funs.lean, Types.lean: generated)
                              and hand-written FunsExternal.lean, TypesExternal.lean
  Defs/                       definitions needed to state the specs
  Specs/                      one spec file per Rust file: public statements + axioms used
  Proofs/                     the proofs, one file per Rust item
```

### What is committed

- **Committed:** the generated translation (`Funs.lean`, `Types.lean`, `translation.json`), the
  hand-written `FunsExternal.lean` and `TypesExternal.lean`, `lake-manifest.json`, and
  `lean-toolchain`. The stale-translation check in CI needs the generated files to be in git.
- **Git-ignored:** `.aeneas/`, `.llbc/` and `.lake/` (build outputs), and
  `*External_Template.lean` (regenerated on every run).
- **Never edited by hand:** the generated files. To change them, change the Rust, a patch, or the
  Charon settings, and re-run the translation. CI rejects hand-edits.

## 0. Scope

Before translating anything, decide which part of the crate is worth verifying and which part
Aeneas can handle. Aeneas works well on pure, sequential, safe Rust: data structures, parsing,
encoding, arithmetic. It does not handle I/O, threads and synchronisation, interior mutability or
`unsafe` code well. Code that is mostly about those is usually excluded rather than patched, and the
verification concentrates on the logic underneath it. Write the scope decision down, since it
determines what the final result does and does not cover.

## 1. The Lean project pins Aeneas

`lakefile.toml` requires the Aeneas Lean library at a specific release tag:

```toml
[[require]]
name = "aeneas"
git = "https://github.com/AeneasVerif/aeneas.git"
subDir = "backends/lean"
rev = "nightly-YYYY.MM.DD-<hash>"   # must be a GitHub release tag
```

This one `rev` is the single source of truth for the Aeneas version. Both scripts read it from
`lakefile.toml`, so the binaries that translate the code always match the Lean library the proofs
build against. To upgrade Aeneas, change the `rev`, rerun both scripts, and fix whatever breaks.

## 2. Install: `scripts/aeneas-install.sh`

The script:

1. Reads the Aeneas `rev` from `lakefile.toml`.
2. If `.aeneas/aeneas -version` doesn't already report that tag, downloads the matching release
   bundle (charon, charon-driver, aeneas, the Lean backend) for the current platform from GitHub
   into `.aeneas/`.
3. Installs the Rust nightly toolchain that `charon-driver` was built against, from the bundle's
   `rust-toolchain` file.
4. Copies the bundle's `backends/lean/lean-toolchain` to `lean-toolchain`, so Lean matches too.

Running it again does nothing if the right version is already installed.

## 3. Charon settings live in `Cargo.toml`

What gets translated is set in the crate's `Cargo.toml`, not in the script:

```toml
[package.metadata.charon]
start_from = ["my_crate"]
# Items we will never verify: not translated at all.
exclude = [
  "my_crate::some_module::{impl core::fmt::Debug for _}",
]
# Items verification relies on but which we deliberately do not translate.
opaque = []
```

- **`exclude`** is for things we have no interest in verifying, such as `Debug` and `Hash` impls,
  marker-trait impls, and other code outside the scope of the specs. Excluded items are not
  translated, and nothing we verify may depend on them.
- **`opaque`** is almost never used. An item is made opaque only when it **cannot be translated
  and there is no useful Rust model** we could patch in. Its Lean signature is then generated
  without a body, and we state its behaviour as a Lean axiom in `FunsExternal.lean`. Every opaque
  item adds to the trusted base, so it needs a strong justification. The default answer to a
  translation problem is a patch (below), not `opaque`.

Each entry should have a comment saying why it is there.

Entries are Charon name patterns, such as `my_crate::module::Type::method` or
`my_crate::module::{impl core::fmt::Debug for _}` (every `Debug` impl in a module). For the full pattern
syntax and the other options, see the [Charon documentation](https://github.com/AeneasVerif/charon)
and `charon cargo --help` for the pinned version.

## 4. Translation patches

Aeneas can't translate every Rust construct (for example, iterator adaptors like `fold` when only
`Iterator::next` is modelled). Rather than give up on the item, we make a small,
behaviour-preserving edit to the Rust source so that it translates.

Each workaround is one patch file in `translation-patches/`, kept **local to this repo** (never
fetched from elsewhere). The patches are applied only to a copy of the crate at translation time.
The real Rust source is never modified. Each patch starts with a header:

```
Translation patch: <EdwardsPoint as Sum<T>>::sum

Change: `iter.fold(..)` becomes a `for item in iter` loop.
Why: Aeneas only models `Iterator::next` (aeneas#1057).
Behaviour: identical for iterators whose `fold` agrees with `next` (all std/lawful iterators).

diff --git a/src/... b/src/...
...
```

The patch changes the code that is verified, so it is part of the trusted base. That means:

- Keep each patch minimal, with one concern per file.
- The header must state the change, why it is needed (link the upstream Aeneas/Charon issue if
  there is one), and why the behaviour is unchanged.
- Each patch is **reviewed by multiple independent agents** for behaviour preservation before it is
  accepted. A human checks it in the final review.
- When an Aeneas upgrade fixes the underlying limitation, delete the patch.

To write a patch:

1. Run the translate script once, so that `.llbc/work/` holds a patched copy of the crate.
2. Make the edit in `.llbc/work/`.
3. Save it with `git diff` into `translation-patches/NN-short-name.patch`, numbered so the order
   they apply in is clear, and add the header.
4. Re-run the translate script and check that the item now translates.

The real `src/` is never patched, so merging new upstream code stays easy. After a merge, a patch
may stop applying. Then the script stops, and the patch has to be regenerated against the new code
and reviewed again.

## 5. Translate: `scripts/aeneas-translate.sh`

The script:

1. Checks that `.aeneas/` matches the `rev` in `lakefile.toml` (otherwise asks you to run the
   install script).
2. Copies the crate into `.llbc/work/` with `rsync`, leaving out `target/` and `lean/`.
3. Applies every `translation-patches/*.patch` to the copy **one after the other**, in file-name
   order, with `git apply`. If any patch fails to apply, the script stops.
4. Runs `charon cargo --preset=aeneas` on the patched copy for the single target and features we
   verify, writing `.llbc/<crate>.llbc`. Charon reads its settings from `Cargo.toml`.

   The target triple and the cargo features (and any `--cfg` flags) are fixed in the script. They
   pick one configuration of the crate, and **the proofs hold only for that configuration**. Choose
   it deliberately (usually the default features on a 64-bit target), and state it in the README
   and the spec files.
5. Runs `aeneas -backend lean -split-files -emit-json` on the LLBC, writing the generated Lean
   into `lean/<Crate>/` and `translation.json` (needed if another crate later reuses this
   translation with `-extern-crate`).

Aeneas regenerates `Funs.lean` and `Types.lean` on every run. It also emits
`*External_Template.lean` files listing the signatures of anything it needs from outside (std
functions it doesn't model, opaque items). We write those by hand in `FunsExternal.lean` and
`TypesExternal.lean`, which are kept in git.

### External functions need axioms

Aeneas only translates the crate itself. Anything it calls from outside (std functions that Aeneas'
standard library doesn't model, functions from other crates, opaque items) has no Lean body. Each
of these has to be declared in `FunsExternal.lean` (types in `TypesExternal.lean`), with its
behaviour stated as an axiom. These axioms are trusted, so:

- Keep them as few and as weak as possible, and state only what the proofs need.
- Each one is reviewed like a patch: by multiple agents, then by a human.
- Where a model is generally useful (most std functions), prefer adding it to the Aeneas standard
  library upstream, so it stops being an axiom here.

Calls into other crates the project depends on can be handled in two ways:

- Leave them as externals with axioms. This is cheap, but every function adds to what must be
  trusted.
- Translate the dependency too, and reuse its translation with `-extern-crate NAME=PATH` (see the
  Aeneas
  README section
  [Translating crates which depend on each other](https://github.com/AeneasVerif/aeneas#translating-crates-which-depend-on-each-other)).
  This is more work, but the calls are then verified rather than assumed.

Decide this per dependency, based on how much of the crate's behaviour flows through it.

For how the template files, `-split-files` and the `rust_fun`/`rust_type` attributes work, see the
Aeneas docs:
[Adding models of Rust definitions to the Lean backend](https://github.com/AeneasVerif/aeneas#adding-models-of-rust-definitions-to-the-lean-backend).

### Translating carefully

The goal is to **translate everything possible**. Work through the Charon and Aeneas output item
by item:

- For each error or skipped item, decide what to do. If it's out of scope, add it to `exclude`. If
  it's in scope, write a patch, or fix it upstream in Aeneas/Charon. Use `opaque` only as the last
  resort described above.
- Don't accept silent losses. Check that every public item we care about appears in `Funs.lean`
  with a real body.
- Rerun the translation after each change and commit the regenerated output together with the
  patches and settings that produced it.

## 6. Decide the public API specs

Once the translation is complete, we decide which public API items we care about and what each one
should guarantee. The spec statements are the part that has to be trusted, so they are reviewed
before any proof work starts:

What a statement means: Aeneas translates each function into the `Result` monad, where panics,
arithmetic overflow and out-of-bounds indexing become failure. A spec of the form
`f x ⦃ r => P r ⦄` therefore says that `f x` **terminates without panicking** and that its result
satisfies `P`. Preconditions (hypotheses on the inputs) say when the function is guaranteed not to
panic. A weaker precondition gives a stronger result.

1. Draft the statements (and the definitions they need in `Defs/`).
2. **Multiple agents review them independently.** Is each one faithful to the Rust documentation
   and the intended behaviour? Is it strong enough to be useful? Does it accidentally assume what it
   should prove?
3. **A human then checks** and signs off on the statements.

## 7. Spec files

There is one file in `Specs/` per Rust source file. It lists the file's public items in source
order. Each statement is restated (with `recall`) from its proof in `Proofs/`, followed by the
axioms that proof depends on, checked by `#print axioms`:

```lean
/-- `PartialEq for MontgomeryPoint`: equality of the encoded `u`-coordinates. -/
recall eq_spec (self other : MontgomeryPoint) :
    eq self other ⦃ (r : Bool) =>
      r = true ↔ decodeUCoordinate self.toVector = decodeUCoordinate other.toVector ⦄

/-- [propext, Classical.choice, Quot.sound, RustAx.subtle] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms eq_spec
```

So the spec file is everything a reader needs to trust the result. It shows what is claimed and
what each claim rests on: the standard Lean axioms plus any of our own (from `FunsExternal.lean` or
opaque items). The module docstring names the definitions the statements use and lists what was
not translated. If a proof starts using a new axiom, the `#guard_msgs` check fails the build.

### What must be trusted

A proved spec says something about the Rust code only if all of the following are right:

- **Tools:** Charon and Aeneas translate the Rust faithfully, and Lean's kernel checks proofs
  correctly.
- **Configuration:** the target and features chosen in the translate script. Other configurations
  are not covered.
- **Translation patches:** each one preserves behaviour.
- **Axioms:** in `FunsExternal.lean` and `TypesExternal.lean` (external and opaque items), and any
  others listed in the spec files.
- **Statements:** the definitions in `Defs/` and the statements in `Specs/` say what we mean.
- **Exclusions:** excluded items are not verified at all, and neither is anything outside the
  scope decided in §0.

The proofs themselves don't need to be read or trusted: Lean checks them.

## 8. Proofs

Proofs are added for everything else: the public specs, plus whatever lemmas about internal
functions they need. There is one file per Rust item in `Proofs/`.

1. **Complete first.** Get every spec proved with no `sorry`, by whatever works.
2. **Improve later.** Once everything is proved, go back over the proofs to make them shorter,
   more robust to translation changes and Aeneas upgrades, and better factored into reusable
   lemmas. Spec statements don't change during this phase.

## 9. CI

Two GitHub Actions workflows keep the repo honest:

- **Translation is not stale** (`.github/workflows/aeneas-translation.yml`). Runs when `src/`,
  `Cargo.toml`, `Cargo.lock`, `translation-patches/`, the scripts, `lakefile.toml` or the generated
  Lean changes. It runs `scripts/aeneas-install.sh` (caching `.aeneas/` and the nightly by the
  pinned tag), then `scripts/aeneas-translate.sh`, and fails if `git status --porcelain` shows any
  difference from what is committed. This catches a Rust change, a patch, a Charon setting or an
  Aeneas bump that was committed without regenerating the translation, and it catches hand-edits
  to generated files.
- **Lean project builds** (`.github/workflows/lean-build.yml`). Runs when anything under `lean/`,
  `lakefile.toml`, `lake-manifest.json` or `lean-toolchain` changes. It installs elan, fetches the
  Mathlib cache (`lake exe cache get`), and runs `lake build --wfail`, which treats warnings
  (including `sorry`) as errors. The build also runs the `#guard_msgs` axiom checks in `Specs/`, so
  a proof that starts using a new axiom fails CI. Cache `.lake/build` and the Aeneas package to
  keep it fast.

Together these guarantee that what is proved is the translation of the Rust code currently in the
repo.

## Workflow summary

```
scripts/aeneas-install.sh           # once, and after bumping the Aeneas rev
scripts/aeneas-translate.sh         # after any change to src/, patches, or charon settings
lake exe cache get && lake build    # check the specs and proofs
```
