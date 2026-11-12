# Formal verification of `mysql_common` (Aeneas / Lean)

This directory holds a Lean 4 verification of the part of `mysql_common` that encodes data
to, and decodes data from, the MySQL wire protocol. The Rust is translated to Lean by
[Charon](https://github.com/AeneasVerif/charon) and [Aeneas](https://github.com/AeneasVerif/aeneas),
following the process in [`../VERIFICATION.md`](../VERIFICATION.md). Spec statements about the
public API are stated in `Specs/` and proved in `Proofs/`.

**Status:** 888 spec statements, all proved, with no `sorry`. Each statement in `Specs/` is
followed by a `#guard_msgs … #print axioms` check of exactly the axioms it rests on, so the build
fails if a proof starts depending on anything new. The statements still need a final human
sign-off (see *Open items*).

## What is covered

The data path, in stages, in source order per Rust file:

| Stage | Rust | Spec file(s) |
|---|---|---|
| a. primitives | `io.rs` (`ParseBuf`, `BufMutExt` at `Vec<u8>`), `misc/mod.rs` (lenenc / varlen helpers), `misc/raw/*` (every `IntRepr`, `BytesRepr`, `RawSeq`, `RawConst`, `RawFlags`, `Skip`, `Either`, array/slice impls) | `Specs/Io.lean`, `Specs/Misc*.lean` |
| b. value wire format | `value/mod.rs`: `Value::serialize`, `bin_len`, text and binary decoding | `Specs/Value.lean` |
| c. result-set rows | `row/mod.rs` text and binary rows, `NullBitmap` | `Specs/Row.lean`, `Specs/Packets.lean` |
| d. statement params | `ComStmtExecuteRequestBuilder`, `ComStmtExecuteRequest` | `Specs/Packets.lean` |
| e. metadata / status | `Column`, OK / EOF / ERR packets, `constants.rs` (column types, flags) | `Specs/Packets.lean`, `Specs/Constants.lean` |
| f. framing | `packet_to_chunks`, `ChunkDecoder`, `PlainPacketCodec` (uncompressed) | `Specs/Proto/Codec.lean` |
| g. conversions | `value/convert/*` (`FromValue`, `From<T> for Value` for ints, bool, floats, `Duration`, strings, bytes, `Option`, uuid, chrono, time, bigint, rust_decimal, bigdecimal), `value/json` | `Specs/Value/Convert*.lean`, `Specs/Value/Json/*` |

The headline properties:
- **Exact encodings.** Each serializer appends exactly the protocol's bytes.
- **Total, exact decoding.** Every checked parser either errors or succeeds on *any* input, and
  the result and remaining buffer are characterised exactly.
- **Round trips.** Decoding an encoding gives back the value (up to documented normalisation),
  for: lenenc ints and strings, fixed-width ints, varlen ints, `Value` in binary and text
  form, text and binary rows, column definitions, OK/EOF/ERR packets, framing (including
  resuming a partial read), and every `FromValue` / `From` pair.

The definitions the statements use (`Defs/`) are written from the MySQL protocol documentation,
not transcribed from the Rust. Where the crate deliberately departs from the protocol, the spec
states the departure.

**Not covered:** binlog, auth / crypto, `collations.rs`, compression (zlib) and the compressed
`PacketCodec`, `sync_framed` I/O, `ReadMysqlExt`/`WriteMysqlExt`, `fmt`/`Debug`/`Display`,
`Value::as_sql`, `PartialEq`/`PartialOrd for Value` (float NaN semantics), the other packets
(handshake, auth switch, change user, session state), `RawFlags::parse` (binlog only), and the
generic `Serialized`/`Deserialized` JSON wrappers. Each Specs module docstring lists what it
leaves out.

## Configuration

The proofs hold for one configuration only: target `x86_64-unknown-linux-gnu` (64-bit,
little-endian), `--no-default-features --features derive,flate2/rust_backend,chrono,time,rust_decimal,bigdecimal,frunk`
(see `scripts/aeneas-translate.sh`). `flate2/rust_backend` replaces the default `zlib` C
backend, which does not cross-compile from macOS. Compression is out of scope, so the verified
code is the same either way. Aeneas is pinned in `../lakefile.toml`.

## What must be trusted

1. **Tools:** Charon and Aeneas translate the Rust faithfully, and Lean's kernel checks the
   proofs.
2. **Translation patches** (`../translation-patches/`, 52 patches). These are behaviour-preserving
   edits applied to a copy of the crate so that it translates. Each one has a
   Change / Why / Behaviour header and was reviewed by three independent agents. The patched
   copy passes the crate's own 121 library tests. Some patches go beyond small rewrites:
   - **Rust stand-ins for external crates:** an in-crate copy of `bytes::BufMut` for `Vec<u8>`
     (01, 31), the `bitflags` types written as plain structs (20), and a `Vec`-backed model of
     `BytesMut` for the plain codec (21).
   - **Public-API narrowings in the patched copy only:** `BufMutExt` is implemented only for
     `Vec<u8>` (01), the `Hash` bound on `IntRepr::Primitive` is dropped (18), `params()`
     returns a slice (28), and the codec signatures change (21).
   - **Stack use:** two loops become recursion (30), so the patched copy uses stack proportional
     to the column count.
3. **Hand-written Lean models** (`MysqlCommon/FunsExternal.lean`, `TypesExternal.lean`). Most are
   exact definitions:
   - `F32`/`F64` as bit patterns;
   - `Cow`, `Arc` (only `new`/`clone`/`deref` are used);
   - UTF-8 validation via Lean's `ByteArray.IsValidUTF8`;
   - the `btoi` integer parsers;
   - `Duration` (with its `nanos < 10^9` invariant);
   - `Uuid::from_bytes`.

   The axioms come in three kinds:
   - **Opaque types and functions that assert nothing:** `io::Error` and its constructors,
     float parsing, bignum / decimal / json, the `time` parsers and `Duration` arithmetic.
   - **One opaque function:** `core.mem.size_of`, used only by `RawFlags::SIZE`.
   - **A dozen axioms that assert behaviour of a dependency, in namespace `Trusted`**, behind the
     opaque Rust module `value::convert::trusted` (patch 40). Each was checked against the pinned
     dependency's source, and by tests:
     - the seven date/time regexes on ASCII input;
     - chrono's `NaiveDate::from_ymd_opt` / `NaiveTime::from_hms_micro_opt` validity and getters;
     - time's `Date::from_calendar_date` / `Time::from_hms_micro` validity and getters.
4. **Modelling assumptions of Aeneas:**
   - Allocation never fails, and a `Vec` may grow to `usize::MAX`. "Never panics" therefore
     means "never panics, assuming allocation succeeds".
   - Integer overflow is a panic, i.e. overflow-checked (debug) semantics. A proved
     "returns normally" spec implies no overflow occurred, so it also holds for release builds.
     Only statements that assert a panic differ in release builds.
   - Stack exhaustion is not modelled.
5. **The statements and definitions** in `Specs/` and `Defs/` say what is intended. These were
   reviewed by three independent agents per stage, then re-reviewed after revision.

Every axiom a statement uses is listed in the `#guard_msgs` check after it in `Specs/`.

## Upstream bugs and surprising behaviour found

Each item is stated as a Lean theorem, or as an explicit hypothesis or caveat in the spec, and
was confirmed against upstream `src/`:

1. **`IntRepr for VarLen::serialize` has its branches swapped.** For `x < 128` it never
   terminates (appending zeros); for `x ≥ 128` it writes one byte with the continuation bit
   set. (`misc/raw/int.rs`)
2. **`BytesRepr for VarLen` writes a lenenc length but reads a JSONB varlen length**, so lengths
   of 128 and above do not round-trip and can be misread silently. (binlog JSONB strings)
3. **The 24/40/48/56-bit signed readers do not sign-extend.** Signed `MEDIUMINT` in binlog rows
   (`binlog/value.rs:96`) decodes `-1` as `16777215`.
4. **`Value::deserialize_bin` panics (`unimplemented!`) on server-supplied column types**
   `TIMESTAMP2`, `DATETIME2`, `TIME2`, `TYPED_ARRAY` and `UNKNOWN` when the cell is not NULL.
   A server can therefore crash the client.
5. **`from_value_opt` (the non-panicking API) panics on `Bytes` holding non-ASCII Unicode
   digits**, e.g. `"00:00:00.\u{0660}"`, when converting to `Duration`, chrono
   `NaiveTime`/`NaiveDateTime`/`NaiveDate` or `time::Duration`. The cause: regex `\d` is
   Unicode-aware, but `btou(..).unwrap()` accepts only ASCII digits.
6. **`mysql_time_to_duration` computes `microseconds * 1000` in `u32`.** It overflows for
   micros > 4294967, which a server can send in a binary `TIME`: it panics in debug builds and
   gives a wrong duration in release builds.
7. **`Seq<_, LeU32/LeU64>` deserialize trusts the count read from the wire**:
   - `Vec::with_capacity(count)` can panic on capacity overflow, or abort on OOM, from a 9-byte
     input;
   - `SIZE * count` is an unchecked multiply.
8. **`ColumnMeta::catalog_ref` (and `Column::catalog_ref`) returns the schema field.**
   (`packets/mod.rs:162`)
9. **`MySerialize for Column` writes `column_length` before `character_set`**, the reverse of
   the protocol and of the crate's own reader. A serialized column reads back with wrong values
   and no error. (`packets/mod.rs:300`)
10. **Rollback of an already-typed (`Ready`) conversion does not return the original `Value`**:
    `UInt 5` as `i8` comes back as `Int 5`, `Int 7` as `bool` as `Int 1`, and `Float` as `f64` as
    `Double`.
11. **`From<Duration> for Value` can produce invalid times and wraps days**: it rounds to
    microseconds without carrying (micros can be 1000000), and truncates days with `as u32`.
12. **Year handling in the chrono and time conversions**:
    - chrono `From<NaiveDate(Time)>` panics for years outside 1000–9999;
    - time `From<Date/PrimitiveDateTime>` uses `year as u16`, so negative years wrap;
    - `Value::from(time::Duration::MIN)` panics.
13. **A text DATE can never be converted to `time::PrimitiveDateTime`**: every 10–18-byte
    string is rejected (date-only format plus `InsufficientInformation`).
14. **Quirks** (documented, not bugs):
    - `checked_eat_lenenc_int` decodes `0xFB`/`0xFF` as 0;
    - `StatusFlags` rejects bit 2;
    - lenient DATE/TIME length handling;
    - an unsigned integer accepts `"-0"`;
    - `Some(x)` with a NULL-valued `x` reads back as `None`.

## Layout

- `MysqlCommon/`: the generated translation (`Funs.lean`, `Types.lean`; never hand-edited) and
  the hand-written `FunsExternal.lean`, `TypesExternal.lean`.
- `Defs/`: definitions used to state the specs.
- `Specs/`: one file per Rust file. The public statements (`recall`ed from `Proofs/`), each with
  its axiom check. `Specs/Defs*.lean` recall the sanity lemmas about the definitions.
- `Proofs/`: one file per Rust item; `Proofs/Util/` holds shared helper lemmas.

## Reproducing

```
scripts/aeneas-install.sh        # pinned charon + aeneas, Rust nightly, lean-toolchain
scripts/aeneas-translate.sh      # regenerate the translation (must leave git clean)
lake exe cache get && lake build # check every proof and axiom guard
```

## Open items

- **Human sign-off of the statements** (VERIFICATION.md §6). Each stage was reviewed by agents,
  but a person has not yet signed off. One statement changed after review, because its proof
  showed it false: `RawSeq::into_owned_spec` now assumes the element type's `Clone` is the
  identity, which is true for every primitive the crate uses.
- Some statements are stronger in their hypotheses than necessary (noted in their docstrings),
  e.g. `BareBytes::serialize_spec` bounds the untruncated length. They are true as stated.
- The upstream bugs above should be reported to the crate's maintainers.
