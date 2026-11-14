# Status of the verification of `mysql_common` (Aeneas / Lean)

The details behind [`../README.md`](../README.md). `formal/` holds a Lean 4 verification of the part of `mysql_common` that encodes data
to, and decodes data from, the MySQL wire protocol and the binlog. The Rust is translated to Lean
by [Charon](https://github.com/AeneasVerif/charon) and [Aeneas](https://github.com/AeneasVerif/aeneas),
following the process in `VERIFICATION.md` (the method, kept outside this repo). Spec statements
about the public API are stated in `Specs/` and proved in `Proofs/`.

Paths below such as `Specs/…`, `Defs/…` and `Proofs/…` name the Lean module folders: `Defs/` and
`Specs/` are in `formal/specs/`, `Proofs/` in `formal/proofs/`.

**Status:** 2177 spec statements, all proved, with no `sorry`; `lake build --wfail` is clean and
the translation is reproducible. Each statement in `Specs/` is followed by a
`#guard_msgs … #print axioms` check of exactly the axioms it rests on, so the build fails if a
proof starts depending on anything new. The statements still need a final human sign-off (see
*Open items*).

## What is covered

In stages, in source order per Rust file:

| Stage | Rust | Spec file(s) |
|---|---|---|
| a. primitives | `io.rs` (`ParseBuf`, `BufMutExt` at `Vec<u8>`), `misc/mod.rs` (lenenc / varlen helpers, `split_version`), `misc/raw/*` (every `IntRepr`, `BytesRepr`, `RawSeq`, `RawConst`, `RawFlags`, `Skip`, `Either`, array/slice impls) | `Specs/Io.lean`, `Specs/Misc*.lean` |
| b. value wire format | `value/mod.rs`: `Value::serialize`, `bin_len`, text and binary decoding | `Specs/Value.lean` |
| c. result-set rows | `row/mod.rs`: text and binary rows, `NullBitmap`, row access (`get`, `take`, `Index`, `ColumnIndex`) | `Specs/Row.lean`, `Specs/Packets.lean` |
| d. statement params | `ComStmtExecuteRequestBuilder`, `ComStmtExecuteRequest` | `Specs/Packets.lean` |
| e. metadata / status | `Column`, OK / EOF / ERR packets, `constants.rs` (column types, flags) | `Specs/Packets.lean`, `Specs/Constants.lean` |
| f. framing | `packet_to_chunks`, `ChunkDecoder`, `PlainPacketCodec` | `Specs/Proto/Codec.lean` |
| g. conversions | `value/convert/*` (`FromValue`, `From<T> for Value` for ints, bool, floats, `Duration`, strings, bytes, `Option`, uuid, chrono, time, bigint, rust_decimal, bigdecimal), `value/json` | `Specs/Value/Convert*.lean`, `Specs/Value/Json/*` |
| h. row conversion | `row/convert/*`: `FromRow` for `Row`, `T: FromValue`, tuples of arity 1–12, `HNil` | `Specs/Row/Convert*.lean` |
| i. SQL text | `named_params.rs`, `params.rs`, `Value::as_sql` / `escaped` | `Specs/NamedParams.lean`, `Specs/Params.lean`, `Specs/Value/AsSql.lean` |
| j. compression | `compress`, `CompDecoder`, `CompPacketCodec`, `PacketCodec` (flate2) | `Specs/Proto/Codec.lean` |
| k. connection phase | handshake, `HandshakeResponse`, `SslRequest`, auth switch / more data, `ComChangeUser`, `PublicKeyRequest` / `Response` (`caching_sha2_password`), `LocalInfilePacket` | `Specs/Packets/Connection.lean`, `Specs/Packets/CachingSha2Password.lean` |
| l. statements / session | `StmtPacket`, `ComStmtSendLongData`, `ComStmtClose`, MariaDB bulk execute, `SessionStateInfo`, `session_state_change.rs` | `Specs/Packets/StmtBinlog.lean`, `Specs/Packets/SessionStateChange.lean` |
| m. replication commands | `ComRegisterSlave`, `ComTableDump`, `ComBinlogDump`, `ComBinlogDumpGtid` (untagged and tagged SIDs), `GnoInterval`, `Sid`, `Tag`, `SemiSyncAckPacket`, `BinlogRequest` | `Specs/Packets/StmtBinlog.lean`, `Specs/Packets/BinlogRequest.lean` |
| n. binlog | `binlog/consts.rs`, `misc.rs` (packed DATETIME2 / TIME2 / TIMESTAMP2), `value.rs` (`BinlogValue`), `row.rs` (`BinlogRow` accessors), `events/mod.rs` (header, footer, dispatch) and every translated event type | `Specs/Binlog/**` |

The headline properties:
- **Exact encodings.** Each serializer appends exactly the protocol's bytes.
- **Total, exact decoding.** Every checked parser either errors or succeeds on *any* input, and
  the result is characterised exactly (panics, where they exist, are stated exactly).
- **Round trips.** Decoding an encoding gives back the value (up to documented normalisation),
  for every encoder/decoder pair above, including the codecs (`PacketCodec.encode_decode_plain`
  / `_comp`, resuming a partial read) and every binlog event with a translated reader.

The definitions the statements use (`Defs/`) are written from the MySQL protocol documentation
and, for the binlog, MySQL's source (`mysys/my_time.cc`, `log_event.cc`, `Field_*`), not
transcribed from the Rust. Where the crate departs from them, the spec states the departure.

**Not covered:** auth crypto (`AuthPlugin::init`), `collations.rs`, `sync_framed` I/O,
`ReadMysqlExt`/`WriteMysqlExt`, `fmt`/`Debug`/`Display`, `PartialEq`/`PartialOrd for Value`,
`RawFlags::parse`, the generic `Serialized`/`Deserialized` JSON wrappers, `FromRow for HCons`;
in the binlog: `Event::read`/`write`/checksums, `MyDeserialize for BinlogRow`, JSONB / JSON diff /
decimal decoding, `UserVarEvent`, the tagged GTID event format, `TransactionPayloadEvent::deserialize`
and zstd, the table map's optional metadata, the `bitvec` views. Each Specs module docstring
lists what it leaves out.

## Configuration

The proofs hold for one configuration only: target `x86_64-unknown-linux-gnu` (64-bit,
little-endian), `--no-default-features --features derive,flate2/rust_backend,chrono,time,rust_decimal,bigdecimal,frunk,binlog_core`
(see `scripts/aeneas-translate.sh`). Aeneas is pinned in `formal/lakefile.toml`.
- `flate2/rust_backend` (miniz_oxide) replaces the default `zlib` C backend, which does not
  cross-compile from macOS. The flate2 axioms were checked against flate2 1.1.11 / miniz_oxide
  0.9.1 (`PINNED_DEPS`) and hold for this build only, not the zlib one.
- `binlog_core` exists only in the patched copy (patch 140): there `binlog = ["binlog_core",
  "dep:zstd"]`, and the zstd uses (a C library) go through the opaque `binlog::trusted`. Only
  the untranslated zstd decompression API differs.

Statements that need `usize` to be 64-bit take the hypothesis `Target64` (the configuration is
x86_64) rather than an axiom; the rows-event readers also take `core.mem.size_of Std.U16 = ok
2#usize`.

## What must be trusted

1. **Tools:** Charon and Aeneas translate the Rust faithfully, and Lean's kernel checks the
   proofs.
2. **Translation patches** (`formal/trusted/patches/`, 107 patches). These are behaviour-preserving
   edits applied to a copy of the crate so that it translates. Each one has a
   Change / Why / Behaviour header and was reviewed by independent agents (three per round). With
   all 107 patches applied, the patched copy passes the crate's 121 library tests (`cargo test
   --lib`, features `test,chrono,time,rust_decimal,bigdecimal,frunk,binlog`). Some patches go
   beyond small rewrites:
   - **Rust stand-ins for external crates:** an in-crate copy of `bytes::BufMut` for `Vec<u8>`
     (01, 31, 152), the `bitflags` types as plain structs (20, 61, 142), and a `Vec`-backed model
     of `BytesMut` for both codecs (21, 123).
   - **Trust-boundary modules** (opaque in Cargo.toml, one dependency call per function):
     `value::convert::trusted` (40), `misc::trusted` (64), `sql_trusted` (80),
     `proto::codec::trusted` (120), `binlog::trusted` (140).
   - **Public-API narrowings in the patched copy only:** `BufMutExt` only for `Vec<u8>` (01), no
     `Hash` bound on `IntRepr::Primitive` (18), `params()` returns a slice (28), the codec
     signatures (21, 123).
   - **A changed check:** patch 156 checks a GTID tag read from the wire bytewise instead of via
     `Tag::new` (`str::chars` has no model); equivalent, tested differentially.
   - **Stack use:** many loops become recursion (e.g. 30, 70, 83, 102, 144, 147, 148), so the
     patched copy uses stack proportional to columns, attributes, SIDs, status variables, ….
3. **Hand-written Lean models** (`formal/trusted/MysqlCommon/FunsExternal.lean`,
   `TypesExternal.lean`). Most are
   exact definitions: `F32`/`F64` as bit patterns; `Cow`; `Arc` as its value (sound only for
   `new`/`clone`/`deref`/`make_mut`); UTF-8 validation via `ByteArray.IsValidUTF8`; the `btoi`
   parsers; `Duration`; `Uuid::from_bytes`; `u8::try_from(u64)`, `i128::to_string`,
   `str::as_bytes`; the `sql_trusted` string and `format!` helpers; `Compression` as its level.

   The axioms come in three kinds:
   - **Opaque types and values that assert nothing:** `io::Error` and its constructors, float
     parsing and `Display`, bignum / decimal / json, the `time` parsers, `from_utf8_lossy` of
     invalid UTF-8, the `Display`/`Debug` impls, the binlog's JSONB / JSON diff / decimal readers,
     `UserVarEvent`, the tagged GTID format, `TransactionPayloadEvent::deserialize`,
     `binlog::trusted` (tags, `bytes_remaining_error`, `timestamp2_frac_bytes`).
   - **Opaque values assumed only to return (not panic):** `Trusted.readExactEofError` (std's
     `READ_EXACT_EOF`), `Trusted.userVarIntoOwned`, `Trusted.tagIntoOwned`, and
     `Trusted.sidTagInvalidError` (patch 156; its `unreachable!` is unreachable only at its single
     call site, so the model is sound only there).
   - **`core.mem.size_of`**, opaque; it identifies Rust types sharing a Lean type, so it is only
     applied to integer types, and its value is taken as a hypothesis where needed (above).
   - **Axioms asserting behaviour of a dependency, namespace `Trusted`:**
     - *value conversions* (`value::convert::trusted`): the seven date/time regexes, exact on
       ASCII (`isMatch_ascii`) and of the pattern's shape on any input (`isMatch_loose`: a `\d`
       is one ASCII digit or at least two bytes `≥ 128`; fuzzed on ~494M inputs); chrono's and
       time's date/time constructors (validity and getters); time's `SignedDuration` (an opaque
       `durNanos`, and per operation when it returns and with what value; only the cases the
       proofs use);
     - *flate2* (`proto::codec::trusted`): opaque streams and results (`compressNew`,
       `decompressNew`, `deflateResult`/`State`, `inflateResult`/`State`, `vecCapacity`) and three
       properties: a successful deflate is non-empty and shorter (`deflateResult_short`), a
       successful inflate has the declared length (`inflateResult_len`), and inflating
       flate2's own deflate output gives the input back (`inflate_deflate`). Nothing is assumed
       about errors or about other zlib implementations' output;
     - *HashMap*: `Params::Named`'s map (`sql_trusted`: `paramsMapEntries` with distinct keys,
       `Empty`/`Insert`/`Remove` up to permutation) and the connect attributes (`misc::trusted`:
       opaque operations, only `connectAttrsEntries_new`, a new map is empty);
     - *version regexes* (`misc::trusted`): `versionReCaptures`/`mariadbVersionReCaptures`,
       opaque, exact on ASCII (`_ascii`), checked against `regex` 1.13.1 on 621 856 inputs
       (`formal/trusted/evidence/RegexEval/`).

   The property axioms were checked against the pinned dependency's source and by tests, by the
   author and independent reviewers. `Proofs/Consistency/` gives models of the `HashMap`
   (`ParamsMap.lean`), connect-attribute and version-regex axioms (`ConnTrusted.lean`), so they
   cannot prove `False`.
4. **Modelling assumptions of Aeneas:**
   - Allocation never fails, and a `Vec` may grow to `usize::MAX`. "Never panics" means "never
     panics, assuming allocation succeeds". Where the crate allocates from a count read from the
     wire, real Rust aborts or panics (capacity overflow) where the model returns `Err`:
     `ComBinlogDumpGtid` (`n_sids`), `Sid` intervals, `PreviousGtidsEvent`, `Seq<_, LeU32/LeU64>`.
   - Integer overflow is a panic, i.e. debug semantics. A proved "returns normally" spec implies
     no overflow occurred, so it also holds for release builds; only statements that assert a
     panic differ (release wraps).
   - Stack exhaustion is not modelled.
   - `HashMap` iteration order is a function of the map in any Lean model, but random in Rust:
     no statement relates the order, bytes or equality of separately built maps.
5. **The statements and definitions** in `Specs/` and `Defs/` say what is intended. These were
   reviewed by three independent agents per stage, then re-reviewed after revision.

Every axiom a statement uses is listed in the `#guard_msgs` check after it in `Specs/`.

## Upstream bugs and surprising behaviour found

Each item is stated as a Lean theorem, or as an explicit hypothesis or caveat in the spec, and
was confirmed against upstream `src/`. Trigger: who can cause it (*server*: data from the server
or binlog; *client*: a packet sent to a server-side user of the crate; *caller*: the API user).

| # | Where | What goes wrong | Trigger |
|---|---|---|---|
| 1 | `IntRepr for VarLen::serialize` (`misc/raw/int.rs`) | branches swapped: never terminates for `x < 128`, one byte with the continuation bit for `x ≥ 128` | caller |
| 2 | `BytesRepr for VarLen` | writes a lenenc length, reads a JSONB varlen: lengths ≥ 128 misread silently | caller |
| 3 | `eat_i24/i40/i48/i56` | no sign extension: binlog signed `MEDIUMINT` `-1` reads as `16777215` (`binlog/value.rs:96`) | server |
| 4 | `Value::deserialize_bin` | `unimplemented!` panic on non-NULL `TIMESTAMP2`/`DATETIME2`/`TIME2`/`TYPED_ARRAY`/`UNKNOWN` columns | server |
| 5 | `from_value_opt` (Duration, chrono, `time::Duration`) | panics on non-ASCII Unicode digits (`"00:00:00.\u{0660}"`): Unicode `\d` + `btou(..).unwrap()` | server |
| 6 | `mysql_time_to_duration` | `micros * 1000` in `u32`: panic (debug) / wrong value (release) for micros > 4294967 | server |
| 7 | `Seq<_, LeU32/LeU64>::deserialize` | trusts the wire count: `with_capacity` panic/abort from 9 bytes; unchecked `SIZE * count` | server |
| 8 | `ColumnMeta::catalog_ref`, `Column::catalog_ref` (`packets/mod.rs:162`) | returns the schema field | caller |
| 9 | `MySerialize for Column` (`packets/mod.rs:300`) | writes `column_length` before `character_set`: reads back wrong, no error | caller |
| 10 | `ParseIrOpt::rollback` of `Ready` | does not restore the value (`UInt 5` as `i8` → `Int 5`; `Float` as `f64` → `Double`) | caller |
| 11 | `From<Duration> for Value` | rounds to micros without carry (micros = 1000000), days truncated `as u32` | caller |
| 12 | chrono / time `From<Date…> for Value` | chrono panics outside years 1000–9999; time wraps negative years (`as u16`); `time::Duration::MIN` panics | caller |
| 13 | `FromValue for time::PrimitiveDateTime` | every 10–18-byte string (a text `DATE`) is rejected | server |
| 14 | `FromRow` for tuples (`row/convert/mod.rs`, `take_or_place!`) | on a taken later cell, earlier converted cells are not put back: data lost | caller |
| 15 | `Value::as_sql` | `24·days + hours` in `u32`: panic for days ≥ 178956971 | caller |
| 16 | `Value::as_sql` / `escaped` | escaping not charset-aware: with gbk/big5/gb18030/sjis/cp932 a `'` ends the literal (SQL injection) | caller |
| 17 | `ParsedNamedParams::parse` | byte after lone `/`, `-`, a placeholder not re-examined: `x/'a:b'` substitutes inside a string, `1-:a` missed, `:a?` not reported mixed, `/**/` swallows the rest | caller |
| 18 | compressed `compress` / `encode` | `max_allowed_packet = 0` panics (`chunks(0)`) | caller |
| 19 | `PacketCodec::compress(level)` | level > 10 accepted, first deflate panics (debug, miniz_oxide `debug_assert!`) | caller |
| 20 | `CompPacketCodec::encode` after a failed deflate | earlier pieces stay in `out_buf` and are sent twice; plain seq id advanced, compressed not | caller |
| 21 | `CompDecoder` after a failed inflate | header consumed but state stays pending: later calls misread the stream | server |
| 22 | `HandshakePacket::deserialize` | length byte 128–135: `as i8 - 8` overflows, panic (debug; also from the crate's own 120–127-byte scramble) | server |
| 23 | `HandshakePacket::deserialize` | length byte ≥ 136 reads 13 scramble bytes instead of `b - 8` (misreads its own 128–247-byte scramble) | server |
| 24 | `server_version_parsed`, `maria_db_server_version_parsed` | panic on non-ASCII Unicode digits (regex `\d` + `btoi(..).unwrap()`) | server |
| 25 | `ComStmtBulkExecuteRequestBuilder::new` | `max_allowed_packet - 4` underflows for values < 4 | caller |
| 26 | `ComStmtBulkExecuteRequest::deserialize` | type `SIZE` is 3 for a 2-byte type: misaligned, misreads the crate's own packets | client |
| 27 | `ComStmtBulkExecuteRequest::deserialize` | reads only the first row, reads a value after `DEFAULT`/`IGNORE`, panics on unsupported types | client |
| 28 | bulk type merging | keeps the first type, unites flags: `Int(-1)` with a `UInt` sent as `LONGLONG UNSIGNED` (`2^64 - 1`) | caller |
| 29 | `ComBinlogDumpGtid::deserialize`, `Sid` intervals | `with_capacity` of a wire count before checking it: abort from a ~24–31-byte packet | client |
| 30 | binlog `PreviousGtidsEvent::deserialize` | `with_capacity` of the SID / interval counts from the wire: panic or abort from 24 bytes | server |
| 31 | binlog `Event::read` (not translated) | panics on truncated input (`read_exact(..).unwrap()`) and on data shorter than the checksum (`len - 4`) | server |
| 32 | binlog `Event` `checksum()`/`len`/`write` | ignore `checksum_enabled`: events inside a transaction payload report `Some([0; 4])` and 4 extra bytes | server |
| 33 | binlog GTID reader | leaves MySQL 8.0.33+'s `commit_group_ticket` unread, so `read_event` fails on such events | server |
| 34 | binlog `len` vs `serialize` | `RandEvent` 8 vs 16; `GtidEvent` always counts the logical clock; v1 rows +2; `ExecuteLoadQueryEvent` caps at 65522; `TransactionPayloadEvent::new` ignores the header; `TableMapEvent` counts `(n + 8) / 7` bitmap bytes | caller |
| 35 | `QueryEvent` `Q_MICROSECONDS` | sliced as 3 bytes, read as `u32`: never decodes | server |
| 36 | `QueryEvent` `Q_UPDATED_DB_NAMES` | NUL terminator not skipped: every name after the first is empty | server |
| 37 | `StatusVarsIterator` | not fused (yields from inside a failed variable); a db-names count of 254 loses all later variables | server |
| 38 | binlog `my_time_packed_from_binary` (TIME2, 1–2 digits) | `frac -= 0x100` in `u32`: negative value with a fraction panics (debug) / wrong (release) | server |
| 39 | binlog `TableMapEvent` / `BinlogValue` (`value.rs:59`) | `TYPED_ARRAY` metadata returned without the element type byte, which the decoder reads as `col_meta[0]` | server |
| 40 | `BinlogValue` pre-5.6.4 `TIME` | read unsigned and hours `as u8`: negative times and hours ≥ 256 misread | server |
| 41 | `BinlogValue` / packed DATETIME2 | panics on short metadata (index), on `TYPED_ARRAY` without metadata, on DATETIME2 integer part 0 (`i64` overflow / negation) | server |
| 42 | `BinlogValue` `YEAR` | byte 0 (year `0000`) reads as `"1900"` | server |
| 43 | `TryFrom<u64>` for `TransactionPayloadFields` / `…CompressionType`; `TransactionPayloadEvent::deserialize` | panic on unknown values ≥ 256, unknown compression code, or truncated unknown field | server |

**Quirks** (documented, not bugs): `checked_eat_lenenc_int` decodes `0xFB`/`0xFF` as 0;
`StatusFlags` rejects bit 2; lenient DATE/TIME lengths; an unsigned integer accepts `"-0"`;
`Some(x)` with a NULL-valued `x` reads back as `None`; `split_version` accepts a sign in the first
two parts and its failure equals `0.0.0`; `compress` of an empty `src` returns seq id 0;
`Params::into_values` sometimes reports the last missing name instead of the first, and
`into_positional` does not check names; `as_sql` prints out-of-range dates and NaN/`inf`;
`ComChangeUser` always writes connect attributes; `parse_parsec_salt` needs exactly 20 bytes;
`BinlogRequest::filename` is not lossy as documented; uppercase GTID tags are rejected (MySQL
lowercases them); `EventType` rejects `0x29` (`HEARTBEAT_LOG_EVENT_V2`); `RowsQueryEvent` writes
length byte 0; the `Gno` range doc says `[MIN, MAX]` where the code (correctly, as MySQL) uses
`[MIN, MAX)`.

## Layout

- `formal/translation/MysqlCommon/`: the generated translation (`Funs.lean`, `Types.lean`; never
  hand-edited), with `translation.json` and the root `MysqlCommon.lean`.
- `formal/trusted/MysqlCommon/`: the hand-written `FunsExternal.lean`, `TypesExternal.lean`
  (modules `MysqlCommon.FunsExternal`/`TypesExternal`, library `MysqlCommonExternal`).
- `formal/trusted/patches/`: the translation patches; `formal/trusted/evidence/RegexEval/`: the
  differential test of the version-regex axioms (not part of the build).
- `formal/specs/Defs/`: definitions used to state the specs.
- `formal/specs/Specs/`: one file per Rust file. The public statements (`recall`ed from `Proofs/`), each with
  its axiom check. `Specs/Defs*.lean` recall the sanity lemmas about the definitions.
- `formal/proofs/Proofs/`: one file per Rust item; `Proofs/Util/` holds shared helper lemmas;
  `Proofs/Consistency/` the models of the trusted axioms.

## Reproducing

```
scripts/aeneas-install.sh               # pinned charon + aeneas, Rust nightly, lean-toolchain
scripts/aeneas-translate.sh             # regenerate the translation (must leave git clean)
cd formal && lake exe cache get && lake build --wfail   # check every proof and axiom guard
```

## Open items

- **Human sign-off of the statements** (`VERIFICATION.md` §6, kept outside this repo). Each stage was reviewed by agents,
  but a person has not yet signed off. One statement changed after review, because its proof
  showed it false: `RawSeq::into_owned_spec` now assumes the element type's `Clone` is the
  identity, which is true for every primitive the crate uses.
- `Specs/Packets/Connection.lean` and `Specs/Packets/StmtBinlog.lean` should be merged into
  `Specs/Packets.lean` (one file per Rust file), and `Specs/Value/AsSql.lean` into `Specs/Value.lean`.
- A few hypotheses remain stronger than necessary (noted in their docstrings): `Target64` on
  the composite readers where only the base lenenc readers have the exact `hfit` form, and the
  `dst + src + 2^24` bound in `PlainPacketCodec.decode_spec` for chunks after the first.
- Off ASCII the date/time and version regexes are only described by shape (or not at all), so
  the panic statements characterise when a panic happens but no theorem exhibits a concrete
  panicking string.
- The upstream bugs above should be reported to the crate's maintainers.
