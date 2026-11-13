import Proofs.Binlog.Value.BinlogValue

/-!
# `src/binlog/value.rs`
    `BinlogValue`: `into_owned` and the row-value decoder `MyDeserialize for BinlogValue`, with
    context `(column type, column metadata, is_unsigned, is_partial)`, per column type, against
    MySQL's binlog row formats (`Defs/BinlogValue.lean`).

    **Configuration.** As in `Specs/Binlog/Mod.lean`. The decoder statements take `Target64` (the
    integer types go through `Value::deserialize_bin`, whose statement takes it).

    Panics are stated as equations `f x = fail e` (see `Specs/Value.lean`).

    **Allocation caveat.** As in `Specs/Value.lean` (decoded byte strings are copied).

    **Definitions used.** `Defs/BinlogValue.lean` (`binlogRead`, `BinlogOut`, `binlogBug`,
    `binlogEffType`, `binlogEnc`, `binlogEncBug`, `binlogValView`, `resMap`, `stringFieldLen`,
    `oldTimeVal`), `Defs/BinlogCore.lean` (`time2NegFracBug`, `timestamp2Read`,
    `timestamp2Bin`, packed temporal formats), `Defs/Value.lean` (`Val`, `binRead`),
    `Defs/Convert.lean` (`decimalBytes`), `Defs/LenEnc.lean` (`checkedLenPrefixed`),
    `Defs/Bytes.lean`.

    **Trusted axioms.** None of the `Trusted.*` axioms. The decoder calls these opaque functions
    (nothing is assumed about them; the statements expose the calls): `binlog.jsonb.parse_jsonb_value`,
    `binlog.jsondiff.parse_json_diffs` (JSON), `binlog.decimal.read_bin_to_string_bytes`
    (NEWDECIMAL), `binlog.trusted.timestamp2_frac_bytes` (`format!("{}.{:06}", sec, usec)`, for a
    TIMESTAMP2 with a fraction), `binlog.trusted.read_exact_eof` (the error value of the temporal
    readers: `ok Trusted.readExactEofError`, an opaque value), and `into_owned` calls `binlog.jsonb.Value.into_owned`,
    `binlog.jsondiff.json_diffs_into_owned`. `YEAR`/`TIMESTAMP2` text goes through
    `i128::to_string`/`String::into_bytes`, modelled exactly in `FunsExternal.lean`.

    **Not covered.** `TryFrom<BinlogValue> for Value` (JSONB to JSON text through `serde_json`;
    excluded in Cargo.toml), the JSON, NEWDECIMAL and TIMESTAMP2-fraction decoders themselves
    (opaque modules), derived `Clone`/`PartialEq`, `Debug`. Which column type and metadata a row
    column has comes from the table map event (events half): ENUM and SET columns arrive here
    already resolved by `TableMapEvent::get_column_type` (a STRING column is read as a string,
    whatever its real-type byte, e.g. `0xF7`).

    **Behaviour to note.**
    * **Bug** (signed MEDIUMINT, `value.rs:96`): `RawInt<LeI24>` does not sign-extend, so a
      negative signed INT24 decodes as its value plus `2^24` (`-1` as `16777215`).
    * **Bug** (pre-5.6.4 TIME): MySQL ≤ 5.7's `Field_time` stores a 3-byte signed `±HHMMSS`
      (`int3store`/`sint3korr`); the crate reads it unsigned (mysqlbinlog itself reads
      `uint3korr`, `log_event.cc:1981`; the crate additionally truncates the hours `as u8`):
      negative times are misread and hours from 256 (MySQL allows up to 838) wrap. With days 0
      (the crate's representation of this type), no `Value` represents 256–838 hours.
    * **Bug** (TIME2 with 1–2 fractional digits): negative values with a fraction panic (see
      `Specs/Binlog/Misc.lean`). A server can crash the client.
    * **Panics on malformed metadata** (index out of bounds): metadata shorter than the column type
      needs (`binlogMetaLen`), and a `TYPED_ARRAY` with no metadata. And on the invalid DATETIME2
      integer part 0 with a non-positive fraction (`i64` overflow).
    * **Bug** (YEAR `0000`): MySQL stores the year `0000` as the byte 0 and its value is 0
      (`Field_year`; `SELECT` returns `0000`); the crate reads it as `"1900"` (only
      `mysqlbinlog` prints 1900, `log_event.cc:2033`).
    * **Quirks:** a STRING metadata whose first byte (the real type) is 0 is read as a little-endian
      `u16` length (`stringFieldLen`); TIMESTAMP2 seconds and 1–2-digit fraction bytes are read as
      signed (`timestamp2Read`).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `enum BinlogValue and its impls` -/

/-- `into_owned`: a plain value is returned unchanged; JSON values go through the opaque `into_owned` of their modules. -/
recall binlog.value.BinlogValue.into_owned_eq (self : binlog.value.BinlogValue) :
    binlog.value.BinlogValue.into_owned self =
      (match self with
       | .Value v => ok (.Value v)
       | .Jsonb x => binlog.jsonb.Value.into_owned x >>= fun y => ok (.Jsonb y)
       | .JsonDiff x => binlog.jsondiff.json_diffs_into_owned x >>= fun y => ok (.JsonDiff y))

/-- [propext, Classical.choice, Quot.sound, binlog.jsonb.Value, binlog.jsondiff.JsonDiff, binlog.jsondiff.json_diffs_into_owned, binlog.jsonb.Value.into_owned] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.into_owned_eq
/-- `MyDeserialize for BinlogValue`: `SIZE` is `None`. -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.SIZE_eq :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.SIZE_eq
/-- `deserialize`: when `binlogRead` gives a value (and the input is not one of the crate's bugs, `binlogBug`), the crate returns that value (`BinlogValue::Value`) and leaves the same rest. -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_ok (h64 : Target64)
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (v : Val) (rest' : List U8) (hr : binlogRead ct md.val uns buf.val = .ok v rest')
    (hb : ¬ binlogBug ct md.val uns buf.val) :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf ⦃ r rest =>
      (okPart r).map binlogValView = some (some v) ∧ rest.val = rest' ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_ok
/-- `deserialize`: when `binlogRead` gives an error, the crate returns an error and leaves the same rest. -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_err (h64 : Target64)
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (rest' : List U8) (hr : binlogRead ct md.val uns buf.val = .err rest') :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf ⦃ r rest => okPart r = none ∧ rest.val = rest' ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_err
/-- **Crash paths.** `deserialize` panics when `binlogRead` says so: metadata too short for the column type (index out of bounds), and the invalid DATETIME2 integer part 0 with a non-positive fraction (`i64` overflow). -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_panics
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (e : Error) (hr : binlogRead ct md.val uns buf.val = .panic e) :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf = fail e

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_panics
/-- `deserialize` of a JSON column: a 4-byte little-endian length `n`, then `n` bytes handed to the opaque binary-JSON parser (`parse_jsonb_value`; `parse_json_diffs` for a partial update, `is_partial`), whose result is wrapped as `Jsonb`/`JsonDiff`; the rest after the `n` bytes is left (whatever the parser consumes). The metadata is not read. -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_json (h64 : Target64)
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hj : binlogEffType ct md.val = .MYSQL_TYPE_JSON) (n : Nat) (r : List U8)
    (hl : readLE 4 buf.val = some (n, r)) (hn : n ≤ r.length) :
    ∃ pb rb : io.ParseBuf, pb.val = r.take n ∧ rb.val = r.drop n ∧
      binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf =
        (if part then
          binlog.jsondiff.parse_json_diffs pb >>= fun x => ok (resMap .JsonDiff x, rb)
        else
          binlog.jsonb.parse_jsonb_value pb >>= fun x => ok (resMap .Jsonb x.1, rb))

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_json
/-- `deserialize` of a JSON column with a short input: an error, leaving the input unchanged if the length is missing, else the bytes after the length. -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_json_short (h64 : Target64)
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hj : binlogEffType ct md.val = .MYSQL_TYPE_JSON)
    (hs : ∀ n r, readLE 4 buf.val = some (n, r) → r.length < n) :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf ⦃ r rest =>
      okPart r = none ∧
        rest.val = (match readLE 4 buf.val with | some (_, r) => r | none => buf.val) ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_json_short
/-- `deserialize` of a NEWDECIMAL column: the opaque decimal reader on the input, with the precision and scale from the metadata, its text wrapped as `Bytes`. -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_decimal
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hd : binlogEffType ct md.val = .MYSQL_TYPE_NEWDECIMAL) (m0 m1 : U8) (t : List U8)
    (hm : md.val = m0 :: m1 :: t) (p s : Usize) (hp : p.val = m0.val) (hs : s.val = m1.val) :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf =
      (binlog.decimal.read_bin_to_string_bytes buf p s >>= fun x =>
        ok (resMap (fun d => binlog.value.BinlogValue.Value (.Bytes d)) x.1, x.2))

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_decimal
/-- `deserialize` of a TIMESTAMP2 column with a non-zero fraction: the text the opaque `timestamp2_frac_bytes(sec, usec)` gives (the crate's `format!("{}.{:06}", sec, usec)`), as `Bytes`, leaving the rest after the value. -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_timestamp2_frac
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (ht : binlogEffType ct md.val = .MYSQL_TYPE_TIMESTAMP2) (d : U8) (t : List U8)
    (hm : md.val = d :: t) (sec usec : I32) (rest' : List U8)
    (hr : timestamp2Read d.val buf.val = some ((sec.val, usec.val), rest')) (hu : usec.val ≠ 0) :
    ∃ rb : io.ParseBuf, rb.val = rest' ∧
      binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf =
        (binlog.trusted.timestamp2_frac_bytes sec usec >>= fun b =>
          ok (.Ok (binlog.value.BinlogValue.Value (.Bytes b)), rb))

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_timestamp2_frac
/-- TIMESTAMP2 round trip with a fraction: on MySQL's encoding (`timestamp2Bin`) of a timestamp in range (seconds `0 ≤ sec < 2^31`) with a non-zero fraction representable at `dec`, the decoder hands exactly the seconds and microseconds to the opaque formatter `timestamp2_frac_bytes` and leaves the rest after the value. -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_timestamp2_frac_roundtrip
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (ht : binlogEffType ct md.val = .MYSQL_TYPE_TIMESTAMP2) (d : U8) (t : List U8)
    (hm : md.val = d :: t) (sec usec : I32) (hs : 0 ≤ sec.val)
    (hu : 0 < usec.val ∧ usec.val < 10 ^ 6 ∧ usec.val % (fracUnit d.val : Int) = 0)
    (tail : List U8) (h : buf.val = timestamp2Bin d.val sec.val.toNat usec.val.toNat ++ tail) :
    ∃ rb : io.ParseBuf, rb.val = tail ∧
      binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf =
        (binlog.trusted.timestamp2_frac_bytes sec usec >>= fun b =>
          ok (.Ok (binlog.value.BinlogValue.Value (.Bytes b)), rb))

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_timestamp2_frac_roundtrip
/-- Round trip: `deserialize` reads back MySQL's binlog encoding (`binlogEnc`) of every value a column of that type and metadata holds, except the bug cases (`binlogEncBug`: negative signed INT24; negative or ≥ 256-hour pre-5.6.4 TIME; negative TIME2 with 1–2 fractional digits and a fraction). -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_roundtrip (h64 : Target64)
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (v : Val) (bs tail : List U8) (he : binlogEnc ct md.val uns v = some bs)
    (hb : ¬ binlogEncBug ct md.val uns v) (h : buf.val = bs ++ tail) :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf ⦃ r rest =>
      (okPart r).map binlogValView = some (some v) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_roundtrip
/-- **Bug** (signed MEDIUMINT, `value.rs:96`). A signed INT24 is the 3 bytes zero-extended (`RawInt<LeI24>` does not sign-extend), where MySQL (`sint3korr`) sign-extends: a negative value comes back as itself plus `2^24`. -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_int24_signed (h64 : Target64)
    (ct : constants.ColumnType) (md : Slice U8) (part : Bool) (buf : io.ParseBuf)
    (ht : binlogEffType ct md.val = .MYSQL_TYPE_INT24) (hl : 3 ≤ buf.length) :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, false, part) buf ⦃ r rest =>
      (okPart r).map binlogValView = some (some (.int (leNat (buf.val.take 3)))) ∧
        rest.val = buf.val.drop 3 ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_int24_signed
/-- **Bug**, an instance: the signed MEDIUMINT `-1` (bytes `FF FF FF`) decodes as `16777215`. -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_int24_minus_one (h64 : Target64) (md : Slice U8) (part : Bool)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = [byte 0xFF, byte 0xFF, byte 0xFF] ++ tail) :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (.MYSQL_TYPE_INT24, md, false, part) buf ⦃ r rest =>
      (okPart r).map binlogValView = some (some (.int 16777215)) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_int24_minus_one
/-- **Bug** (pre-5.6.4 TIME). The crate reads the 3 bytes unsigned and takes the hours mod 256 (`as u8`), where MySQL reads them signed (`sint3korr`, `Field_time` of MySQL ≤ 5.7; `oldTimeVal`): negative times and times from 256 hours are misread (they agree elsewhere). (`mysqlbinlog` itself reads `uint3korr`, `log_event.cc:1981`; the crate additionally truncates the hours `as u8`.) -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_time_unsigned (h64 : Target64)
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (ht : binlogEffType ct md.val = .MYSQL_TYPE_TIME) (hl : 3 ≤ buf.length) :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf ⦃ r rest =>
      (okPart r).map binlogValView =
        some (some (.time false 0 (leNat (buf.val.take 3) / 10000 % 256)
          (leNat (buf.val.take 3) % 10000 / 100) (leNat (buf.val.take 3) % 100) 0)) ∧
        rest.val = buf.val.drop 3 ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_time_unsigned
/-- **Bug (crash path)**: a TIME2 column with 1–2 fractional digits and a negative value with a fraction (`time2NegFracBug`) panics (see `my_time_packed_from_binary_neg_frac`). -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_time2_neg_frac
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (ht : binlogEffType ct md.val = .MYSQL_TYPE_TIME2) (d : U8) (t : List U8)
    (hm : md.val = d :: t) (hb : time2NegFracBug d.val buf.val) :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf = fail .integerOverflow

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_time2_neg_frac
/-- **Bug (crash path)**, an instance: the TIME(1) value `-00:00:00.5`, which MySQL writes as `7F FF FF CE` (`Defs.time2Bin_neg_half`), crashes the decoder. -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_time2_neg_half_second (md : Slice U8) (uns part : Bool)
    (hm : md.val.head? = some (byte 1)) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = [byte 0x7F, byte 0xFF, byte 0xFF, byte 0xCE] ++ tail) :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (.MYSQL_TYPE_TIME2, md, uns, part) buf = fail .integerOverflow

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_time2_neg_half_second
/-- YEAR round trip: MySQL stores a year `y` in 1901–2155 as the byte `y - 1900`; the crate reads it back as the text of `y`. -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_year_roundtrip (h64 : Target64)
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (ht : binlogEffType ct md.val = .MYSQL_TYPE_YEAR) (y : Nat) (hy : 1901 ≤ y ∧ y ≤ 2155)
    (tail : List U8) (h : buf.val = byte (y - 1900) :: tail) :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf ⦃ r rest =>
      (okPart r).map binlogValView = some (some (.bytes (decimalBytes y))) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_year_roundtrip
/-- **Bug**: the YEAR byte 0, MySQL's year `0000` (value 0: `Field_year::val_int`; `SELECT` returns `0000`; `binlogRead` gives `"0"`), reads as `"1900"`. Only `mysqlbinlog` prints it as 1900 (`log_event.cc:2033`). -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_year_zero (h64 : Target64)
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (ht : binlogEffType ct md.val = .MYSQL_TYPE_YEAR) (tail : List U8) (h : buf.val = byte 0 :: tail) :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf ⦃ r rest =>
      (okPart r).map binlogValView = some (some (.bytes (decimalBytes 1900))) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_year_zero
/-- TIMESTAMP2 round trip without fraction: MySQL's encoding (`timestamp2Bin`) of a timestamp in range (seconds below `2^31`) with zero microseconds reads back as the text of the seconds. -/
recall binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_timestamp2_roundtrip (h64 : Target64)
    (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (ht : binlogEffType ct md.val = .MYSQL_TYPE_TIMESTAMP2) (d : U8) (t : List U8)
    (hm : md.val = d :: t) (sec : Nat) (hs : sec < 2 ^ 31) (tail : List U8)
    (h : buf.val = timestamp2Bin d.val sec 0 ++ tail) :
    binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize (ct, md, uns, part) buf ⦃ r rest =>
      (okPart r).map binlogValView = some (some (.bytes (decimalBytes sec))) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.readExactEofError, binlog.decimal.read_bin_to_string_bytes, binlog.jsonb.Value, binlog.jsonb.parse_jsonb_value, binlog.jsondiff.JsonDiff, binlog.jsondiff.parse_json_diffs, binlog.trusted.timestamp2_frac_bytes, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize_timestamp2_roundtrip
end mysql_common
