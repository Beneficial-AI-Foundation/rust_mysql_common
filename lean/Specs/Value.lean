import Proofs.Value.Value
import Proofs.Value.ValueDeserializer

/-!
# `src/value/mod.rs`
    The wire format of `Value`: binary-protocol serialization (`MySerialize for Value`, `bin_len`)
    and deserialization (`ValueDeserializer<BinValue>`, via `Value::deserialize_bin`), and
    text-protocol deserialization (`ValueDeserializer<TextValue>`, via `Value::deserialize_text`).

    **Configuration.** As in `Specs/Io.lean`. The decoders' exact characterisations take `Target64`
    (lengths are `u64` cast to `usize`).

    `¬ f x ⦃ _ => True ⦄` means `f x` does not return normally (it panics or does not terminate); every function stated this way here is loop-free, so it means `f x` panics.

    **Allocation caveat.** Decoding a byte string copies it (`.to_vec()`, `into_owned`), and
    `serialize` grows the output `Vec`. Aeneas models allocation as infallible (bounded only by
    `usize::MAX`); real Rust aborts on OOM. So "does not panic" means "does not panic, assuming
    allocation succeeds". The length of a decoded string is bounded by the input buffer.

    **Definitions used.** `Defs/Value.lean` (`Val`, `Val.ofValue`, `binEnc`, `binRead`, `dateRead`,
    `timeRead`, `dateProto`, `timeProto` (the protocol's temporal formats, see `Specs/Defs.lean`
    for how the crate's readers relate to them), `binSupported`, `isLenencStrType`, `isUnsigned`, `binCompatible`, `binNorm`,
    `textRead`), `Defs/LenEnc.lean`, `Defs/Bytes.lean`. Floats are compared by bit pattern only.

    **Not covered.** `Value::as_sql`, `Debug`, the conversions in `value/convert/*` and `value/json.rs`
    (later stages), `SerializationSide`. The private helpers `deserialize_tiny`/`short`/`long`/
    `longlong`/`datetime`/`time` are covered through `deserialize_bin`.

    **Behaviour to note.**
    * `deserialize_bin` panics (`unimplemented!`) on the column types `TIMESTAMP2`, `DATETIME2`,
      `TIME2`, `TYPED_ARRAY`, `UNKNOWN`: a column definition from the server can crash the client.
    * Binary decoding normalises (`binNorm`): an 8-byte integer is reinterpreted by the column's
      signedness. At an unsigned column, a value `≤ i64::MAX` comes back as `Int` (also an `Int x`
      with `x < 0` comes back as `UInt (x + 2^64)`); at a signed column, a `UInt x` with
      `x > i64::MAX` comes back as the negative `Int (x - 2^64)`. A negative zero `Time` comes back
      positive.
    * The decoders accept input the protocol does not define: lenenc lengths starting `0xFB`/`0xFF`
      give an empty string (in a text row, `0xFF` -- an ERR packet header -- becomes an empty value);
      DATE/TIME lengths other than 0/4/7/11 and 0/8/12 are read leniently (`dateRead`, `timeRead`);
      a TIME sign byte other than 1 means positive.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `enum Value and its impls` -/

/-- `MySerialize for Value`: appends the binary-protocol encoding `binEnc` (NULL appends
    nothing: NULLs go in the row's null bitmap). -/
recall value.Value.Insts.Mysql_commonProtoMySerialize.serialize_spec (v : value.Value) (buf : alloc.vec.Vec U8)
    (h : buf.length + (binEnc (Val.ofValue v)).length ≤ Usize.max) :
    value.Value.Insts.Mysql_commonProtoMySerialize.serialize v buf ⦃ buf' => buf'.val = buf.val ++ binEnc (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- `bin_len`: the length of the binary encoding, exactly what `serialize` appends. Precondition:
    the `u64` length computation does not overflow (true of every real `Vec`). -/
recall value.Value.bin_len_spec (v : value.Value)
    (h : (binEnc (Val.ofValue v)).length < 2 ^ 64) :
    value.Value.bin_len v ⦃ n => n.val = (binEnc (Val.ofValue v)).length ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.bin_len_spec`

/-- `deserialize_text`: total; `textRead` (`0xFB` is NULL, anything else a length-encoded
    string; an error on an empty buffer, with the buffer unchanged). -/
recall value.Value.deserialize_text_spec (h64 : Target64) (buf : io.ParseBuf) :
    value.Value.deserialize_text buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = textRead buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.deserialize_text_spec`

/-- `deserialize_text` reads a length-encoded string back as `Bytes` (its first byte is never `0xFB`). -/
recall value.Value.deserialize_text_roundtrip (s tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = lenencStr s ++ tail) :
    value.Value.deserialize_text buf ⦃ r rest =>
      (okPart r).map Val.ofValue = some (.bytes s) ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.deserialize_text_roundtrip`

/-- `deserialize_text` reads `0xFB` as `NULL`, consuming just that byte. -/
recall value.Value.deserialize_text_null (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = byte 0xFB :: tail) :
    value.Value.deserialize_text buf ⦃ r rest =>
      (okPart r).map Val.ofValue = some .null ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.deserialize_text_null`

/-- `deserialize_bin`: for a supported column type, total; `binRead` for that type and the
    column's `UNSIGNED_FLAG` (see `Defs/Value.lean` for the formats and for how input the protocol
    does not define is read). -/
recall value.Value.deserialize_bin_spec (h64 : Target64) (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hct : binSupported ct = true) (buf : io.ParseBuf) :
    value.Value.deserialize_bin (ct, flags) buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = binRead ct (isUnsigned flags) buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.deserialize_bin_spec`

/-- **Crash path.** `deserialize_bin` panics (`unimplemented!("Unsupported column type")`) on
    the five unsupported column types, whatever the buffer. (The panic message's `fmt::Arguments`
    are built by Aeneas library functions that are defined and never fail, so this is an
    equation.) -/
recall value.Value.deserialize_bin_unsupported (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hct : binSupported ct = false) (buf : io.ParseBuf) :
    value.Value.deserialize_bin (ct, flags) buf = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.deserialize_bin_unsupported`

/-- Round trip: `deserialize_bin` at a compatible column type (`binCompatible`) reads back what
    `serialize` writes, up to `binNorm` (integers reinterpreted by the column's signedness; a
    negative zero `Time` comes back positive). Everything else, including floats (bit for bit),
    dates and byte strings, comes back unchanged. -/
recall value.Value.deserialize_bin_roundtrip (v : value.Value) (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hc : binCompatible (Val.ofValue v) ct)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = binEnc (Val.ofValue v) ++ tail) :
    value.Value.deserialize_bin (ct, flags) buf ⦃ r rest =>
      (okPart r).map Val.ofValue = some (binNorm (isUnsigned flags) (Val.ofValue v)) ∧
      rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.deserialize_bin_roundtrip`

/-! ### `struct ValueDeserializer and its impls` -/

/-- `MyDeserialize for ValueDeserializer<TextValue>`: `SIZE` is `None`. -/
recall value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for ValueDeserializer<TextValue>`: total; `deserialize_text`, wrapped. -/
recall value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64) (buf : io.ParseBuf) :
    value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun d => Val.ofValue d.1), rest.val) = textRead buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MyDeserialize for ValueDeserializer<BinValue>`: `SIZE` is `None`. -/
recall value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.SIZE_eq :
    value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.SIZE_eq`

/-- `MyDeserialize for ValueDeserializer<BinValue>`: for a supported column type, total; `deserialize_bin`, wrapped. -/
recall value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_spec (h64 : Target64) (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hct : binSupported ct = true) (buf : io.ParseBuf) :
    value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf ⦃ r rest =>
      ((okPart r).map (fun d => Val.ofValue d.1), rest.val) = binRead ct (isUnsigned flags) buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_spec`

/-- **Crash path.** `MyDeserialize for ValueDeserializer<BinValue>` panics on the unsupported column types. -/
recall value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_unsupported (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hct : binSupported ct = false) (buf : io.ParseBuf) :
    value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_unsupported`

/-- `MyDeserialize for ValueDeserializer<TextValue>` reads a length-encoded string back as `Bytes`, and `0xFB` as `NULL`. -/
recall value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (v : Val) (tail : List U8) (buf : io.ParseBuf)
    (hv : (∃ s, v = .bytes s ∧ buf.val = lenencStr s ++ tail) ∨ (v = .null ∧ buf.val = byte 0xFB :: tail)) :
    value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun d => Val.ofValue d.1) = some v ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-- `MyDeserialize for ValueDeserializer<BinValue>`: the round trip of `deserialize_bin`. -/
recall value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.roundtrip (v : value.Value) (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hc : binCompatible (Val.ofValue v) ct)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = binEnc (Val.ofValue v) ++ tail) :
    value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf ⦃ r rest =>
      (okPart r).map (fun d => Val.ofValue d.1) = some (binNorm (isUnsigned flags) (Val.ofValue v)) ∧
      rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.roundtrip`
end mysql_common
