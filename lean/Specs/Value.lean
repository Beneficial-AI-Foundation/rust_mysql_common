import Proofs.Value.Value
import Proofs.Value.ValueDeserializer

/-!
# `src/value/mod.rs`
    The wire format of `Value`: binary-protocol serialization (`MySerialize for Value`, `bin_len`)
    and deserialization (`ValueDeserializer<BinValue>`, via `Value::deserialize_bin`), and
    text-protocol deserialization (`ValueDeserializer<TextValue>`, via `Value::deserialize_text`).

    **Configuration.** As in `Specs/Io.lean`. The decoders' exact characterisations take `Target64`
    (lengths are `u64` cast to `usize`).

    **Definitions used.** `Defs/Value.lean` (`Val`, `Val.ofValue`, `binEnc`, `binRead`, `dateRead`,
    `timeRead`, `binSupported`, `isLenencStrType`, `isUnsigned`, `binCompatible`, `binNorm`,
    `textRead`), `Defs/LenEnc.lean`, `Defs/Bytes.lean`. Floats are compared by bit pattern only.

    **Not covered.** `Value::as_sql`, `Debug`, the conversions in `value/convert/*` and `value/json.rs`
    (later stages), `SerializationSide`. The private helpers `deserialize_tiny`/`short`/`long`/
    `longlong`/`datetime`/`time` are covered through `deserialize_bin`.

    **Behaviour to note.**
    * `deserialize_bin` panics (`unimplemented!`) on the column types `TIMESTAMP2`, `DATETIME2`,
      `TIME2`, `TYPED_ARRAY`, `UNKNOWN`: a column definition from the server can crash the client.
    * Binary decoding normalises: an 8-byte integer is reinterpreted by the column's signedness, an
      unsigned value `≤ i64::MAX` comes back as `Int`; a negative zero `Time` comes back positive
      (`binNorm`).
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
    (h : ∀ b : alloc.vec.Vec U8, v = value.Value.Bytes b → b.length + 9 < 2 ^ 64) :
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

/-- `deserialize_bin`: for a supported column type, total; `binRead` for that type and the
    column's `UNSIGNED_FLAG` (see `Defs/Value.lean` for the formats and for how input the protocol
    does not define is read). -/
recall value.Value.deserialize_bin_spec (h64 : Target64) (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hct : binSupported ct = true) (buf : io.ParseBuf) :
    value.Value.deserialize_bin (ct, flags) buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = binRead ct (isUnsigned flags) buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.deserialize_bin_spec`

/-- **Crash path.** `deserialize_bin` panics (`unimplemented!("Unsupported column type")`) on
    the five unsupported column types, whatever the buffer. -/
recall value.Value.deserialize_bin_unsupported (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hct : binSupported ct = false) (buf : io.ParseBuf) :
    ¬ value.Value.deserialize_bin (ct, flags) buf ⦃ _ => True ⦄

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
    ¬ value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf ⦃ _ => True ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_unsupported`
end mysql_common
