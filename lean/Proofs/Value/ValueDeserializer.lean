import Defs

/-! Statements for `struct ValueDeserializer and its impls` (spec file: `Specs/Value.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MyDeserialize for ValueDeserializer<TextValue>`: `SIZE` is `None`. -/
theorem value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for ValueDeserializer<TextValue>`: total; `deserialize_text`, wrapped. -/
theorem value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64) (buf : io.ParseBuf) :
    value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun d => Val.ofValue d.1), rest.val) = textRead buf.val ⦄ := by
  sorry

/-- `MyDeserialize for ValueDeserializer<BinValue>`: `SIZE` is `None`. -/
theorem value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.SIZE_eq :
    value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.SIZE = none := by
  sorry

/-- `MyDeserialize for ValueDeserializer<BinValue>`: for a supported column type, total; `deserialize_bin`, wrapped. -/
theorem value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_spec (h64 : Target64) (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hct : binSupported ct = true) (buf : io.ParseBuf) :
    value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf ⦃ r rest =>
      ((okPart r).map (fun d => Val.ofValue d.1), rest.val) = binRead ct (isUnsigned flags) buf.val ⦄ := by
  sorry

/-- **Crash path.** `MyDeserialize for ValueDeserializer<BinValue>` panics on the unsupported column types. -/
theorem value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_unsupported (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hct : binSupported ct = false) (buf : io.ParseBuf) :
    value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf = fail .panic := by
  sorry

/-- `MyDeserialize for ValueDeserializer<TextValue>` reads a length-encoded string back as `Bytes`, and `0xFB` as `NULL`. -/
theorem value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (v : Val) (tail : List U8) (buf : io.ParseBuf)
    (hv : (∃ s, v = .bytes s ∧ buf.val = lenencStr s ++ tail) ∨ (v = .null ∧ buf.val = byte 0xFB :: tail)) :
    value.ValueDeserializerTextValue.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun d => Val.ofValue d.1) = some v ∧ rest.val = tail ⦄ := by
  sorry

/-- `MyDeserialize for ValueDeserializer<BinValue>`: the round trip of `deserialize_bin`. -/
theorem value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.roundtrip (v : value.Value) (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hc : binCompatible (Val.ofValue v) ct)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = binEnc (Val.ofValue v) ++ tail) :
    value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf ⦃ r rest =>
      (okPart r).map (fun d => Val.ofValue d.1) = some (binNorm (isUnsigned flags) (Val.ofValue v)) ∧
      rest.val = tail ⦄ := by
  sorry

end mysql_common
