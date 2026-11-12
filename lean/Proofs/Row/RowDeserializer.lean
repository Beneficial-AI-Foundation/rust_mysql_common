import Defs

/-! Statements for `struct RowDeserializer and its impls` (spec file: `Specs/Row.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `into_inner`: the row. -/
theorem row.RowDeserializer.into_inner_eq {S P : Type} (self : row.RowDeserializer S P) :
    row.RowDeserializer.into_inner self = ok self.1 := by
  sorry

/-- `MyDeserialize for RowDeserializer<T, Text>`: `SIZE` is `None`. -/
theorem row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE_eq (T : Type) :
    row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE T = none := by
  sorry

/-- `MyDeserialize for RowDeserializer<T, Text>`: total; one text value per column (`textRowRead`), all present (`Some`), with the given columns. -/
theorem row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_spec (h64 : Target64) (T : Type) (columns : alloc.sync.Arc (Slice packets.Column))
    (buf : io.ParseBuf) :
    row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize T columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) = (textRowRead columns.length buf.val).1.map (List.map some) ∧
      rest.val = (textRowRead columns.length buf.val).2 ∧
      ∀ d, okPart r = some d → d.1.columns = columns ⦄ := by
  sorry

/-- Round trip: a text row of `NULL`s and byte strings (one per column) is read back. -/
theorem row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip (h64 : Target64) (T : Type) (columns : alloc.sync.Arc (Slice packets.Column)) (vs : List Val)
    (hv : ∀ v ∈ vs, isTextVal v = true) (hn : vs.length = columns.length) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = (vs.map textEnc).flatten ++ tail) :
    row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize T columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) = some (vs.map some) ∧ rest.val = tail ⦄ := by
  sorry

/-- `MyDeserialize for RowDeserializer<S, Binary>`: `SIZE` is `None`. -/
theorem row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE_eq {S : Type} (inst : value.SerializationSide S) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE inst = none := by
  sorry

/-- `MyDeserialize for RowDeserializer<S, Binary>`: when every column type is supported by the binary value decoder, total; `binRowRead` with `S`'s bit offset (header byte, NULL bitmap, then the non-NULL values), all present (`Some`), with the given columns. (The bound on the number of columns keeps `bitmap_len` from overflowing.) -/
theorem row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_spec (h64 : Target64) {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (hsup : ∀ c ∈ columns.val, binSupported c.column_type.1 = true)
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (buf : io.ParseBuf) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) =
        (binRowRead off.val (columns.val.map colInfo) buf.val).1.map (List.map some) ∧
      rest.val = (binRowRead off.val (columns.val.map colInfo) buf.val).2 ∧
      ∀ d, okPart r = some d → d.1.columns = columns ⦄ := by
  sorry

/-- **Crash path.** `MyDeserialize for RowDeserializer<S, Binary>` panics when it reaches a non-NULL value of a column of unsupported type; e.g. when the first column has such a type and is not marked NULL. -/
theorem row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_unsupported {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (c : packets.Column) (cs : List packets.Column) (hc : columns.val = c :: cs)
    (hsup : binSupported c.column_type.1 = false)
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (buf : io.ParseBuf)
    (hbuf : 1 + nullBitmapLen off.val columns.length ≤ buf.length)
    (hnn : bitmapBit off.val ((buf.val.drop 1).take (nullBitmapLen off.val columns.length)) 0 = false) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf = fail .panic := by
  sorry

/-- Round trip: a binary row (`binRowEnc`: header, NULL bitmap, values) of `Value`s that are `NULL` or fit their column's type (`binCompatible`) is read back, up to the value decoder's normalisation `binNorm` (integers reinterpreted by the column's `UNSIGNED_FLAG`, negative zero times made positive). -/
theorem row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip (h64 : Target64) {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (vs : List value.Value) (hn : vs.length = columns.length)
    (hc : ∀ p ∈ vs.zip columns.val, Val.ofValue p.1 = .null ∨ binCompatible (Val.ofValue p.1) p.2.column_type.1)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = binRowEnc off.val (vs.map Val.ofValue) ++ tail) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) =
        some ((vs.zip columns.val).map (fun p => some (binNorm (isUnsigned p.2.flags.1) (Val.ofValue p.1)))) ∧
      rest.val = tail ⦄ := by
  sorry

end mysql_common
