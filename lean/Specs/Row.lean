import Proofs.Row.Row
import Proofs.Row.RowDeserializer

/-!
# `src/row/mod.rs`
    Rows (`Row`) and their deserialization from text-protocol and binary-protocol result-set
    rows (`RowDeserializer<T, Text>`, `RowDeserializer<S, Binary>`).

    **Patch.** The two deserializers' loops are helpers (`deserialize_text_values`, and the
    recursion `deserialize_bin_values`), translation patch 30; `NullBitmap`'s byte access goes
    through `AsRef` (patches 22, 32). The statements are about the public `deserialize`.

    **Configuration.** As in `Specs/Io.lean`. The decoders take `Target64` (lengths are `u64`
    cast to `usize`). `RowDeserializer<S, Binary>` is stated for any `SerializationSide` `S`, given
    its `BIT_OFFSET`, and instantiated at `ServerSide` (offset 2), which clients use for result
    sets (`*_server`).

    **Panics.** The binary row reader is characterised on every input: it panics exactly when
    `binRowCrash` holds (`deserialize_crash`), and otherwise returns what `binRowRead` says
    (`deserialize_spec`). Facts about `binRowCrash`: `Specs/DefsCF.lean`.

    **Allocation caveat.** Decoding copies strings and grows the value vector; Aeneas models
    allocation as infallible, so "does not panic" means "does not panic, assuming allocation
    succeeds".

    **Definitions used.** `Defs/Row.lean` (`rowVals`, `colInfo`, `textRowRead`, `textEnc`,
    `isTextVal`, `binRowRead`, `binValuesRead`, `binRowCrash`, `binValuesCrash`, `binRowEnc`,
    `isNullVal`, `intWidth`, `binEncAt`,
    `binFitsAt`, `binNormAt`, `binRowEncAt`), `Defs/NullBitmap.lean`
    (`nullBitmapLen`, `bitmapBit`), `Defs/Value.lean` (`Val`, `textRead`, `binRead`, `binSupported`,
    `binCompatible`, `binNorm`, `isUnsigned`), `Defs/Bytes.lean`.

    **Not covered.** `new_row` (collects through an iterator `map`), `Row::as_ref`, `get`,
    `get_opt`, `take`, `take_opt`, `unwrap`, `place`, `Index` impls, `ColumnIndex`, `Debug`,
    `row/convert` (not translated, or later stages).

    **Behaviour to note.**
    * The binary row's header byte is not checked (the protocol says `0x00`).
    * `RowDeserializer<S, Binary>` panics (through `Value::deserialize_bin`) on a non-NULL value of
      a column whose type is `TIMESTAMP2`, `DATETIME2`, `TIME2`, `TYPED_ARRAY` or `UNKNOWN`: a column
      definition from the server can crash the client.
    * Neither deserializer checks that the row ends after the last value (trailing bytes stay in
      the buffer).
    * Text rows inherit the value decoder's quirk: a value starting with `0xFF` decodes as the
      empty string.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct Row and its impls` -/

/-- `new_row_raw`: the row of the given cells and columns, when there are as many of each. -/
recall row.new_row_raw_spec (values : alloc.vec.Vec (Option value.Value)) (columns : alloc.sync.Arc (Slice packets.Column))
    (h : values.length = columns.length) :
    row.new_row_raw values columns ⦃ r => r.values = values ∧ r.columns = columns ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.new_row_raw_spec
/-- `new_row_raw` panics (`assert!`) when the numbers of cells and columns differ. -/
recall row.new_row_raw_panics (values : alloc.vec.Vec (Option value.Value)) (columns : alloc.sync.Arc (Slice packets.Column))
    (h : values.length ≠ columns.length) :
    row.new_row_raw values columns = fail .assertionFailure

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.new_row_raw_panics
/-- `len`: the number of cells. -/
recall row.Row.len_spec (self : row.Row) :
    row.Row.len self ⦃ n => n.val = self.values.length ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.Row.len_spec
/-- `is_empty`: no cells. -/
recall row.Row.is_empty_spec (self : row.Row) :
    row.Row.is_empty self ⦃ b => (b ↔ self.values.val = []) ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.Row.is_empty_spec
/-- `columns_ref`: the columns. -/
recall row.Row.columns_ref_eq (self : row.Row) :
    row.Row.columns_ref self = ok self.columns

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.Row.columns_ref_eq
/-- `columns`: (another `Arc` to) the columns. -/
recall row.Row.impl.columns_eq (self : row.Row) :
    row.Row.impl.columns self = ok self.columns

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.Row.impl.columns_eq
/-- `unwrap_raw`: the cells. -/
recall row.Row.unwrap_raw_eq (self : row.Row) :
    row.Row.unwrap_raw self = ok self.values

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.Row.unwrap_raw_eq
/-! ### `struct RowDeserializer and its impls` -/

/-- `into_inner`: the row. -/
recall row.RowDeserializer.into_inner_eq {S P : Type} (self : row.RowDeserializer S P) :
    row.RowDeserializer.into_inner self = ok self.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.RowDeserializer.into_inner_eq
/-- `MyDeserialize for RowDeserializer<T, Text>`: `SIZE` is `None`. -/
recall row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE_eq (T : Type) :
    row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE T = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE_eq
/-- `MyDeserialize for RowDeserializer<T, Text>`: total; one text value per column (`textRowRead`), all present (`Some`), with the given columns. -/
recall row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_spec (h64 : Target64) (T : Type) (columns : alloc.sync.Arc (Slice packets.Column))
    (buf : io.ParseBuf) :
    row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize T columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) = (textRowRead columns.length buf.val).1.map (List.map some) ∧
      rest.val = (textRowRead columns.length buf.val).2 ∧
      ∀ d, okPart r = some d → d.1.columns = columns ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_spec
/-- Round trip: a text row of `NULL`s and byte strings (one per column) is read back. -/
recall row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip (h64 : Target64) (T : Type) (columns : alloc.sync.Arc (Slice packets.Column)) (vs : List Val)
    (hv : ∀ v ∈ vs, isTextVal v = true) (hn : vs.length = columns.length) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = (vs.map textEnc).flatten ++ tail) :
    row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize T columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) = some (vs.map some) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.RowDeserializerTText.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip
/-- `MyDeserialize for RowDeserializer<S, Binary>`: `SIZE` is `None`. -/
recall row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE_eq {S : Type} (inst : value.SerializationSide S) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE inst = none

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.SIZE_eq
/-- `MyDeserialize for RowDeserializer<S, Binary>`: whenever it does not panic (`binRowCrash` is `false`; see `deserialize_crash` for the other case), total; `binRowRead` with `S`'s bit offset (header byte, NULL bitmap, then the non-NULL values), all present (`Some`), with the given columns. It is enough that every column of unsupported type is marked NULL in the row's bitmap (`Defs.binRowCrash_eq_false_of_supported`), but a truncated row, or one where an earlier value fails to decode, is covered too: it is an error, not a panic. (The bound on the number of columns keeps `bitmap_len` from overflowing.) -/
recall row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_spec (h64 : Target64) {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (buf : io.ParseBuf)
    (hnc : binRowCrash off.val (columns.val.map colInfo) buf.val = false) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) =
        (binRowRead off.val (columns.val.map colInfo) buf.val).1.map (List.map some) ∧
      rest.val = (binRowRead off.val (columns.val.map colInfo) buf.val).2 ∧
      ∀ d, okPart r = some d → d.1.columns = columns ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_spec
/-- **Crash path, exactly.** `MyDeserialize for RowDeserializer<S, Binary>` panics (`unimplemented!`) whenever `binRowCrash` is `true`: the header and bitmap are there, and the reader reaches a column of unsupported type that is not marked NULL, every earlier non-NULL value having decoded. With `deserialize_spec` this covers every input: the reader panics iff `binRowCrash`. -/
recall row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_crash (h64 : Target64) {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (buf : io.ParseBuf)
    (hc : binRowCrash off.val (columns.val.map colInfo) buf.val = true) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf = fail .panic

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_crash
/-- **Crash path, simplest case** (no `Target64` needed; `deserialize_crash` is the general statement): `MyDeserialize for RowDeserializer<S, Binary>` panics when the first column has an unsupported type and is not marked NULL. -/
recall row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_unsupported {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (c : packets.Column) (cs : List packets.Column) (hc : columns.val = c :: cs)
    (hsup : binSupported c.column_type.1 = false)
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (buf : io.ParseBuf)
    (hbuf : 1 + nullBitmapLen off.val columns.length ≤ buf.length)
    (hnn : bitmapBit off.val ((buf.val.drop 1).take (nullBitmapLen off.val columns.length)) 0 = false) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf = fail .panic

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_unsupported
/-- Round trip (parameter encoding: every integer in 8 bytes, so integers only at `LONGLONG`; see `roundtrip_at` for the server's format): a binary row (`binRowEnc`: header, NULL bitmap, values) of `Value`s that are `NULL` or fit their column's type (`binCompatible`) is read back, up to the value decoder's normalisation `binNorm` (integers reinterpreted by the column's `UNSIGNED_FLAG`, negative zero times made positive). -/
recall row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip (h64 : Target64) {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (vs : List value.Value) (hn : vs.length = columns.length)
    (hc : ∀ p ∈ vs.zip columns.val, Val.ofValue p.1 = .null ∨ binCompatible (Val.ofValue p.1) p.2.column_type.1)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = binRowEnc off.val (vs.map Val.ofValue) ++ tail) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) =
        some ((vs.zip columns.val).map (fun p => some (binNorm (isUnsigned p.2.flags.1) (Val.ofValue p.1)))) ∧
      rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip
/-- `ServerSide::BIT_OFFSET` is 2 (from `src/value/mod.rs`; the offset of binary result-set rows). -/
recall value.ServerSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET_val :
    value.ServerSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET.val = 2

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.ServerSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET_val
/-- `MyDeserialize for RowDeserializer<ServerSide, Binary>` (how clients read binary result-set rows): `deserialize_spec` at bit offset 2. -/
recall row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_spec_server (h64 : Target64) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 9 ≤ Usize.max) (buf : io.ParseBuf)
    (hnc : binRowCrash 2 (columns.val.map colInfo) buf.val = false) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize value.ServerSide.Insts.Mysql_commonValueSerializationSide columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) =
        (binRowRead 2 (columns.val.map colInfo) buf.val).1.map (List.map some) ∧
      rest.val = (binRowRead 2 (columns.val.map colInfo) buf.val).2 ∧
      ∀ d, okPart r = some d → d.1.columns = columns ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_spec_server
/-- `deserialize_crash` at `ServerSide` (bit offset 2): a binary result-set row from the server crashes the client exactly when `binRowCrash 2`. -/
recall row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_crash_server (h64 : Target64) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 9 ≤ Usize.max) (buf : io.ParseBuf)
    (hc : binRowCrash 2 (columns.val.map colInfo) buf.val = true) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize value.ServerSide.Insts.Mysql_commonValueSerializationSide columns buf = fail .panic

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize_crash_server
/-- Round trip at the columns' types: a binary row as the server sends it (`binRowEncAt`: each non-NULL value in its column's format, integers in the column's width) of `Value`s that are `NULL` or fit their column (`binFitsAt`: in range for a narrow integer type, else `binCompatible`) is read back, up to `binNormAt`. -/
recall row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip_at (h64 : Target64) {S : Type} (inst : value.SerializationSide S) (off : Usize)
    (hoff : inst.BIT_OFFSET = ok off) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 7 + off.val ≤ Usize.max) (vs : List value.Value) (hn : vs.length = columns.length)
    (hc : ∀ p ∈ vs.zip columns.val, Val.ofValue p.1 = .null ∨
      binFitsAt p.2.column_type.1 (isUnsigned p.2.flags.1) (Val.ofValue p.1))
    (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = binRowEncAt off.val (columns.val.map (·.column_type.1)) (vs.map Val.ofValue) ++ tail) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize inst columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) =
        some ((vs.zip columns.val).map (fun p =>
          some (binNormAt p.2.column_type.1 (isUnsigned p.2.flags.1) (Val.ofValue p.1)))) ∧
      rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip_at
/-- `roundtrip_at` at `ServerSide` (bit offset 2). -/
recall row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip_at_server (h64 : Target64) (columns : alloc.sync.Arc (Slice packets.Column))
    (hlen : columns.length + 9 ≤ Usize.max) (vs : List value.Value) (hn : vs.length = columns.length)
    (hc : ∀ p ∈ vs.zip columns.val, Val.ofValue p.1 = .null ∨
      binFitsAt p.2.column_type.1 (isUnsigned p.2.flags.1) (Val.ofValue p.1))
    (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = binRowEncAt 2 (columns.val.map (·.column_type.1)) (vs.map Val.ofValue) ++ tail) :
    row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.deserialize value.ServerSide.Insts.Mysql_commonValueSerializationSide columns buf ⦃ r rest =>
      (okPart r).map (fun d => rowVals d.1) =
        some ((vs.zip columns.val).map (fun p =>
          some (binNormAt p.2.column_type.1 (isUnsigned p.2.flags.1) (Val.ofValue p.1)))) ∧
      rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms row.RowDeserializerSBinary.Insts.Mysql_commonProtoMyDeserializeDeArcSliceColumn.roundtrip_at_server
end mysql_common
