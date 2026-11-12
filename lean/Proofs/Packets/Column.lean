import Defs

/-! Statements for `struct Column and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MyDeserialize for Column`: `SIZE` is `None`. -/
theorem packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for Column`: total; `colDefRead` (six strings, then 13 bytes: `0x0c`, character set, column length, type, flags, decimals, filler). -/
theorem packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64) (buf : io.ParseBuf) :
    packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map ColDef.ofColumn, rest.val) = colDefRead buf.val ⦄ := by
  sorry

/-- Round trip: a column definition in the protocol layout (`colDefEnc`) is read back. -/
theorem packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h64 : Target64) (c : packets.Column) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = colDefEnc (ColDef.ofColumn c) ++ tail) :
    packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map ColDef.ofColumn = some (ColDef.ofColumn c) ∧ rest.val = tail ⦄ := by
  sorry

/-- `MySerialize for Column`: appends `colDefEncCrate`, **which has `column_length` and `character_set` in the wrong order** (not `colDefEnc`, the protocol layout the reader expects). -/
theorem packets.Column.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.Column) (buf : alloc.vec.Vec U8)
    (h : buf.length + (colDefEncCrate (ColDef.ofColumn self)).length ≤ Usize.max) :
    packets.Column.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ colDefEncCrate (ColDef.ofColumn self) ⦄ := by
  sorry

/-- `column_length`: the field. -/
theorem packets.Column.impl.column_length_eq (self : packets.Column) :
    packets.Column.impl.column_length self = ok self.column_length.1 := by
  sorry

/-- `column_type`: the field. -/
theorem packets.Column.impl.column_type_eq (self : packets.Column) :
    packets.Column.impl.column_type self = ok self.column_type.1 := by
  sorry

/-- `character_set`: the field. -/
theorem packets.Column.impl.character_set_eq (self : packets.Column) :
    packets.Column.impl.character_set self = ok self.character_set.1 := by
  sorry

/-- `flags`: the field. -/
theorem packets.Column.impl.flags_eq (self : packets.Column) :
    packets.Column.impl.flags self = ok self.flags.1 := by
  sorry

/-- `decimals`: the field. -/
theorem packets.Column.impl.decimals_eq (self : packets.Column) :
    packets.Column.impl.decimals self = ok self.decimals.1 := by
  sorry

/-- `catalog_ref`: **returns the `schema` field, not `catalog`** (`self.schema.as_bytes()`; a bug in the crate). -/
theorem packets.Column.catalog_ref_spec (self : packets.Column) :
    packets.Column.catalog_ref self ⦃ s => s.val = cowList self.«meta».schema.1 ⦄ := by
  sorry

/-- `schema_ref`: the `schema` field. -/
theorem packets.Column.schema_ref_spec (self : packets.Column) :
    packets.Column.schema_ref self ⦃ s => s.val = cowList self.«meta».schema.1 ⦄ := by
  sorry

/-- `table_ref`: the `table` field. -/
theorem packets.Column.table_ref_spec (self : packets.Column) :
    packets.Column.table_ref self ⦃ s => s.val = cowList self.«meta».table.1 ⦄ := by
  sorry

/-- `org_table_ref`: the `org_table` field. -/
theorem packets.Column.org_table_ref_spec (self : packets.Column) :
    packets.Column.org_table_ref self ⦃ s => s.val = cowList self.«meta».org_table.1 ⦄ := by
  sorry

/-- `name_ref`: the `name` field. -/
theorem packets.Column.name_ref_spec (self : packets.Column) :
    packets.Column.name_ref self ⦃ s => s.val = cowList self.«meta».«name».1 ⦄ := by
  sorry

/-- `org_name_ref`: the `org_name` field. -/
theorem packets.Column.org_name_ref_spec (self : packets.Column) :
    packets.Column.org_name_ref self ⦃ s => s.val = cowList self.«meta».org_name.1 ⦄ := by
  sorry

end mysql_common
