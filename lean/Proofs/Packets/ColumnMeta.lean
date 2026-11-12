import Defs

/-! Statements for `struct ColumnMeta and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `into_owned`: the same fields. -/
theorem packets.ColumnMeta.into_owned_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.into_owned self ⦃ m => metaFields m = metaFields self ⦄ := by
  sorry

/-- `catalog_ref`: **returns the `schema` field, not `catalog`** (`self.schema.as_bytes()`; a bug in the crate). -/
theorem packets.ColumnMeta.catalog_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.catalog_ref self ⦃ s => s.val = cowList self.schema.1 ⦄ := by
  sorry

/-- `schema_ref`: the `schema` field. -/
theorem packets.ColumnMeta.schema_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.schema_ref self ⦃ s => s.val = cowList self.schema.1 ⦄ := by
  sorry

/-- `table_ref`: the `table` field. -/
theorem packets.ColumnMeta.table_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.table_ref self ⦃ s => s.val = cowList self.table.1 ⦄ := by
  sorry

/-- `org_table_ref`: the `org_table` field. -/
theorem packets.ColumnMeta.org_table_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.org_table_ref self ⦃ s => s.val = cowList self.org_table.1 ⦄ := by
  sorry

/-- `name_ref`: the `name` field. -/
theorem packets.ColumnMeta.name_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.name_ref self ⦃ s => s.val = cowList self.«name».1 ⦄ := by
  sorry

/-- `org_name_ref`: the `org_name` field. -/
theorem packets.ColumnMeta.org_name_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.org_name_ref self ⦃ s => s.val = cowList self.org_name.1 ⦄ := by
  sorry

/-- `MyDeserialize for ColumnMeta`: `SIZE` is `None`. -/
theorem packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for ColumnMeta`: total; the six length-encoded strings (`lenencStrs 6`). -/
theorem packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64) (buf : io.ParseBuf) :
    packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map metaFields, rest.val) = lenencStrs 6 buf.val ⦄ := by
  sorry

/-- `MySerialize for ColumnMeta`: appends the six fields as length-encoded strings. -/
theorem packets.ColumnMeta.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ColumnMeta) (buf : alloc.vec.Vec U8)
    (h : buf.length + ((metaFields self).map lenencStr).flatten.length ≤ Usize.max) :
    packets.ColumnMeta.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ ((metaFields self).map lenencStr).flatten ⦄ := by
  sorry

end mysql_common
