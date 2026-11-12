import Defs
import Proofs.Util.PacketsColStmt
import Proofs.Io.ParseBuf

/-! Statements for `struct ColumnMeta and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PCSUtil

namespace mysql_common

/-- `into_owned`: the same fields. -/
theorem packets.ColumnMeta.into_owned_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.into_owned self ⦃ m => metaFields m = metaFields self ⦄ := by
  unfold packets.ColumnMeta.into_owned
  step with raw_into_owned as ⟨rb, h0⟩
  step with raw_into_owned as ⟨rb1, h1⟩
  step with raw_into_owned as ⟨rb2, h2⟩
  step with raw_into_owned as ⟨rb3, h3⟩
  step with raw_into_owned as ⟨rb4, h4⟩
  step with raw_into_owned as ⟨rb5, h5⟩
  simp only [metaFields, h0, h1, h2, h3, h4, h5]

/-- `catalog_ref`: **returns the `schema` field, not `catalog`** (`self.schema.as_bytes()`; a bug in the crate). -/
theorem packets.ColumnMeta.catalog_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.catalog_ref self ⦃ s => s.val = cowList self.schema.1 ⦄ := by
  exact lenenc_as_bytes _

/-- `schema_ref`: the `schema` field. -/
theorem packets.ColumnMeta.schema_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.schema_ref self ⦃ s => s.val = cowList self.schema.1 ⦄ := by
  exact lenenc_as_bytes _

/-- `table_ref`: the `table` field. -/
theorem packets.ColumnMeta.table_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.table_ref self ⦃ s => s.val = cowList self.table.1 ⦄ := by
  exact lenenc_as_bytes _

/-- `org_table_ref`: the `org_table` field. -/
theorem packets.ColumnMeta.org_table_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.org_table_ref self ⦃ s => s.val = cowList self.org_table.1 ⦄ := by
  exact lenenc_as_bytes _

/-- `name_ref`: the `name` field. -/
theorem packets.ColumnMeta.name_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.name_ref self ⦃ s => s.val = cowList self.«name».1 ⦄ := by
  exact lenenc_as_bytes _

/-- `org_name_ref`: the `org_name` field. -/
theorem packets.ColumnMeta.org_name_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.org_name_ref self ⦃ s => s.val = cowList self.org_name.1 ⦄ := by
  exact lenenc_as_bytes _

/-- `MyDeserialize for ColumnMeta`: `SIZE` is `None`. -/
theorem packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  unfold packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for ColumnMeta`: total; the six length-encoded strings (`lenencStrs 6`). -/
theorem packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64) (buf : io.ParseBuf) :
    packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map metaFields, rest.val) = lenencStrs 6 buf.val ⦄ := by
  unfold packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  simp only [io.ParseBuf.parse_unchecked_eq]
  step*
  all_goals simp_all [okPart, lenencStrs, metaFields]

/-- `MySerialize for ColumnMeta`: appends the six fields as length-encoded strings. -/
theorem packets.ColumnMeta.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ColumnMeta) (buf : alloc.vec.Vec U8)
    (h : buf.length + ((metaFields self).map lenencStr).flatten.length ≤ Usize.max) :
    packets.ColumnMeta.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ ((metaFields self).map lenencStr).flatten ⦄ := by
  unfold packets.ColumnMeta.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [metaFields, List.map, List.flatten] at h ⊢
  step*
  all_goals (simp_all; try omega)

end mysql_common
