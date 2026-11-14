import Defs
import Proofs.Util.PacketsColStmt
import Proofs.Misc.Raw.Bytes.RawBytes
import Proofs.Constants.ColumnFlags

/-! Statements for `impl Column`: `new` and the `with_*` builders (spec file:
`Specs/Packets/StmtBinlog.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PCSUtil

namespace mysql_common

private theorem sb_ok {α β : Type} {x : α} {k : α → Result β} {P : β → Prop} (h : k x ⦃ P ⦄) :
    Std.bind (ok x) k ⦃ P ⦄ :=
  WP.spec_bind (Pₘ := fun y => y = x) ((WP.spec_ok x).mpr rfl) (by rintro _ rfl; exact h)

/-- `Column::new(ty)`: the catalog `def` (`ColumnMeta::default`), every other string empty, every
    number 0, flags empty, the given column type. -/
theorem packets.Column.new_spec (ty : constants.ColumnType) :
    packets.Column.new ty ⦃ c => ColDef.ofColumn c =
      { catalog := utf8 "def", schema := [], table := [], orgTable := [], colName := [],
        orgName := [], charset := 0, length := 0, type := ty, flags := 0, decimals := 0 } ⦄ := by
  unfold packets.Column.new
  simp only [alloc.sync.Arc.Insts.CoreDefaultDefault.default,
    packets.ColumnMeta.Insts.CoreDefaultDefault.default, core.str.Str.as_bytes,
    misc.raw.bytes.RawBytes.new, misc.raw.bytes.RawBytes.Insts.CoreDefaultDefault.default,
    misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default, misc.raw.int.RawInt.Insts.CoreDefaultDefault.default,
    misc.raw._const.Const.Insts.CoreDefaultDefault.default,
    constants.ColumnFlags.Insts.CoreDefaultDefault.default, constants.ColumnFlags.empty,
    misc.raw._const.Const.new, core.marker.PhantomData.Insts.CoreDefaultDefault.default,
    core.convert.IntoFrom.into, core.convert.FromSame.from]
  simp only [bind_ok, Std.bind_assoc]
  iterate 8 apply sb_ok
  apply (WP.spec_ok _).mpr
  simp [ColDef.ofColumn, cowList]
  refine ⟨?_, rfl, rfl, rfl⟩
  unfold packets.ColumnMeta.DEFAULT_CATALOG_NAME
  decide +kernel

/-- `with_catalog`: replaces the catalog by (an owned copy of) the given bytes; nothing else
    changes. -/
theorem packets.Column.with_catalog_spec (self : packets.Column) (catalog : Slice U8) :
    packets.Column.with_catalog self catalog ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with catalog := catalog.val } ⦄ := by
  unfold packets.Column.with_catalog
  apply WP.spec_bind (Pₘ := fun rb => rb.1 = .Borrowed catalog)
  · rw [misc.raw.bytes.RawBytes.new_eq _ _ catalog (.Borrowed catalog) rfl]; exact (WP.spec_ok _).mpr rfl
  intro rb hrb
  apply WP.spec_bind (raw_into_owned _ _)
  intro rb1 h
  apply WP.spec_bind (Pₘ := fun p => p = (self.meta, fun t => t)) ((WP.spec_ok _).mpr rfl)
  rintro _ rfl
  apply (WP.spec_ok _).mpr
  rw [hrb] at h
  simp only [ColDef.ofColumn, h]
  rfl

/-- `with_schema`: replaces the schema; nothing else changes. -/
theorem packets.Column.with_schema_spec (self : packets.Column) (schema : Slice U8) :
    packets.Column.with_schema self schema ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with schema := schema.val } ⦄ := by
  unfold packets.Column.with_schema
  apply WP.spec_bind (Pₘ := fun rb => rb.1 = .Borrowed schema)
  · rw [misc.raw.bytes.RawBytes.new_eq _ _ schema (.Borrowed schema) rfl]; exact (WP.spec_ok _).mpr rfl
  intro rb hrb
  apply WP.spec_bind (raw_into_owned _ _)
  intro rb1 h
  apply WP.spec_bind (Pₘ := fun p => p = (self.meta, fun t => t)) ((WP.spec_ok _).mpr rfl)
  rintro _ rfl
  apply (WP.spec_ok _).mpr
  rw [hrb] at h
  simp only [ColDef.ofColumn, h]
  rfl

/-- `with_table`: replaces the table; nothing else changes. -/
theorem packets.Column.with_table_spec (self : packets.Column) (table : Slice U8) :
    packets.Column.with_table self table ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with table := table.val } ⦄ := by
  unfold packets.Column.with_table
  apply WP.spec_bind (Pₘ := fun rb => rb.1 = .Borrowed table)
  · rw [misc.raw.bytes.RawBytes.new_eq _ _ table (.Borrowed table) rfl]; exact (WP.spec_ok _).mpr rfl
  intro rb hrb
  apply WP.spec_bind (raw_into_owned _ _)
  intro rb1 h
  apply WP.spec_bind (Pₘ := fun p => p = (self.meta, fun t => t)) ((WP.spec_ok _).mpr rfl)
  rintro _ rfl
  apply (WP.spec_ok _).mpr
  rw [hrb] at h
  simp only [ColDef.ofColumn, h]
  rfl

/-- `with_org_table`: replaces the original table name; nothing else changes. -/
theorem packets.Column.with_org_table_spec (self : packets.Column) (org_table : Slice U8) :
    packets.Column.with_org_table self org_table ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with orgTable := org_table.val } ⦄ := by
  unfold packets.Column.with_org_table
  apply WP.spec_bind (Pₘ := fun rb => rb.1 = .Borrowed org_table)
  · rw [misc.raw.bytes.RawBytes.new_eq _ _ org_table (.Borrowed org_table) rfl]; exact (WP.spec_ok _).mpr rfl
  intro rb hrb
  apply WP.spec_bind (raw_into_owned _ _)
  intro rb1 h
  apply WP.spec_bind (Pₘ := fun p => p = (self.meta, fun t => t)) ((WP.spec_ok _).mpr rfl)
  rintro _ rfl
  apply (WP.spec_ok _).mpr
  rw [hrb] at h
  simp only [ColDef.ofColumn, h]
  rfl

/-- `with_name`: replaces the column name; nothing else changes. -/
theorem packets.Column.with_name_spec (self : packets.Column) («name» : Slice U8) :
    packets.Column.with_name self «name» ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with colName := «name».val } ⦄ := by
  unfold packets.Column.with_name
  apply WP.spec_bind (Pₘ := fun rb => rb.1 = .Borrowed «name»)
  · rw [misc.raw.bytes.RawBytes.new_eq _ _ «name» (.Borrowed «name») rfl]; exact (WP.spec_ok _).mpr rfl
  intro rb hrb
  apply WP.spec_bind (raw_into_owned _ _)
  intro rb1 h
  apply WP.spec_bind (Pₘ := fun p => p = (self.meta, fun t => t)) ((WP.spec_ok _).mpr rfl)
  rintro _ rfl
  apply (WP.spec_ok _).mpr
  rw [hrb] at h
  simp only [ColDef.ofColumn, h]
  rfl

/-- `with_org_name`: replaces the original column name; nothing else changes. -/
theorem packets.Column.with_org_name_spec (self : packets.Column) (org_name : Slice U8) :
    packets.Column.with_org_name self org_name ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with orgName := org_name.val } ⦄ := by
  unfold packets.Column.with_org_name
  apply WP.spec_bind (Pₘ := fun rb => rb.1 = .Borrowed org_name)
  · rw [misc.raw.bytes.RawBytes.new_eq _ _ org_name (.Borrowed org_name) rfl]; exact (WP.spec_ok _).mpr rfl
  intro rb hrb
  apply WP.spec_bind (raw_into_owned _ _)
  intro rb1 h
  apply WP.spec_bind (Pₘ := fun p => p = (self.meta, fun t => t)) ((WP.spec_ok _).mpr rfl)
  rintro _ rfl
  apply (WP.spec_ok _).mpr
  rw [hrb] at h
  simp only [ColDef.ofColumn, h]
  rfl

/-- `with_flags`: replaces the flags; nothing else changes. -/
theorem packets.Column.with_flags_spec (self : packets.Column) (flags : constants.ColumnFlags) :
    packets.Column.with_flags self flags ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with flags := flags.val } ⦄ := by
  unfold packets.Column.with_flags
  simp only [misc.raw._const.Const.new]
  exact sb_ok ((WP.spec_ok _).mpr rfl)

/-- `with_column_length`: replaces the column length; nothing else changes. -/
theorem packets.Column.with_column_length_spec (self : packets.Column) (column_length : U32) :
    packets.Column.with_column_length self column_length ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with length := column_length.val } ⦄ := by
  unfold packets.Column.with_column_length
  simp only [misc.raw.int.RawInt.new]
  exact sb_ok ((WP.spec_ok _).mpr rfl)

/-- `with_character_set`: replaces the character set; nothing else changes. -/
theorem packets.Column.with_character_set_spec (self : packets.Column) (character_set : U16) :
    packets.Column.with_character_set self character_set ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with charset := character_set.val } ⦄ := by
  unfold packets.Column.with_character_set
  simp only [misc.raw.int.RawInt.new]
  exact sb_ok ((WP.spec_ok _).mpr rfl)

/-- `with_decimals`: replaces the decimals; nothing else changes. -/
theorem packets.Column.with_decimals_spec (self : packets.Column) (decimals : U8) :
    packets.Column.with_decimals self decimals ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with decimals := decimals.val } ⦄ := by
  unfold packets.Column.with_decimals
  simp only [misc.raw.int.RawInt.new]
  exact sb_ok ((WP.spec_ok _).mpr rfl)

end mysql_common
