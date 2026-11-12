import Defs
import Proofs.Util.PacketsColStmt
import Proofs.Packets.ColumnMeta
import Proofs.Io.ParseBuf
import Proofs.Misc.Raw.Int.RawInt
import Proofs.Misc.Raw.Const.Const
import Proofs.Misc.Raw.Int.ConstU8
import Proofs.Misc.Raw.Int.U8
import Proofs.Misc.Raw.Int.LeU16
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Misc.Raw.Skip
import Proofs.Constants.ColumnType
import Proofs.Constants.ColumnFlags
import Proofs.Defs.LemmasCF

/-! Statements for `struct Column and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PCSUtil

namespace mysql_common

@[local step]
private theorem branch_spec_col {T E : Type} (r : core.result.Result T E) :
    core.result.Result.Insts.CoreOpsTry.branch r ⦃ cf =>
      (∀ v, cf = .Continue v → r = .Ok v) ∧
      (∀ res, cf = .Break res → ∃ e, r = .Err e ∧ res = .Err e) ⦄ :=
  mysql_common.PCSUtil.branch_spec' r

/-- `MyDeserialize for Column`: `SIZE` is `None`. -/
theorem packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  unfold packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

private theorem d_constu8 (buf : io.ParseBuf) (x : U8) (t : List U8) (hb : buf.val = x :: t) :
    misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize 12#u8
      packets.InvalidFixedLengthFieldsLen.Insts.CoreErrorError
      packets.InvalidFixedLengthFieldsLen.Insts.CoreDefaultDefault () buf ⦃ r rest =>
      ((okPart r).isSome ↔ x.val = 12) ∧ rest.val = t ⦄ := by
  apply WP.spec_mono (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec _ _ _
    (by simp [packets.InvalidFixedLengthFieldsLen.Insts.CoreDefaultDefault.default]) buf (by simp [hb]))
  rintro ⟨r, rest⟩ h
  simp_all [WP.uncurry', leNat]

private theorem d_u16 (buf : io.ParseBuf) (x y : U8) (t : List U8) (hb : buf.val = x :: y :: t) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 () buf ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val + 256 * y.val) ∧ rest.val = t ⦄ := by
  have := misc.raw.int.RawInt.deserialize_spec misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 buf
    (fun (o : Option U16) (rest : io.ParseBuf) => o.map (fun v : U16 => v.val) = some (x.val + 256 * y.val) ∧ rest.val = t)
    (by
      apply WP.spec_mono (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec buf (by simp [hb]))
      rintro ⟨r, rest⟩ h
      simp_all [WP.uncurry', leNat])
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ h
  simp_all [WP.uncurry', Option.map_map, Function.comp_def]

private theorem d_u32 (buf : io.ParseBuf) (x0 x1 x2 x3 : U8) (t : List U8) (hb : buf.val = x0 :: x1 :: x2 :: x3 :: t) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 () buf ⦃ r rest =>
      (okPart r).map (·.1.val) = some (leNat [x0, x1, x2, x3]) ∧ rest.val = t ⦄ := by
  have := misc.raw.int.RawInt.deserialize_spec misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 buf
    (fun (o : Option U32) (rest : io.ParseBuf) => o.map (fun v : U32 => v.val) = some (leNat [x0, x1, x2, x3]) ∧ rest.val = t)
    (by
      apply WP.spec_mono (misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec buf (by simp [hb]))
      rintro ⟨r, rest⟩ h
      simp_all [WP.uncurry'])
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ h
  simp_all [WP.uncurry', Option.map_map, Function.comp_def]

private theorem d_u8 (buf : io.ParseBuf) (x : U8) (t : List U8) (hb : buf.val = x :: t) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
      U8.Insts.Mysql_commonMiscRawIntIntReprU8 () buf ⦃ r rest =>
      (okPart r).map (·.1.val) = some x.val ∧ rest.val = t ⦄ := by
  have := misc.raw.int.RawInt.deserialize_spec U8.Insts.Mysql_commonMiscRawIntIntReprU8 buf
    (fun (o : Option U8) (rest : io.ParseBuf) => o.map (fun v : U8 => v.val) = some x.val ∧ rest.val = t)
    (by
      apply WP.spec_mono (U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec buf (by simp [hb]))
      rintro ⟨r, rest⟩ h
      simp_all [WP.uncurry', leNat])
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ h
  simp_all [WP.uncurry', Option.map_map, Function.comp_def]

private theorem d_coltype (buf : io.ParseBuf) (x : U8) (t : List U8) (hb : buf.val = x :: t) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
      U8.Insts.Mysql_commonMiscRawIntIntReprU8
      constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType
      constants.UnknownColumnType.Insts.CoreErrorError () buf ⦃ r rest =>
      (okPart r).map (·.1) = columnTypeOfCode x.val ∧ rest.val = t ⦄ := by
  have := misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec U8.Insts.Mysql_commonMiscRawIntIntReprU8 constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType constants.UnknownColumnType.Insts.CoreErrorError buf
    (fun (o : Option U8) (rest : io.ParseBuf) => o = some x ∧ rest.val = t)
    (by
      apply WP.spec_mono (U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec buf (by simp [hb]))
      rintro ⟨r, rest⟩ h
      simp only [WP.uncurry', hb, List.take, List.drop, leNat] at h ⊢
      refine ⟨?_, h.2⟩
      cases r <;> simp_all [okPart]
      rename_i a
      rw [← byte_eq_self a, ← byte_eq_self x, h.1])
    (fun (p : U8) (o : Option constants.ColumnType) => o = columnTypeOfCode p.val)
    (by
      intro p
      simp only [constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from_spec]
      apply (WP.spec_ok _).mpr
      cases columnTypeOfCode p.val <;> rfl)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨o, ⟨rfl, h2⟩, h3⟩
  exact ⟨h3, h2⟩

private theorem d_colflags (buf : io.ParseBuf) (x y : U8) (t : List U8) (hb : buf.val = x :: y :: t) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16
      constants.ColumnFlags.Insts.CoreConvertTryFromU16UnknownColumnFlags
      constants.UnknownColumnFlags.Insts.CoreErrorError () buf ⦃ r rest =>
      (okPart r).map (·.1.val) = some (x.val + 256 * y.val) ∧ rest.val = t ⦄ := by
  have := misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 constants.ColumnFlags.Insts.CoreConvertTryFromU16UnknownColumnFlags constants.UnknownColumnFlags.Insts.CoreErrorError buf
    (fun (o : Option U16) (rest : io.ParseBuf) => o.map (fun v : U16 => v.val) = some (x.val + 256 * y.val) ∧ rest.val = t)
    (by
      apply WP.spec_mono (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec buf (by simp [hb]))
      rintro ⟨r, rest⟩ h
      simp_all [WP.uncurry', leNat])
    (fun (p : U16) (o : Option constants.ColumnFlags) => o.map (fun v : constants.ColumnFlags => v.val) = some p.val)
    (by
      intro p
      apply WP.spec_mono (constants.ColumnFlags.Insts.CoreConvertTryFromU16UnknownColumnFlags.try_from_spec p)
      intro r hr
      have : p.val &&& columnFlagsAll = p.val := by
        have hp : p.val < 2 ^ 16 := by scalar_tac
        simp only [columnFlagsAll]
        rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hp]
      simp_all [okPart])
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨o, ⟨h1, h2⟩, h3⟩
  refine ⟨?_, h2⟩
  cases o with
  | none => simp at h1
  | some p => simp_all [Option.map_map, Function.comp_def]

private theorem d_skip (buf : io.ParseBuf) (x y : U8) (t : List U8) (hb : buf.val = x :: y :: t) :
    misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize 2#usize () buf ⦃ r rest =>
      (okPart r).isSome ∧ rest.val = t ⦄ := by
  apply WP.spec_mono (misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec _ buf (by simp [hb]))
  rintro ⟨r, rest⟩ h
  simp_all [WP.uncurry']

private theorem len13 {α : Type} (l : List α) (h : l.length = 13) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, l = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] := by
  match l, h with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12], _ => exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

private theorem parse_colmeta (h64 : Target64) (buf : io.ParseBuf) :
    io.ParseBuf.parse packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple buf () ⦃ r rest =>
      lenencStrs 6 buf.val = ((okPart r).map metaFields, rest.val) ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq])]
  apply WP.spec_mono (packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf)
  rintro ⟨r, rest⟩ h
  simp only [WP.uncurry'] at h ⊢
  exact h.symm

private theorem parse_13 (buf : io.ParseBuf) :
    io.ParseBuf.parse io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize buf 13#usize ⦃ r rest =>
      if 13 ≤ buf.length then
        (okPart r).map (·.val) = some (buf.val.take 13) ∧ rest.val = buf.val.drop 13
      else okPart r = none ∧ rest = buf ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE])]
  exact mysql_common.PBUtil.deserialize_usize_ok 13#usize buf

attribute [local step] packets.ColumnMeta.into_owned_spec parse_13

/-- `MyDeserialize for Column`: total; `colDefRead` (six strings, then 13 bytes: `0x0c`, character set, column length, type, flags, decimals, filler). -/
theorem packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64) (buf : io.ParseBuf) :
    packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map ColDef.ofColumn, rest.val) = colDefRead buf.val ⦄ := by
  unfold packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize alloc.sync.Arc.new
  step with parse_colmeta h64 buf as ⟨r, buf1, hm⟩
  step*
  · obtain rfl := cf_post cm (by assumption)
    obtain rfl := cf1_post pb (by assumption)
    have hlen : 13 ≤ buf1.length := by
      by_contra hc; simp [hc, okPart] at r1_post
    simp only [hlen, ite_true, okPart, Option.map] at r1_post
    obtain ⟨hpb, hb2⟩ := r1_post
    have hpb' : pb.val = buf1.val.take 13 := by simpa using hpb
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, hx⟩ :=
      len13 pb.val (by rw [hpb']; simp; omega)
    have htake : buf1.val.take 13 = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] := hpb' ▸ hx
    clear hpb hpb' cf_post cf_post1 cf1_post cf1_post1
    simp only [io.ParseBuf.parse_unchecked_eq]
    step with d_constu8 pb x0 _ hx as ⟨r2, b3, h2a, h2b⟩
    step*
    step with d_u16 b3 x1 x2 _ h2b as ⟨r3, b4, h3a, h3b⟩
    step*
    step with d_u32 b4 x3 x4 x5 x6 _ h3b as ⟨r4, b5, h4a, h4b⟩
    step*
    step with d_coltype b5 x7 _ h4b as ⟨r5, b6, h5a, h5b⟩
    step*
    step with d_colflags b6 x8 x9 _ h5b as ⟨r6, b7, h6a, h6b⟩
    step*
    step with d_u8 b7 x10 _ h6b as ⟨r7, b8, h7a, h7b⟩
    step*
    step with d_skip b8 x11 x12 _ h7b as ⟨r8, b9, h8a, h8b⟩
    step*
    all_goals (simp_all [colDefRead, metaFields, okPart, ColDef.ofColumn, leNat])
    all_goals (split_ifs with hlt; · omega
               split <;> simp_all)
  · split_ifs at * <;> simp_all [colDefRead, metaFields, okPart]
  · simp_all [colDefRead, okPart]

/-- Round trip: a column definition in the protocol layout (`colDefEnc`) is read back. -/
theorem packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h64 : Target64) (c : packets.Column) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = colDefEnc (ColDef.ofColumn c) ++ tail) :
    packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map ColDef.ofColumn = some (ColDef.ofColumn c) ∧ rest.val = tail ⦄ := by
  have hmax : Usize.max < 2 ^ 64 := by
    simp [Target64] at h64; simp [Usize.max, Usize.numBits, h64]
  have hs : ∀ s ∈ [(ColDef.ofColumn c).catalog, (ColDef.ofColumn c).schema, (ColDef.ofColumn c).table,
      (ColDef.ofColumn c).orgTable, (ColDef.ofColumn c).colName, (ColDef.ofColumn c).orgName], s.length < 2 ^ 64 := by
    intro s hs
    simp only [ColDef.ofColumn, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact lt_of_le_of_lt (cowList_length_le _) hmax
  have hc : (ColDef.ofColumn c).charset < 2 ^ 16 := by simp only [ColDef.ofColumn]; scalar_tac
  have hl : (ColDef.ofColumn c).length < 2 ^ 32 := by simp only [ColDef.ofColumn]; scalar_tac
  have hf : (ColDef.ofColumn c).flags < 2 ^ 16 := by
    simp only [ColDef.ofColumn]; exact (c.flags.1 : U16).hBounds
  have hd : (ColDef.ofColumn c).decimals < 256 := by simp only [ColDef.ofColumn]; scalar_tac
  apply WP.spec_mono (packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf)
  rintro ⟨r, rest⟩ hr
  simp only [WP.uncurry'] at hr ⊢
  rw [h, colDefRead_colDefEnc _ _ hs hc hl hf hd] at hr
  simpa using hr

/-- `MySerialize for Column`: appends `colDefEncCrate`, **which has `column_length` and `character_set` in the wrong order** (not `colDefEnc`, the protocol layout the reader expects): the crate's own reader reads it back **with no error but a wrong `character_set` and `column_length`** (`Defs.colDefRead_colDefEncCrate`). -/
theorem packets.Column.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.Column) (buf : alloc.vec.Vec U8)
    (h : buf.length + (colDefEncCrate (ColDef.ofColumn self)).length ≤ Usize.max) :
    packets.Column.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ colDefEncCrate (ColDef.ofColumn self) ⦄ := by
  simp only [colDefEncCrate, ColDef.ofColumn, List.length_append, List.length_cons,
    List.length_nil, mysql_common.PBUtil.length_leBytes] at h
  unfold packets.Column.Insts.Mysql_commonProtoMySerialize.serialize alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref
  rw [Aeneas.Std.bind_ok]
  step with packets.ColumnMeta.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨b1, h1⟩
  · simp [metaFields, alloc.vec.Vec.length] at h ⊢; omega
  step*
  all_goals (simp_all [colDefEncCrate, ColDef.ofColumn, metaFields, alloc.vec.Vec.length]; try omega)
  all_goals rfl

/-- `column_length`: the field. -/
theorem packets.Column.impl.column_length_eq (self : packets.Column) :
    packets.Column.impl.column_length self = ok self.column_length.1 := by
  unfold packets.Column.impl.column_length; exact misc.raw.int.RawInt.deref_eq _ _

/-- `column_type`: the field. -/
theorem packets.Column.impl.column_type_eq (self : packets.Column) :
    packets.Column.impl.column_type self = ok self.column_type.1 := by
  unfold packets.Column.impl.column_type; exact misc.raw._const.Const.deref_eq _

/-- `character_set`: the field. -/
theorem packets.Column.impl.character_set_eq (self : packets.Column) :
    packets.Column.impl.character_set self = ok self.character_set.1 := by
  unfold packets.Column.impl.character_set; exact misc.raw.int.RawInt.deref_eq _ _

/-- `flags`: the field. -/
theorem packets.Column.impl.flags_eq (self : packets.Column) :
    packets.Column.impl.flags self = ok self.flags.1 := by
  unfold packets.Column.impl.flags; exact misc.raw._const.Const.deref_eq _

/-- `decimals`: the field. -/
theorem packets.Column.impl.decimals_eq (self : packets.Column) :
    packets.Column.impl.decimals self = ok self.decimals.1 := by
  unfold packets.Column.impl.decimals; exact misc.raw.int.RawInt.deref_eq _ _

/-- `catalog_ref`: **returns the `schema` field, not `catalog`** (`self.schema.as_bytes()`; a bug in the crate). -/
theorem packets.Column.catalog_ref_spec (self : packets.Column) :
    packets.Column.catalog_ref self ⦃ s => s.val = cowList self.«meta».schema.1 ⦄ := by
  unfold packets.Column.catalog_ref alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref
  rw [Aeneas.Std.bind_ok]; exact packets.ColumnMeta.catalog_ref_spec self.meta

/-- `schema_ref`: the `schema` field. -/
theorem packets.Column.schema_ref_spec (self : packets.Column) :
    packets.Column.schema_ref self ⦃ s => s.val = cowList self.«meta».schema.1 ⦄ := by
  unfold packets.Column.schema_ref alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref
  rw [Aeneas.Std.bind_ok]; exact packets.ColumnMeta.schema_ref_spec self.meta

/-- `table_ref`: the `table` field. -/
theorem packets.Column.table_ref_spec (self : packets.Column) :
    packets.Column.table_ref self ⦃ s => s.val = cowList self.«meta».table.1 ⦄ := by
  unfold packets.Column.table_ref alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref
  rw [Aeneas.Std.bind_ok]; exact packets.ColumnMeta.table_ref_spec self.meta

/-- `org_table_ref`: the `org_table` field. -/
theorem packets.Column.org_table_ref_spec (self : packets.Column) :
    packets.Column.org_table_ref self ⦃ s => s.val = cowList self.«meta».org_table.1 ⦄ := by
  unfold packets.Column.org_table_ref alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref
  rw [Aeneas.Std.bind_ok]; exact packets.ColumnMeta.org_table_ref_spec self.meta

/-- `name_ref`: the `name` field. -/
theorem packets.Column.name_ref_spec (self : packets.Column) :
    packets.Column.name_ref self ⦃ s => s.val = cowList self.«meta».«name».1 ⦄ := by
  unfold packets.Column.name_ref alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref
  rw [Aeneas.Std.bind_ok]; exact packets.ColumnMeta.name_ref_spec self.meta

/-- `org_name_ref`: the `org_name` field. -/
theorem packets.Column.org_name_ref_spec (self : packets.Column) :
    packets.Column.org_name_ref self ⦃ s => s.val = cowList self.«meta».org_name.1 ⦄ := by
  unfold packets.Column.org_name_ref alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref
  rw [Aeneas.Std.bind_ok]; exact packets.ColumnMeta.org_name_ref_spec self.meta

end mysql_common
