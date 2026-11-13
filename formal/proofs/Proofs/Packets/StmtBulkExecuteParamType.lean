import Defs
import Proofs.Util.StmtBulkParam

/-! Statements for `struct StmtBulkExecuteParamType and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Helper lemmas:
`Proofs/Util/StmtBulkParam.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `StmtBulkExecuteParamType::new(type, flags)`: the given type and flags. -/
theorem packets.StmtBulkExecuteParamType.new_eq (type : constants.ColumnType)
    (flags : constants.StmtExecuteParamFlags) :
    packets.StmtBulkExecuteParamType.new type flags = ok ⟨(type, ()), (flags, ())⟩ := by
  simp only [packets.StmtBulkExecuteParamType.new, SBParam.bind_const_new]

/-- `from_value(v)`: the type the crate sends for the value (`bulkTy`). -/
@[step]
theorem packets.StmtBulkExecuteParamType.from_value_spec (v : value.Value) :
    packets.StmtBulkExecuteParamType.from_value v ⦃ t =>
      (columnTypeCode t.type.1, t.flags.1.val) = bulkTy (Val.ofValue v) ⦄ := by
  cases v <;> simp [packets.StmtBulkExecuteParamType.from_value, constants.StmtExecuteParamFlags.empty,
    SBParam.bind_const_new, bulkTy, Val.ofValue]
  unfold constants.StmtExecuteParamFlags.UNSIGNED; rfl

/-- `column_type`: the type. -/
theorem packets.StmtBulkExecuteParamType.column_type_eq (self : packets.StmtBulkExecuteParamType) :
    packets.StmtBulkExecuteParamType.column_type self = ok self.type.1 := by
  obtain ⟨⟨t, u⟩, f⟩ := self; cases u; rfl

/-- `flags`: the flags. -/
theorem packets.StmtBulkExecuteParamType.impl.flags_eq (self : packets.StmtBulkExecuteParamType) :
    packets.StmtBulkExecuteParamType.impl.flags self = ok self.flags.1 := by
  obtain ⟨t, ⟨f, u⟩⟩ := self; cases u; rfl

/-- `MyDeserialize for StmtBulkExecuteParamType`: **`SIZE` is `Some(3)`, but the type is 2
    bytes on the wire** (crate bug): `parse` (`parse_spec`) and the request reader consume 3
    bytes per type. -/
theorem packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 3#usize := by
  unfold packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

private theorem deserialize_aux (buf : io.ParseBuf) :
    packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map SBParam.ptOf, rest.val) = bulkTypeRead buf.val ⦄ := by
  unfold packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  apply WP.spec_bind (SBParam.parse_const_u8 _ _ (fun p => columnTypeOfCode p.val) SBParam.coltype_try_from buf)
  rintro ⟨r, buf1⟩ hr
  cases hb : buf.val with
  | nil =>
    simp only [hb] at hr
    obtain ⟨hr1, rfl⟩ := hr
    cases r with
    | Ok v => simp [okPart] at hr1
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch, okPart, bulkTypeRead, hb]
  | cons x t =>
    simp only [hb] at hr
    obtain ⟨hr1, hr2⟩ := hr
    cases r with
    | Err e =>
      simp only [okPart, Option.map_none] at hr1
      simp [core.result.Result.Insts.CoreOpsTry.branch, okPart, bulkTypeRead, ← hr1, hr2]
    | Ok v =>
      simp only [okPart, Option.map_some] at hr1
      have hcode := SBParam.columnTypeCode_of_code hr1.symm
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      apply WP.spec_bind (SBParam.parse_const_u8
        constants.StmtExecuteParamFlags.Insts.CoreConvertTryFromU8UnknownStmtExecuteParamFlags
        constants.UnknownStmtExecuteParamFlags.Insts.CoreErrorError (fun p => if p.val = 0 ∨ p.val = 128 then some p else none)
        SBParam.flags_try_from buf1)
      rintro ⟨r1, buf2⟩ hr'
      cases hb1 : buf1.val with
      | nil =>
        simp only [hb1] at hr'
        obtain ⟨h1, rfl⟩ := hr'
        cases r1 with
        | Ok w => simp [okPart] at h1
        | Err e =>
          simp [okPart, bulkTypeRead, ← hr1, hb1]
          simp_all
      | cons y t' =>
        simp only [hb1] at hr'
        obtain ⟨h1, h2⟩ := hr'
        have ht : t = y :: t' := by rw [← hr2, hb1]
        cases r1 with
        | Err e =>
          simp only [okPart, Option.map_none] at h1
          simp [okPart, bulkTypeRead, ← hr1, ht, h2]
          split_ifs at h1
          simp_all
        | Ok w =>
          simp only [okPart, Option.map_some] at h1
          simp [okPart, bulkTypeRead, ← hr1, ht, h2]
          split_ifs at h1
          simp_all

/-- `MyDeserialize for StmtBulkExecuteParamType`: total; `bulkTypeRead` (a known type code,
    then a flag byte 0 or 128). -/
theorem packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun t => (columnTypeCode t.type.1, t.flags.1.val)), rest.val) =
        bulkTypeRead buf.val ⦄ := by
  exact deserialize_aux buf

private theorem parse_aux (buf : io.ParseBuf) :
    io.ParseBuf.parse packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple buf () ⦃ r rest =>
      if 3 ≤ buf.length then
        (okPart r).map SBParam.ptOf = (bulkTypeRead (buf.val.take 3)).1 ∧ rest.val = buf.val.drop 3
      else okPart r = none ∧ rest = buf ⦄ := by
  have hs : proto.MyDeserialize.SIZE packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple =
      ok (some 3#usize) := by
    simp only
    rw [packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq]
  by_cases h3 : 3 ≤ buf.length
  · simp only [h3, ite_true]
    apply io.ParseBuf.parse_of_size _ buf () 3#usize hs (by simpa using h3)
      (fun o => o.map SBParam.ptOf = (bulkTypeRead (buf.val.take 3)).1)
    intro sub hsub
    apply WP.spec_mono (deserialize_aux sub)
    rintro ⟨r, rest⟩ h
    simp only [WP.uncurry'_pair] at h ⊢
    have h3' : (3#usize).val = 3 := rfl
    rw [h3'] at hsub
    rw [← hsub, ← h]
  · simp only [h3, ite_false]
    have h3' : buf.length < 3 := by omega
    exact io.ParseBuf.parse_of_size_short _ buf () 3#usize hs h3'

/-- `buf.parse::<StmtBulkExecuteParamType>(())`: total; **consumes 3 bytes** (`SIZE`), of which
    `bulkTypeRead` reads two; an error with the buffer unchanged on fewer than 3 bytes (so a
    2-byte type at the end of a packet is rejected). -/
@[step]
theorem packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec
    (buf : io.ParseBuf) :
    io.ParseBuf.parse packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple buf () ⦃ r rest =>
      if 3 ≤ buf.length then
        (okPart r).map (fun t => (columnTypeCode t.type.1, t.flags.1.val)) = (bulkTypeRead (buf.val.take 3)).1 ∧
        rest.val = buf.val.drop 3
      else okPart r = none ∧ rest = buf ⦄ := by
  exact parse_aux buf

/-- `MySerialize for StmtBulkExecuteParamType`: appends the 2 bytes `bulkTypeEnc` (type code,
    flag byte). -/
@[step]
theorem packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.StmtBulkExecuteParamType) (buf : alloc.vec.Vec U8) (h : buf.length + 2 ≤ Usize.max) :
    packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ bulkTypeEnc (columnTypeCode self.type.1, self.flags.1.val) ⦄ := by
  unfold packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMySerialize.serialize
  apply WP.spec_bind (PCSUtil.const_coltype_serialize self.type buf (by omega))
  intro b1 hb1
  apply WP.spec_mono (SBParam.const_paramflags_serialize self.flags b1
    (by simp only [alloc.vec.Vec.length, hb1, List.length_append] at h ⊢; simp at h ⊢; omega))
  intro b2 hb2
  rw [hb2, hb1]
  simp [bulkTypeEnc]

end mysql_common
