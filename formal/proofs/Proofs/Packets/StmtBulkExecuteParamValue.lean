import Defs
import Proofs.Util.StmtBulkParam
import Proofs.Value.Value

/-! Statements for `struct StmtBulkExecuteParamValue and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Helper lemmas:
`Proofs/Util/StmtBulkParam.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `StmtBulkExecuteParamValue::new(v)`: the value, with the indicator `NULL` for `NULL` and
    `NONE` otherwise (`bulkInd`). -/
theorem packets.StmtBulkExecuteParamValue.new_spec (v : value.Value) :
    packets.StmtBulkExecuteParamValue.new v ⦃ x =>
      x.value = v ∧ bulkIndicatorCode x.indicator.1 = bulkInd (Val.ofValue v) ⦄ := by
  cases v <;> simp [packets.StmtBulkExecuteParamValue.new, SBParam.bind_const_new, bulkIndicatorCode,
    bulkInd, Val.ofValue]

/-- `indicator`: the indicator. -/
theorem packets.StmtBulkExecuteParamValue.impl.indicator_eq (self : packets.StmtBulkExecuteParamValue) :
    packets.StmtBulkExecuteParamValue.impl.indicator self = ok self.indicator.1 := by
  obtain ⟨⟨i, u⟩, v⟩ := self; cases u; rfl

/-- `value`: the value. -/
theorem packets.StmtBulkExecuteParamValue.impl.value_eq (self : packets.StmtBulkExecuteParamValue) :
    packets.StmtBulkExecuteParamValue.impl.value self = ok self.value := by
  rfl

/-- `MyDeserialize for StmtBulkExecuteParamValue`: `SIZE` is `None`. -/
theorem packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.SIZE_eq :
    packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.SIZE = none := by
  unfold packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.SIZE; rfl

private theorem deserialize_aux (h64 : Target64) (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (buf : io.ParseBuf)
    (hnp : ∀ e, bulkValueRead ct (isUnsigned flags) buf.val ≠ .panic e) :
    packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf ⦃ r rest =>
      bulkValueRead ct (isUnsigned flags) buf.val = .done ((okPart r).map bulkIV) rest.val ⦄ := by
  unfold packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize
  apply WP.spec_bind (SBParam.parse_const_u8
    constants.MariadbBulkIndicator.Insts.CoreConvertTryFromU8UnknownMariadbBulkIndicator
    constants.UnknownMariadbBulkIndicator.Insts.CoreErrorError (fun p => SBParam.indOfCode p.val)
    SBParam.ind_try_from buf)
  rintro ⟨r, buf1⟩ hr
  cases hb : buf.val with
  | nil =>
    simp only [hb] at hr
    obtain ⟨hr1, rfl⟩ := hr
    cases r with
    | Ok v => simp [okPart] at hr1
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch, okPart, bulkValueRead, hb]
  | cons x t =>
    simp only [hb] at hr hnp
    obtain ⟨hr1, hr2⟩ := hr
    cases r with
    | Err e =>
      simp only [okPart, Option.map_none] at hr1
      have hx := SBParam.indOfCode_none.mp hr1.symm
      simp [core.result.Result.Insts.CoreOpsTry.branch, okPart, bulkValueRead, hx, hr2]
    | Ok v =>
      simp only [okPart, Option.map_some] at hr1
      have hcode := SBParam.indOfCode_some hr1.symm
      have hx3 : ¬ 3 < x.val := fun h => by
        rw [SBParam.indOfCode_none.mpr h] at hr1; simp at hr1
      simp [core.result.Result.Insts.CoreOpsTry.branch, misc.raw._const.Const.deref_eq, SBParam.ind_eq_null, hcode]
      by_cases h1 : x.val = 1
      · simp [h1, okPart, bulkIV, bulkValueRead, hr2, hcode, Val.ofValue]
      · simp only [h1, ite_false]
        cases hs : binSupported ct
        · exfalso
          apply hnp .panic
          simp [bulkValueRead, hx3, h1, hs]
        · apply WP.spec_bind (SBParam.vd_bin_spec h64 ct flags hs buf1)
          rintro ⟨r1, buf2⟩ h2
          rw [hr2] at h2
          cases r1 with
          | Err e =>
            simp [okPart] at h2
            simp [okPart, bulkValueRead, hx3, h1, hs, ← h2]
          | Ok w =>
            obtain ⟨wv, wu⟩ := w
            simp [okPart] at h2
            simp [okPart, bulkValueRead, hx3, h1, hs, ← h2, bulkIV, hcode]
            rfl

/-- `MyDeserialize for StmtBulkExecuteParamValue` for a parameter of column type `ct` with
    column flags `flags`: exactly `bulkValueRead` whenever that reader returns. **Crate
    behaviour**: a value is read after the `DEFAULT` and `IGNORE` indicators (the protocol sends
    none). -/
theorem packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_spec
    (h64 : Target64) (ct : constants.ColumnType) (flags : constants.ColumnFlags) (buf : io.ParseBuf)
    (r0 : Option (Nat × Val)) (rest0 : List U8)
    (h : bulkValueRead ct (isUnsigned flags) buf.val = .done r0 rest0) :
    packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf ⦃ r rest =>
      (okPart r).map bulkIV = r0 ∧ rest.val = rest0 ⦄ := by
  have := deserialize_aux h64 ct flags buf (by intro e he; rw [h] at he; cases he)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ hr
  simp only [WP.uncurry'_pair, h, ReadOut.done.injEq] at hr ⊢
  exact ⟨hr.1.symm, hr.2.symm⟩

/-- **Crash path.** `MyDeserialize for StmtBulkExecuteParamValue` panics where `bulkValueRead`
    does: an indicator other than `NULL` for a column type the binary reader does not support. -/
theorem packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_panics
    (h64 : Target64) (ct : constants.ColumnType) (flags : constants.ColumnFlags) (buf : io.ParseBuf) (e : Error)
    (h : bulkValueRead ct (isUnsigned flags) buf.val = .panic e) :
    packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf = fail e := by
  have _ := h64
  cases hb : buf.val with
  | nil => rw [hb] at h; simp [bulkValueRead] at h
  | cons x t =>
    rw [hb] at h
    simp only [bulkValueRead] at h
    by_cases hx3 : 3 < x.val
    · simp [hx3] at h
    by_cases h1 : x.val = 1
    · simp [h1] at h
    cases hs : binSupported ct
    · simp only [hx3, h1, hs, ite_false, Bool.false_eq_true, ReadOut.panic.injEq] at h
      subst h
      unfold packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize
      obtain ⟨⟨r, buf1⟩, he, hr⟩ := PBUtil.spec_eq_ok (SBParam.parse_const_u8
        constants.MariadbBulkIndicator.Insts.CoreConvertTryFromU8UnknownMariadbBulkIndicator
        constants.UnknownMariadbBulkIndicator.Insts.CoreErrorError (fun p => SBParam.indOfCode p.val)
        SBParam.ind_try_from buf)
      rw [he]
      simp only [hb, WP.uncurry'_pair] at hr
      obtain ⟨hr1, hr2⟩ := hr
      cases r with
      | Err e =>
        simp only [okPart, Option.map_none] at hr1
        exact absurd (SBParam.indOfCode_none.mp hr1.symm) hx3
      | Ok v =>
        simp only [okPart, Option.map_some] at hr1
        have hcode := SBParam.indOfCode_some hr1.symm
        simp [core.result.Result.Insts.CoreOpsTry.branch, misc.raw._const.Const.deref_eq, SBParam.ind_eq_null,
          hcode, h1, SBParam.vd_bin_unsupported ct flags hs]
    · simp [hx3, h1, hs] at h
      split at h <;> simp at h

/-- `MySerialize for StmtBulkExecuteParamValue`: appends `bulkValueEnc` (the indicator, then the
    binary encoding of the value). -/
theorem packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.StmtBulkExecuteParamValue) (buf : alloc.vec.Vec U8)
    (h : buf.length + (bulkValueEnc (bulkIV self)).length ≤ Usize.max) :
    packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ bulkValueEnc (bulkIV self) ⦄ := by
  unfold packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [bulkValueEnc, bulkIV, List.length_cons] at h ⊢
  apply WP.spec_bind (SBParam.const_ind_serialize self.indicator buf (by omega))
  intro b1 hb1
  have hl : b1.length = buf.length + 1 := by
    simp only [alloc.vec.Vec.length, hb1, List.length_append, List.length_singleton]
  apply WP.spec_mono (value.Value.Insts.Mysql_commonProtoMySerialize.serialize_spec self.value b1 (by omega))
  intro b2 hb2
  rw [hb2, hb1]
  simp

end mysql_common
