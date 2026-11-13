import Defs
import Proofs.Util.ParseBuf
import Proofs.Io.ParseBuf
import Proofs.Misc.Raw.Int.U8
import Proofs.Misc.Raw.Const.Const
import Proofs.Constants.ColumnType
import Proofs.Util.PacketsColStmt
import Proofs.Value.Value

/-! Helper lemmas for the `StmtBulkExecuteParam{Type,Value,Values}` proofs. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.SBParam

/-- `buf.parse::<Const<T, u8>>(())` for a `TryFrom<u8>` described by `f`: an error with the buffer
    unchanged on an empty buffer, else the first byte converted by `f`, that byte consumed. -/
theorem parse_const_u8 {T E : Type} (tf : core.convert.TryFrom T U8 E) (err : core.error.Error E)
    (f : U8 → Option T) (hf : ∀ p, tf.try_from p ⦃ r => okPart r = f p ⦄) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple
      U8.Insts.Mysql_commonMiscRawIntIntReprU8 tf err) buf () ⦃ r rest =>
      match buf.val with
      | [] => okPart r = none ∧ rest = buf
      | x :: t => (okPart r).map (·.1) = f x ∧ rest.val = t ⦄ := by
  have hs : (misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple
      U8.Insts.Mysql_commonMiscRawIntIntReprU8 tf err).SIZE = ok (some 1#usize) := by
    simp only [misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq]
    simp [U8.Insts.Mysql_commonMiscRawIntIntReprU8.SIZE_eq]
  cases hb : buf.val with
  | nil =>
    apply io.ParseBuf.parse_of_size_short _ buf () 1#usize hs
    simp [hb]
  | cons x t =>
    have h := io.ParseBuf.parse_of_size _ buf () 1#usize hs (by simp [hb])
      (fun o => o.map (·.1) = f x) (by
        intro sub hsub
        simp only [hb] at hsub
        have := misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
          U8.Insts.Mysql_commonMiscRawIntIntReprU8 tf err sub
          (fun (o : Option U8) (_ : io.ParseBuf) => o = some x)
          (by
            apply WP.spec_mono (U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec sub (by simp [hsub]))
            rintro ⟨r, rest⟩ h
            simp only [WP.uncurry', hsub] at h ⊢
            cases r <;> simp_all [okPart]
            rename_i a
            exact UScalar.eq_of_val_eq h.1)
          (fun (p : U8) (o : Option T) => o = f p) hf
        apply WP.spec_mono this
        rintro ⟨r, rest⟩ ⟨o, rfl, h3⟩
        exact h3)
    apply WP.spec_mono h
    rintro ⟨r, rest⟩ ⟨h1, h2⟩
    simp only [hb] at h2
    exact ⟨h1, h2⟩

theorem coltype_try_from (p : U8) :
    constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from p ⦃ r =>
      okPart r = columnTypeOfCode p.val ⦄ := by
  rw [constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from_spec]
  apply (WP.spec_ok _).mpr
  cases columnTypeOfCode p.val <;> rfl

set_option maxRecDepth 100000 in
theorem and128 (p : U8) : (p &&& 128#u8 = p) ↔ (p.val = 0 ∨ p.val = 128) := by
  rw [UScalar.eq_equiv, UScalar.val_and]
  have hp : p.val < 256 := by scalar_tac
  generalize p.val = n at hp ⊢
  have : (128#u8 : U8).val = 128 := rfl
  rw [this]
  revert n
  decide

theorem flags_try_from (p : U8) :
    constants.StmtExecuteParamFlags.Insts.CoreConvertTryFromU8UnknownStmtExecuteParamFlags.try_from p ⦃ r =>
      okPart r = if p.val = 0 ∨ p.val = 128 then some p else none ⦄ := by
  unfold constants.StmtExecuteParamFlags.Insts.CoreConvertTryFromU8UnknownStmtExecuteParamFlags.try_from
    constants.StmtExecuteParamFlags.from_bits constants.StmtExecuteParamFlags.from_bits_truncate
    constants.StmtExecuteParamFlags.all
  simp only [lift, bind_ok]
  have h0 : (0#u8 ||| 128#u8 : U8) = 128#u8 := rfl
  rw [h0]
  by_cases h : p &&& 128#u8 = p
  · have h' := (and128 p).mp h
    simp [h, h', okPart]
  · have h' : ¬ (p.val = 0 ∨ p.val = 128) := fun h'' => h ((and128 p).mpr h'')
    simp [h, h', okPart]

theorem bind_const_new {T U β : Type} (t : T) (f : misc.raw._const.Const T U → Result β) :
    (do let c ← misc.raw._const.Const.new U t; f c) = f (t, ()) := by
  unfold misc.raw._const.Const.new
  exact Std.bind_tc_ok (α := misc.raw._const.Const T U) ((t, ()) : misc.raw._const.Const T U) f

/-- The (type code, flag byte) of a `StmtBulkExecuteParamType` (hides the `Const` projections,
    which are not type-correct at reducible transparency, from `simp`). -/
def ptOf (t : packets.StmtBulkExecuteParamType) : Nat × Nat := (columnTypeCode t.type.1, t.flags.1.val)

@[simp] theorem ptOf_mk (a : misc.raw._const.Const constants.ColumnType U8)
    (b : misc.raw._const.Const constants.StmtExecuteParamFlags U8) :
    ptOf { type := a, flags := b } = (columnTypeCode a.1, b.1.val) := rfl

/-- `from_residual` of an error is that error. -/
@[simp] theorem from_residual_err {α : Type} (e : core.io.error.Error) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual α
      (core.convert.FromSame core.io.error.Error) (.Err e) = ok (.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem columnTypeCode_of_code {n : Nat} {ct : constants.ColumnType}
    (h : columnTypeOfCode n = some ct) : columnTypeCode ct = n := by
  unfold columnTypeOfCode at h
  have := List.find?_some h
  simpa using this

/-- `Const<StmtExecuteParamFlags, u8>::serialize`: appends the flag byte. -/
@[step]
theorem const_paramflags_serialize (x : misc.raw._const.Const constants.StmtExecuteParamFlags U8)
    (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize
      constants.StmtExecuteParamFlags.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U8.Insts.CoreConvertFromStmtExecuteParamFlags)
      U8.Insts.Mysql_commonMiscRawIntIntReprU8 x buf ⦃ b => b.val = buf.val ++ [x.1] ⦄ := by
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ x.1 rfl]
  exact U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec _ _ h

open constants.MariadbBulkIndicator in
/-- The bulk indicator with code `n`. -/
def indOfCode (n : Nat) : Option constants.MariadbBulkIndicator :=
  if n = 0 then some BULK_INDICATOR_NONE
  else if n = 1 then some BULK_INDICATOR_NULL
  else if n = 2 then some BULK_INDICATOR_DEFAULT
  else if n = 3 then some BULK_INDICATOR_IGNORE
  else none

theorem indOfCode_none {n : Nat} : indOfCode n = none ↔ 3 < n := by
  unfold indOfCode; split_ifs <;> simp <;> omega

theorem indOfCode_some {n : Nat} {i : constants.MariadbBulkIndicator} (h : indOfCode n = some i) :
    bulkIndicatorCode i = n := by
  unfold indOfCode at h; split_ifs at h <;> simp at h <;> subst h <;> simp [bulkIndicatorCode] <;> omega

theorem ind_try_from (p : U8) :
    constants.MariadbBulkIndicator.Insts.CoreConvertTryFromU8UnknownMariadbBulkIndicator.try_from p ⦃ r =>
      okPart r = indOfCode p.val ⦄ := by
  unfold constants.MariadbBulkIndicator.Insts.CoreConvertTryFromU8UnknownMariadbBulkIndicator.try_from
  split
  · exact (WP.spec_ok _).mpr rfl
  · exact (WP.spec_ok _).mpr rfl
  · exact (WP.spec_ok _).mpr rfl
  · exact (WP.spec_ok _).mpr rfl
  · rename_i h0 h1 h2 h3
    have h0' : ¬ p.val = 0 := fun h => h0 (UScalar.eq_of_val_eq (h.trans rfl))
    have h1' : ¬ p.val = 1 := fun h => h1 (UScalar.eq_of_val_eq (h.trans rfl))
    have h2' : ¬ p.val = 2 := fun h => h2 (UScalar.eq_of_val_eq (h.trans rfl))
    have h3' : ¬ p.val = 3 := fun h => h3 (UScalar.eq_of_val_eq (h.trans rfl))
    simp only [WP.spec_ok, okPart, indOfCode, h0', h1', h2', h3', ite_false]

theorem ind_eq_null (a : constants.MariadbBulkIndicator) :
    constants.MariadbBulkIndicator.Insts.CoreCmpPartialEqMariadbBulkIndicator.eq a
      constants.MariadbBulkIndicator.BULK_INDICATOR_NULL =
      ok (bulkIndicatorCode a == 1) := by
  cases a <;> rfl

theorem ind_from (i : constants.MariadbBulkIndicator) :
    U8.Insts.CoreConvertFromMariadbBulkIndicator.from i = ok (byte (bulkIndicatorCode i)) := by
  cases i <;> rfl

/-- `Const<MariadbBulkIndicator, u8>::serialize`: appends the indicator code. -/
@[step]
theorem const_ind_serialize (x : misc.raw._const.Const constants.MariadbBulkIndicator U8)
    (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize
      constants.MariadbBulkIndicator.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U8.Insts.CoreConvertFromMariadbBulkIndicator)
      U8.Insts.Mysql_commonMiscRawIntIntReprU8 x buf ⦃ b => b.val = buf.val ++ [byte (bulkIndicatorCode x.1)] ⦄ := by
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ _ (ind_from x.1)]
  exact U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec _ _ h

/-- `ValueDeserializer<BinValue>::deserialize` is `Value::deserialize_bin` (supported types). -/
theorem vd_bin_spec (h64 : Target64) (ct : constants.ColumnType) (flags : constants.ColumnFlags)
    (hs : binSupported ct = true) (buf : io.ParseBuf) :
    value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize
      (ct, flags) buf ⦃ r rest =>
      ((okPart r).map (fun d => Val.ofValue d.1), rest.val) = binRead ct (isUnsigned flags) buf.val ⦄ := by
  unfold value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize
  apply WP.spec_bind (value.Value.deserialize_bin_spec h64 ct flags hs buf)
  rintro ⟨r, rest⟩ h
  cases r with
  | Err e => simp_all [core.result.Result.Insts.CoreOpsTry.branch, okPart]
  | Ok a =>
    simp only [WP.uncurry'_pair] at h
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    rw [← h]
    rfl

/-- `ValueDeserializer<BinValue>::deserialize` panics on an unsupported type. -/
theorem vd_bin_unsupported (ct : constants.ColumnType) (flags : constants.ColumnFlags)
    (hs : binSupported ct = false) (buf : io.ParseBuf) :
    value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize
      (ct, flags) buf = fail .panic := by
  unfold value.ValueDeserializerBinValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize
  rw [value.Value.deserialize_bin_unsupported ct flags hs buf]
  exact Std.bind_tc_fail _ _

end mysql_common.SBParam
