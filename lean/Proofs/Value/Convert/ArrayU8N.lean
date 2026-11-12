import Defs
import Proofs.Util.ConvBytesTime

/-! Statements for `impl FromValue for [u8; N]` (spec file: `Specs/Value/Convert.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for [u8; N]`: total; succeeds exactly on `Bytes` of length `N`. -/
theorem ArrayU8N.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (N : Usize) (v : value.Value) :
    ArrayU8N.Insts.CoreConvertTryFromValueFromValueError.try_from N v ⦃ r =>
      (∀ a : Array U8 N, r = .Ok a ↔ Val.ofValue v = .bytes a.val) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    simp only [ArrayU8N.Insts.CoreConvertTryFromValueFromValueError.try_from,
      Array.Insts.CoreConvertTryFromVecVec.try_from]
    by_cases h : b.val.length = N.val
    · simp only [h, _root_.dite_true]
      simp [core.result.Result.map_err, Val.ofValue, okPart]
      intro a
      rw [Array.eq_iff, Array.from_val]
    · simp only [h, _root_.dite_false]
      simp [core.result.Result.map_err, Val.ofValue, okPart,
        value.convert.TryFromArrayU8NValueFromValueError.try_from.closure.Insts.CoreOpsFunctionFnOnceTupleVecU8FromValueError.call_once]
      intro a e
      apply h; rw [e]; exact a.property
  | _ => simp [ArrayU8N.Insts.CoreConvertTryFromValueFromValueError.try_from, Val.ofValue, okPart]

/-- `from_value_opt::<[u8; N]>`: as `try_from`. -/
theorem ArrayU8N.Insts.Mysql_commonValueConvertFromValueArrayU8N.from_value_opt_spec (N : Usize) (v : value.Value) :
    value.convert.from_value_opt (ArrayU8N.Insts.Mysql_commonValueConvertFromValueArrayU8N N) v ⦃ r =>
      (∀ a : Array U8 N, r = .Ok a ↔ Val.ofValue v = .bytes a.val) ∧ (okPart r = none → r = .Err v) ⦄ := by
  simp only [value.convert.from_value_opt]
  exact mysql_common.CBTUtil.from_value_opt_same_spec _ _
    (ArrayU8N.Insts.CoreConvertTryFromValueFromValueError.try_from_spec N v)

end mysql_common
