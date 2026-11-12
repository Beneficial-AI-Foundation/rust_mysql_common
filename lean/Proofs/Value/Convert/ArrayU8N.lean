import Defs

/-! Statements for `impl FromValue for [u8; N]` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for [u8; N]`: total; succeeds exactly on `Bytes` of length `N`. -/
theorem ArrayU8N.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (N : Usize) (v : value.Value) :
    ArrayU8N.Insts.CoreConvertTryFromValueFromValueError.try_from N v ⦃ r =>
      (∀ a : Array U8 N, r = .Ok a ↔ Val.ofValue v = .bytes a.val) ∧ (okPart r = none → r = .Err v) ⦄ := by
  sorry

/-- `from_value_opt::<[u8; N]>`: as `try_from`. -/
theorem ArrayU8N.Insts.Mysql_commonValueConvertFromValueArrayU8N.from_value_opt_spec (N : Usize) (v : value.Value) :
    value.convert.from_value_opt (ArrayU8N.Insts.Mysql_commonValueConvertFromValueArrayU8N N) v ⦃ r =>
      (∀ a : Array U8 N, r = .Ok a ↔ Val.ofValue v = .bytes a.val) ∧ (okPart r = none → r = .Err v) ⦄ := by
  sorry

end mysql_common
