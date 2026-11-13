import Defs
import Proofs.Util.ConvBytesTime

/-! Statements for `impl FromValue for String` (spec file: `Specs/Value/Convert.lean`). Helper lemmas: `Proofs/Util/ConvBytesTime.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for String`: total; succeeds exactly on `Bytes` that are valid UTF-8, with
    the string they encode; on failure the original value (the bytes) is returned. -/
theorem alloc.string.String.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    alloc.string.String.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (∀ s, r = .Ok s ↔ Val.ofValue v = .bytes (utf8 s)) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    simp only [alloc.string.String.Insts.CoreConvertTryFromValueFromValueError.try_from,
      value.convert.trusted.string_from_utf8]
    cases h : String.fromUTF8? (Trusted.bytesOf b.val) with
    | none =>
      have := mysql_common.CBTUtil.fromUTF8?_bytesOf_none h
      simp only [Val.ofValue, okPart]
      simp only [bind_ok, Val.bytes.injEq, WP.spec_ok, reduceCtorEq, false_iff, imp_self, and_true]
      exact fun s e => this s e.symm
    | some t =>
      have := mysql_common.CBTUtil.fromUTF8?_bytesOf_some h
      simp only [Val.ofValue, okPart]
      simp only [bind_ok, Val.bytes.injEq, WP.spec_ok, core.result.Result.Ok.injEq, reduceCtorEq,
        imp_self, and_true]
      intro s
      constructor
      · rintro rfl; exact this.symm
      · intro e; exact mysql_common.CBTUtil.utf8_inj (this.trans e)
  | _ =>
    simp [alloc.string.String.Insts.CoreConvertTryFromValueFromValueError.try_from, Val.ofValue,
      okPart]

/-- `from_value_opt::<String>`: as `try_from`. -/
theorem alloc.string.String.Insts.Mysql_commonValueConvertFromValueString.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt alloc.string.String.Insts.Mysql_commonValueConvertFromValueString v ⦃ r =>
      (∀ s, r = .Ok s ↔ Val.ofValue v = .bytes (utf8 s)) ∧ (okPart r = none → r = .Err v) ⦄ := by
  have h := alloc.string.String.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v
  simp only [value.convert.from_value_opt]
  exact mysql_common.CBTUtil.from_value_opt_same_spec _ _ h

end mysql_common
