import Defs

/-! Statements for `impl TryFrom<Value> for ParseIr<Date>` (spec file: `Specs/Value/Convert/Time.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<Date>` on a `Date`: total; only the date fields are read;
    converts exactly when time accepts them. -/
theorem value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_date (y : U16) (mo d h mi s : U8) (us : U32) :
    value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from (.Date y mo d h mi s us) ⦃ r =>
      (okPart r = none → r = .Err (.Date y mo d h mi s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeDateValid y.val mo.val d.val) ∧
      ∀ x w, r = .Ok (x, w) → w = .Date y mo d h mi s us ∧ timeDate x = ((y.val : ℤ), mo.val, d.val) ⦄ := by
  sorry

/-- `TryFrom<Value> for ParseIr<Date>` on `Bytes`: time's date parser (opaque) on valid UTF-8. -/
theorem value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes (b : alloc.vec.Vec U8) :
    value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (
      if IsUtf8 b.val then
        match Trusted.dateParseDate (alloc.vec.Vec.deref b) with
        | some x => .Ok (x, .Bytes b)
        | none => .Err (.Bytes b)
      else .Err (.Bytes b)) := by
  sorry

/-- `TryFrom<Value> for ParseIr<Date>`: any other value is an error. -/
theorem value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from_other (v : value.Value) (hv : ∀ y mo d h mi s us, v ≠ .Date y mo d h mi s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.ParseIrDate.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v) := by
  sorry

/-- `from_value_opt`: as `try_from_date` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate.from_value_opt_date (y : U16) (mo d h mi s : U8) (us : U32) :
    value.convert.from_value_opt time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate (.Date y mo d h mi s us) ⦃ r =>
      (okPart r = none → r = .Err (.Date y mo d h mi s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeDateValid y.val mo.val d.val) ∧
      ∀ x, r = .Ok x → timeDate x = ((y.val : ℤ), mo.val, d.val) ⦄ := by
  sorry

/-- `from_value_opt`: as `try_from_bytes` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate.from_value_opt_bytes (b : alloc.vec.Vec U8) :
    value.convert.from_value_opt time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate (.Bytes b) = ok (
      if IsUtf8 b.val then
        match Trusted.dateParseDate (alloc.vec.Vec.deref b) with
        | some x => .Ok x
        | none => .Err (.Bytes b)
      else .Err (.Bytes b)) := by
  sorry

/-- `from_value_opt`: as `try_from_other` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate.from_value_opt_other (v : value.Value) (hv : ∀ y mo d h mi s us, v ≠ .Date y mo d h mi s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.from_value_opt time.date.Date.Insts.Mysql_commonValueConvertFromValueParseIrDate v = ok (.Err v) := by
  sorry

end mysql_common
