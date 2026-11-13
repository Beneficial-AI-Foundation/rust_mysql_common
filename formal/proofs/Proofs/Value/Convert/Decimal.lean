import Defs
import Proofs.Util.ConvDeps

/-! Statements for `impl FromValue for Decimal, impl From<Decimal> for Value` (spec file: `Specs/Value/Convert/Decimal.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<Decimal>`: `Int`/`UInt` are converted, valid UTF-8 `Bytes`
    parsed by `Decimal::from_str` (opaque); anything else is an error carrying the value. -/
theorem value.convert.ParseIrDecimal.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrDecimal.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Int x => .Ok (Trusted.decimalFromI64 x, v)
      | .UInt x => .Ok (Trusted.decimalFromU64 x, v)
      | .Bytes b =>
        if IsUtf8 b.val then
          match Trusted.decimalFromStr (alloc.vec.Vec.deref b) with
          | some x => .Ok (x, v)
          | none => .Err v
        else .Err v
      | _ => .Err v) := by
  cases v <;> simp [value.convert.ParseIrDecimal.Insts.CoreConvertTryFromValueFromValueError.try_from,
    ConvDeps.str_from_utf8_eq, value.convert.trusted.decimal_from_i64, value.convert.trusted.decimal_from_u64,
    value.convert.trusted.decimal_from_str]
  case Bytes b =>
    by_cases h : IsUtf8 b.val
    · simp only [h, ite_true]
      cases Trusted.decimalFromStr (alloc.vec.Vec.deref b) <;> simp
    · simp [h]

/-- `From<ParseIr<Decimal>>` for `Decimal` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrDecimal.from_eq (x : rust_decimal.decimal.Decimal) (w : value.Value) :
    rust_decimal.decimal.Decimal.Insts.CoreConvertFromParseIrDecimal.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrDecimal.from (x, w) = ok w := by
  exact ⟨rfl, rfl⟩

/-- `From<Decimal> for Value`: `Bytes` of its text (`to_string`, opaque). -/
theorem value.Value.Insts.CoreConvertFromDecimal.from_spec (x : rust_decimal.decimal.Decimal) (h : (utf8 (Trusted.decimalToString x)).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromDecimal.from x ⦃ w =>
      Val.ofValue w = .bytes (utf8 (Trusted.decimalToString x)) ⦄ := by
  obtain ⟨b, hb, hv⟩ := ConvDeps.string_into_bytes_val _ h
  simp [value.Value.Insts.CoreConvertFromDecimal.from, value.convert.trusted.decimal_to_string,
    hb, Val.ofValue, hv]

/-- `from_value_opt`: as `try_from_eq` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem rust_decimal.decimal.Decimal.Insts.Mysql_commonValueConvertFromValueParseIrDecimal.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt rust_decimal.decimal.Decimal.Insts.Mysql_commonValueConvertFromValueParseIrDecimal v = ok (match v with
      | .Int x => .Ok (Trusted.decimalFromI64 x)
      | .UInt x => .Ok (Trusted.decimalFromU64 x)
      | .Bytes b =>
        if IsUtf8 b.val then
          match Trusted.decimalFromStr (alloc.vec.Vec.deref b) with
          | some x => .Ok x
          | none => .Err v
        else .Err v
      | _ => .Err v) := by
  simp only [value.convert.from_value_opt,
    value.convert.ParseIrDecimal.Insts.CoreConvertTryFromValueFromValueError.try_from_eq]
  cases v <;> simp [rust_decimal.decimal.Decimal.Insts.CoreConvertFromParseIrDecimal.from,
    value.convert.ParseIr.commit, core.convert.IntoFrom.into]
  case Bytes b =>
    by_cases h : IsUtf8 b.val
    · simp only [h, ite_true]
      cases Trusted.decimalFromStr (alloc.vec.Vec.deref b) <;> simp
    · simp [h]

end mysql_common
