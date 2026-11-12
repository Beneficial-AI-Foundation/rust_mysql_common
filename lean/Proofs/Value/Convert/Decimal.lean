import Defs

/-! Statements for `impl FromValue for Decimal, impl From<Decimal> for Value` (spec file: `Specs/Value/Convert/Decimal.lean`). Proofs: TODO. -/

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
  sorry

/-- `From<ParseIr<Decimal>>` for `Decimal` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrDecimal.from_eq (x : rust_decimal.decimal.Decimal) (w : value.Value) :
    rust_decimal.decimal.Decimal.Insts.CoreConvertFromParseIrDecimal.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrDecimal.from (x, w) = ok w := by
  sorry

/-- `From<Decimal> for Value`: `Bytes` of its text (`to_string`, opaque). -/
theorem value.Value.Insts.CoreConvertFromDecimal.from_spec (x : rust_decimal.decimal.Decimal) (h : (utf8 (Trusted.decimalToString x)).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromDecimal.from x ⦃ w =>
      Val.ofValue w = .bytes (utf8 (Trusted.decimalToString x)) ⦄ := by
  sorry

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
  sorry

end mysql_common
