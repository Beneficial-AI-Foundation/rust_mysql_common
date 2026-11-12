import Defs

/-! Statements for `impl FromValue for BigDecimal, impl From<BigDecimal> for Value` (spec file: `Specs/Value/Convert/Bigdecimal.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<BigDecimal>`: `Int`/`UInt` are converted, `Float`/`Double`
    converted when the opaque `TryFrom` succeeds (not for NaN/infinities), `Bytes` parsed
    (opaque); anything else is an error carrying the value. -/
theorem value.convert.ParseIrBigDecimal.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrBigDecimal.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Int x => .Ok (Trusted.bigdecimalFromI64 x, v)
      | .UInt x => .Ok (Trusted.bigdecimalFromU64 x, v)
      | .Float x =>
        match Trusted.bigdecimalTryFromF32 x with
        | some y => .Ok (y, v)
        | none => .Err v
      | .Double x =>
        match Trusted.bigdecimalTryFromF64 x with
        | some y => .Ok (y, v)
        | none => .Err v
      | .Bytes b =>
        match Trusted.bigdecimalParseBytes (alloc.vec.Vec.deref b) with
        | some x => .Ok (x, v)
        | none => .Err v
      | _ => .Err v) := by
  sorry

/-- `From<ParseIr<BigDecimal>>` for `BigDecimal` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrBigDecimal.from_eq (x : bigdecimal.BigDecimal) (w : value.Value) :
    bigdecimal.BigDecimal.Insts.CoreConvertFromParseIrBigDecimal.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrBigDecimal.from (x, w) = ok w := by
  sorry

/-- `From<BigDecimal> for Value`: `Bytes` of its text (`to_string`, opaque). -/
theorem value.Value.Insts.CoreConvertFromBigDecimal.from_spec (x : bigdecimal.BigDecimal) (h : (utf8 (Trusted.bigdecimalToString x)).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromBigDecimal.from x ⦃ w =>
      Val.ofValue w = .bytes (utf8 (Trusted.bigdecimalToString x)) ⦄ := by
  sorry

end mysql_common
