import Defs
import Proofs.Util.ConvDeps

/-! Statements for `impl FromValue for BigDecimal, impl From<BigDecimal> for Value` (spec file: `Specs/Value/Convert/Bigdecimal.lean`). -/

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
  cases v <;> simp [value.convert.ParseIrBigDecimal.Insts.CoreConvertTryFromValueFromValueError.try_from,
    value.convert.trusted.bigdecimal_from_i64, value.convert.trusted.bigdecimal_from_u64,
    value.convert.trusted.bigdecimal_try_from_f32, value.convert.trusted.bigdecimal_try_from_f64,
    value.convert.trusted.bigdecimal_parse_bytes] <;> split <;> simp_all

/-- `From<ParseIr<BigDecimal>>` for `BigDecimal` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrBigDecimal.from_eq (x : bigdecimal.BigDecimal) (w : value.Value) :
    bigdecimal.BigDecimal.Insts.CoreConvertFromParseIrBigDecimal.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrBigDecimal.from (x, w) = ok w := by
  exact ⟨rfl, rfl⟩

/-- `From<BigDecimal> for Value`: `Bytes` of its text (`to_string`, opaque). -/
theorem value.Value.Insts.CoreConvertFromBigDecimal.from_spec (x : bigdecimal.BigDecimal) (h : (utf8 (Trusted.bigdecimalToString x)).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromBigDecimal.from x ⦃ w =>
      Val.ofValue w = .bytes (utf8 (Trusted.bigdecimalToString x)) ⦄ := by
  obtain ⟨b, hb, hv⟩ := ConvDeps.string_into_bytes_val _ h
  simp [value.Value.Insts.CoreConvertFromBigDecimal.from, value.convert.trusted.bigdecimal_to_string,
    hb, Val.ofValue, hv]

/-- `from_value_opt`: as `try_from_eq` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem bigdecimal.BigDecimal.Insts.Mysql_commonValueConvertFromValueParseIrBigDecimal.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt bigdecimal.BigDecimal.Insts.Mysql_commonValueConvertFromValueParseIrBigDecimal v = ok (match v with
      | .Int x => .Ok (Trusted.bigdecimalFromI64 x)
      | .UInt x => .Ok (Trusted.bigdecimalFromU64 x)
      | .Float x =>
        match Trusted.bigdecimalTryFromF32 x with
        | some y => .Ok y
        | none => .Err v
      | .Double x =>
        match Trusted.bigdecimalTryFromF64 x with
        | some y => .Ok y
        | none => .Err v
      | .Bytes b =>
        match Trusted.bigdecimalParseBytes (alloc.vec.Vec.deref b) with
        | some x => .Ok x
        | none => .Err v
      | _ => .Err v) := by
  simp only [value.convert.from_value_opt,
    value.convert.ParseIrBigDecimal.Insts.CoreConvertTryFromValueFromValueError.try_from_eq]
  cases v <;> simp [bigdecimal.BigDecimal.Insts.CoreConvertFromParseIrBigDecimal.from,
    value.convert.ParseIr.commit, core.convert.IntoFrom.into]
  case Float x => cases Trusted.bigdecimalTryFromF32 x <;> simp
  case Double x => cases Trusted.bigdecimalTryFromF64 x <;> simp
  case Bytes b => cases Trusted.bigdecimalParseBytes (alloc.vec.Vec.deref b) <;> simp

end mysql_common
