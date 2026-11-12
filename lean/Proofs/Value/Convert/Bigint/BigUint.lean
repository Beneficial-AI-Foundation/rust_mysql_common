import Defs
import Proofs.Util.ConvDeps

/-! Statements for `impl FromValue for BigUint, impl From<BigUint> for Value` (spec file: `Specs/Value/Convert/Bigint.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<BigUint>`: `Int` (if non-negative, per the opaque `from_i64`) and
    `UInt` are converted, `Bytes` parsed (opaque); anything else is an error carrying the value. -/
theorem value.convert.ParseIrBigUint.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrBigUint.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Int x =>
        match Trusted.biguintFromI64 x with
        | some y => .Ok (y, v)
        | none => .Err v
      | .UInt x => .Ok (Trusted.biguintFromU64 x, v)
      | .Bytes b =>
        match Trusted.biguintParseBytes (alloc.vec.Vec.deref b) with
        | some x => .Ok (x, v)
        | none => .Err v
      | _ => .Err v) := by
  cases v <;> simp [value.convert.ParseIrBigUint.Insts.CoreConvertTryFromValueFromValueError.try_from,
    value.convert.trusted.biguint_from_i64, value.convert.trusted.biguint_from_u64,
    value.convert.trusted.biguint_parse_bytes] <;> split <;> simp_all

/-- `From<ParseIr<BigUint>>` for `BigUint` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrBigUint.from_eq (x : num_bigint_1.biguint.BigUint) (w : value.Value) :
    num_bigint_1.biguint.BigUint.Insts.CoreConvertFromParseIrBigUint.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrBigUint.from (x, w) = ok w := by
  exact ⟨rfl, rfl⟩

/-- `From<BigUint> for Value`: `UInt` if it fits in a `u64`, else `Bytes` of its decimal text. -/
theorem value.Value.Insts.CoreConvertFromBigUint.from_spec (x : num_bigint_1.biguint.BigUint) (h : Trusted.biguintToU64 x = none → (utf8 (Trusted.biguintToString x)).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromBigUint.from x ⦃ w =>
      Val.ofValue w = match Trusted.biguintToU64 x with
        | some u => .uint u.val
        | none => .bytes (utf8 (Trusted.biguintToString x)) ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromBigUint.from, value.convert.trusted.biguint_to_u64,
    value.convert.trusted.biguint_to_string]
  rcases hu : Trusted.biguintToU64 x with _ | u
  · obtain ⟨b, hb, hv⟩ := ConvDeps.string_into_bytes_val _ (h hu)
    simp [hb, Val.ofValue, hv]
  · simp [Val.ofValue]

/-- `from_value_opt`: as `try_from_eq` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem num_bigint_1.biguint.BigUint.Insts.Mysql_commonValueConvertFromValueParseIrBigUint.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt num_bigint_1.biguint.BigUint.Insts.Mysql_commonValueConvertFromValueParseIrBigUint v = ok (match v with
      | .Int x =>
        match Trusted.biguintFromI64 x with
        | some y => .Ok y
        | none => .Err v
      | .UInt x => .Ok (Trusted.biguintFromU64 x)
      | .Bytes b =>
        match Trusted.biguintParseBytes (alloc.vec.Vec.deref b) with
        | some x => .Ok x
        | none => .Err v
      | _ => .Err v) := by
  simp only [value.convert.from_value_opt,
    value.convert.ParseIrBigUint.Insts.CoreConvertTryFromValueFromValueError.try_from_eq]
  cases v <;> simp [num_bigint_1.biguint.BigUint.Insts.CoreConvertFromParseIrBigUint.from,
    value.convert.ParseIr.commit, core.convert.IntoFrom.into]
  case Int x => cases Trusted.biguintFromI64 x <;> simp
  case Bytes b => cases Trusted.biguintParseBytes (alloc.vec.Vec.deref b) <;> simp

end mysql_common
