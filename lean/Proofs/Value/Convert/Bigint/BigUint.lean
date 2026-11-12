import Defs

/-! Statements for `impl FromValue for BigUint, impl From<BigUint> for Value` (spec file: `Specs/Value/Convert/Bigint.lean`). Proofs: TODO. -/

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
  sorry

/-- `From<ParseIr<BigUint>>` for `BigUint` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrBigUint.from_eq (x : num_bigint_1.biguint.BigUint) (w : value.Value) :
    num_bigint_1.biguint.BigUint.Insts.CoreConvertFromParseIrBigUint.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrBigUint.from (x, w) = ok w := by
  sorry

/-- `From<BigUint> for Value`: `UInt` if it fits in a `u64`, else `Bytes` of its decimal text. -/
theorem value.Value.Insts.CoreConvertFromBigUint.from_spec (x : num_bigint_1.biguint.BigUint) (h : (utf8 (Trusted.biguintToString x)).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromBigUint.from x ⦃ w =>
      Val.ofValue w = match Trusted.biguintToU64 x with
        | some u => .uint u.val
        | none => .bytes (utf8 (Trusted.biguintToString x)) ⦄ := by
  sorry

end mysql_common
