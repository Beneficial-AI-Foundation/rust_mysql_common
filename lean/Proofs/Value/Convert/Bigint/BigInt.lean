import Defs

/-! Statements for `impl FromValue for BigInt, impl From<BigInt> for Value` (spec file: `Specs/Value/Convert/Bigint.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<BigInt>`: `Int`/`UInt` are converted, `Bytes` parsed (decimal,
    opaque); anything else is an error carrying the value. The original value is kept. -/
theorem value.convert.ParseIrBigInt.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrBigInt.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Int x => .Ok (Trusted.bigintFromI64 x, v)
      | .UInt x => .Ok (Trusted.bigintFromU64 x, v)
      | .Bytes b =>
        match Trusted.bigintParseBytes (alloc.vec.Vec.deref b) with
        | some x => .Ok (x, v)
        | none => .Err v
      | _ => .Err v) := by
  sorry

/-- `From<ParseIr<BigInt>>` for `BigInt` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrBigInt.from_eq (x : num_bigint_1.bigint.BigInt) (w : value.Value) :
    num_bigint_1.bigint.BigInt.Insts.CoreConvertFromParseIrBigInt.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrBigInt.from (x, w) = ok w := by
  sorry

/-- `From<BigInt> for Value`: `Int` if it fits in an `i64`, else `UInt` if it fits in a `u64`, else
    `Bytes` of its decimal text (all three tests opaque). -/
theorem value.Value.Insts.CoreConvertFromBigInt.from_spec (x : num_bigint_1.bigint.BigInt) (h : (utf8 (Trusted.bigintToString x)).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromBigInt.from x ⦃ w =>
      Val.ofValue w = match Trusted.bigintToI64 x, Trusted.bigintToU64 x with
        | some i, _ => .int i.val
        | none, some u => .uint u.val
        | none, none => .bytes (utf8 (Trusted.bigintToString x)) ⦄ := by
  sorry

end mysql_common
