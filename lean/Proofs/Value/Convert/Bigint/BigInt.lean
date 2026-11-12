import Defs
import Proofs.Util.ConvDeps

/-! Statements for `impl FromValue for BigInt, impl From<BigInt> for Value` (spec file: `Specs/Value/Convert/Bigint.lean`). -/

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
  cases v <;> simp [value.convert.ParseIrBigInt.Insts.CoreConvertTryFromValueFromValueError.try_from,
    value.convert.trusted.bigint_from_i64, value.convert.trusted.bigint_from_u64,
    value.convert.trusted.bigint_parse_bytes]
  split <;> simp_all

/-- `From<ParseIr<BigInt>>` for `BigInt` is `commit`, for `Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrBigInt.from_eq (x : num_bigint_1.bigint.BigInt) (w : value.Value) :
    num_bigint_1.bigint.BigInt.Insts.CoreConvertFromParseIrBigInt.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrBigInt.from (x, w) = ok w := by
  exact ⟨rfl, rfl⟩

/-- `From<BigInt> for Value`: `Int` if it fits in an `i64`, else `UInt` if it fits in a `u64`, else
    `Bytes` of its decimal text (all three tests opaque). -/
theorem value.Value.Insts.CoreConvertFromBigInt.from_spec (x : num_bigint_1.bigint.BigInt) (h : Trusted.bigintToI64 x = none → Trusted.bigintToU64 x = none →
      (utf8 (Trusted.bigintToString x)).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromBigInt.from x ⦃ w =>
      Val.ofValue w = match Trusted.bigintToI64 x, Trusted.bigintToU64 x with
        | some i, _ => .int i.val
        | none, some u => .uint u.val
        | none, none => .bytes (utf8 (Trusted.bigintToString x)) ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromBigInt.from, value.convert.trusted.bigint_to_i64,
    value.convert.trusted.bigint_to_u64, value.convert.trusted.bigint_to_string]
  rcases hi : Trusted.bigintToI64 x with _ | i
  · rcases hu : Trusted.bigintToU64 x with _ | u
    · obtain ⟨b, hb, hv⟩ := ConvDeps.string_into_bytes_val _ (h hi hu)
      simp [hb, Val.ofValue, hv]
    · simp [Val.ofValue]
  · simp [Val.ofValue]

/-- `from_value_opt`: as `try_from_eq` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
theorem num_bigint_1.bigint.BigInt.Insts.Mysql_commonValueConvertFromValueParseIrBigInt.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt num_bigint_1.bigint.BigInt.Insts.Mysql_commonValueConvertFromValueParseIrBigInt v = ok (match v with
      | .Int x => .Ok (Trusted.bigintFromI64 x)
      | .UInt x => .Ok (Trusted.bigintFromU64 x)
      | .Bytes b =>
        match Trusted.bigintParseBytes (alloc.vec.Vec.deref b) with
        | some x => .Ok x
        | none => .Err v
      | _ => .Err v) := by
  simp only [value.convert.from_value_opt,
    value.convert.ParseIrBigInt.Insts.CoreConvertTryFromValueFromValueError.try_from_eq]
  cases v <;> simp [num_bigint_1.bigint.BigInt.Insts.CoreConvertFromParseIrBigInt.from,
    value.convert.ParseIr.commit, core.convert.IntoFrom.into]
  case Bytes b => cases Trusted.bigintParseBytes (alloc.vec.Vec.deref b) <;> simp

end mysql_common
