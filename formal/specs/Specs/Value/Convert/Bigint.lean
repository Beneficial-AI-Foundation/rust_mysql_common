import Proofs.Value.Convert.Bigint.BigInt
import Proofs.Value.Convert.Bigint.BigUint

/-!
# `src/value/convert/bigint.rs`
    `FromValue` and `From<_> for Value` for num-bigint's `BigInt` and `BigUint`. The numbers are
    opaque, as are their constructors, parsers, `to_i64`/`to_u64` and `to_string`: the statements
    are glue-level, exact in terms of those opaque functions (which are assumed not to panic).

    **Configuration.** As in `Specs/Io.lean` (num-bigint 0.5.1).

    **Definitions used.** `Defs/Convert.lean` (`utf8`), `Defs/Value.lean`.

    **Trusted axioms these statements rest on** (`FunsExternal.lean`, namespace `Trusted`):
    `bigintFromI64`, `bigintFromU64`, `bigintParseBytes`, `bigintToI64`, `bigintToU64`,
    `bigintToString`, `biguintFromI64`, `biguintFromU64`, `biguintParseBytes`, `biguintToU64`,
    `biguintToString`.

    **Not covered.** That the parse and the conversions mean what their names say (opaque).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-! ### `impl FromValue for BigInt, impl From<BigInt> for Value` -/

/-- `TryFrom<Value> for ParseIr<BigInt>`: `Int`/`UInt` are converted, `Bytes` parsed (decimal,
    opaque); anything else is an error carrying the value. The original value is kept. -/
recall value.convert.ParseIrBigInt.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrBigInt.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Int x => .Ok (Trusted.bigintFromI64 x, v)
      | .UInt x => .Ok (Trusted.bigintFromU64 x, v)
      | .Bytes b =>
        match Trusted.bigintParseBytes (alloc.vec.Vec.deref b) with
        | some x => .Ok (x, v)
        | none => .Err v
      | _ => .Err v)

/-- [propext, choice, Quot.sound, Trusted.bigintFromI64, Trusted.bigintFromU64, Trusted.bigintParseBytes, num_bigint_1.bigint.BigInt] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrBigInt.Insts.CoreConvertTryFromValueFromValueError.try_from_eq
/-- `From<ParseIr<BigInt>>` for `BigInt` is `commit`, for `Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrBigInt.from_eq (x : num_bigint_1.bigint.BigInt) (w : value.Value) :
    num_bigint_1.bigint.BigInt.Insts.CoreConvertFromParseIrBigInt.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrBigInt.from (x, w) = ok w

/-- [propext, Quot.sound, num_bigint_1.bigint.BigInt] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrBigInt.from_eq
/-- `From<BigInt> for Value`: `Int` if it fits in an `i64`, else `UInt` if it fits in a `u64`, else
    `Bytes` of its decimal text (all three tests opaque). -/
recall value.Value.Insts.CoreConvertFromBigInt.from_spec (x : num_bigint_1.bigint.BigInt) (h : Trusted.bigintToI64 x = none → Trusted.bigintToU64 x = none →
      (utf8 (Trusted.bigintToString x)).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromBigInt.from x ⦃ w =>
      Val.ofValue w = match Trusted.bigintToI64 x, Trusted.bigintToU64 x with
        | some i, _ => .int i.val
        | none, some u => .uint u.val
        | none, none => .bytes (utf8 (Trusted.bigintToString x)) ⦄

/-- [propext, choice, Quot.sound, Trusted.bigintToI64, Trusted.bigintToString, Trusted.bigintToU64, num_bigint_1.bigint.BigInt] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromBigInt.from_spec
/-- `from_value_opt`: as `try_from_eq` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall num_bigint_1.bigint.BigInt.Insts.Mysql_commonValueConvertFromValueParseIrBigInt.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt num_bigint_1.bigint.BigInt.Insts.Mysql_commonValueConvertFromValueParseIrBigInt v = ok (match v with
      | .Int x => .Ok (Trusted.bigintFromI64 x)
      | .UInt x => .Ok (Trusted.bigintFromU64 x)
      | .Bytes b =>
        match Trusted.bigintParseBytes (alloc.vec.Vec.deref b) with
        | some x => .Ok x
        | none => .Err v
      | _ => .Err v)

/-- [propext, choice, Quot.sound, Trusted.bigintFromI64, Trusted.bigintFromU64, Trusted.bigintParseBytes, num_bigint_1.bigint.BigInt] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms num_bigint_1.bigint.BigInt.Insts.Mysql_commonValueConvertFromValueParseIrBigInt.from_value_opt_eq
/-! ### `impl FromValue for BigUint, impl From<BigUint> for Value` -/

/-- `TryFrom<Value> for ParseIr<BigUint>`: `Int` (if non-negative, per the opaque `from_i64`) and
    `UInt` are converted, `Bytes` parsed (opaque); anything else is an error carrying the value. -/
recall value.convert.ParseIrBigUint.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
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
      | _ => .Err v)

/-- [propext, choice, Quot.sound, Trusted.biguintFromI64, Trusted.biguintFromU64, Trusted.biguintParseBytes, num_bigint_1.biguint.BigUint] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrBigUint.Insts.CoreConvertTryFromValueFromValueError.try_from_eq
/-- `From<ParseIr<BigUint>>` for `BigUint` is `commit`, for `Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrBigUint.from_eq (x : num_bigint_1.biguint.BigUint) (w : value.Value) :
    num_bigint_1.biguint.BigUint.Insts.CoreConvertFromParseIrBigUint.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrBigUint.from (x, w) = ok w

/-- [propext, Quot.sound, num_bigint_1.biguint.BigUint] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrBigUint.from_eq
/-- `From<BigUint> for Value`: `UInt` if it fits in a `u64`, else `Bytes` of its decimal text. -/
recall value.Value.Insts.CoreConvertFromBigUint.from_spec (x : num_bigint_1.biguint.BigUint) (h : Trusted.biguintToU64 x = none → (utf8 (Trusted.biguintToString x)).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromBigUint.from x ⦃ w =>
      Val.ofValue w = match Trusted.biguintToU64 x with
        | some u => .uint u.val
        | none => .bytes (utf8 (Trusted.biguintToString x)) ⦄

/-- [propext, choice, Quot.sound, Trusted.biguintToString, Trusted.biguintToU64, num_bigint_1.biguint.BigUint] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromBigUint.from_spec
/-- `from_value_opt`: as `try_from_eq` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall num_bigint_1.biguint.BigUint.Insts.Mysql_commonValueConvertFromValueParseIrBigUint.from_value_opt_eq (v : value.Value) :
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
      | _ => .Err v)

/-- [propext, choice, Quot.sound, Trusted.biguintFromI64, Trusted.biguintFromU64, Trusted.biguintParseBytes, num_bigint_1.biguint.BigUint] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms num_bigint_1.biguint.BigUint.Insts.Mysql_commonValueConvertFromValueParseIrBigUint.from_value_opt_eq
end mysql_common
