import Proofs.Value.Convert.Decimal

/-!
# `src/value/convert/decimal.rs`
    `FromValue` and `From<_> for Value` for rust_decimal's `Decimal`. Opaque, glue-level, as for
    `Specs/Value/Convert/Bigint.lean`.

    **Configuration.** As in `Specs/Io.lean` (feature `rust_decimal`, rust_decimal 1.43.0).

    **Definitions used.** `Defs/Convert.lean` (`utf8`, `IsUtf8`), `Defs/Value.lean`.

    **Trusted axioms these statements rest on:** `Trusted.decimalFromI64`, `decimalFromU64`,
    `decimalFromStr`, `decimalToString`.

    **Behaviour to note.** `Float`/`Double` are not converted to `Decimal` (an error), unlike
    `BigDecimal`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-! ### `impl FromValue for Decimal, impl From<Decimal> for Value` -/

/-- `TryFrom<Value> for ParseIr<Decimal>`: `Int`/`UInt` are converted, valid UTF-8 `Bytes`
    parsed by `Decimal::from_str` (opaque); anything else is an error carrying the value. -/
recall value.convert.ParseIrDecimal.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrDecimal.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Int x => .Ok (Trusted.decimalFromI64 x, v)
      | .UInt x => .Ok (Trusted.decimalFromU64 x, v)
      | .Bytes b =>
        if IsUtf8 b.val then
          match Trusted.decimalFromStr (alloc.vec.Vec.deref b) with
          | some x => .Ok (x, v)
          | none => .Err v
        else .Err v
      | _ => .Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrDecimal.Insts.CoreConvertTryFromValueFromValueError.try_from_eq`

/-- `From<ParseIr<Decimal>>` for `Decimal` is `commit`, for `Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrDecimal.from_eq (x : rust_decimal.decimal.Decimal) (w : value.Value) :
    rust_decimal.decimal.Decimal.Insts.CoreConvertFromParseIrDecimal.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrDecimal.from (x, w) = ok w

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrDecimal.from_eq`

/-- `From<Decimal> for Value`: `Bytes` of its text (`to_string`, opaque). -/
recall value.Value.Insts.CoreConvertFromDecimal.from_spec (x : rust_decimal.decimal.Decimal) (h : (utf8 (Trusted.decimalToString x)).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromDecimal.from x ⦃ w =>
      Val.ofValue w = .bytes (utf8 (Trusted.decimalToString x)) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromDecimal.from_spec`

/-- `from_value_opt`: as `try_from_eq` of the intermediate, committed (the converted value in place of the `ParseIr` pair). -/
recall rust_decimal.decimal.Decimal.Insts.Mysql_commonValueConvertFromValueParseIrDecimal.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt rust_decimal.decimal.Decimal.Insts.Mysql_commonValueConvertFromValueParseIrDecimal v = ok (match v with
      | .Int x => .Ok (Trusted.decimalFromI64 x)
      | .UInt x => .Ok (Trusted.decimalFromU64 x)
      | .Bytes b =>
        if IsUtf8 b.val then
          match Trusted.decimalFromStr (alloc.vec.Vec.deref b) with
          | some x => .Ok x
          | none => .Err v
        else .Err v
      | _ => .Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms rust_decimal.decimal.Decimal.Insts.Mysql_commonValueConvertFromValueParseIrDecimal.from_value_opt_eq`

end mysql_common
