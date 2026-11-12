import Proofs.Value.Convert.Bigdecimal

/-!
# `src/value/convert/bigdecimal.rs`
    `FromValue` and `From<_> for Value` for bigdecimal's `BigDecimal`. Opaque, glue-level, as for
    `Specs/Value/Convert/Bigint.lean`.

    **Configuration.** As in `Specs/Io.lean` (feature `bigdecimal`, bigdecimal 0.4.11).

    **Definitions used.** `Defs/Convert.lean` (`utf8`), `Defs/Value.lean`.

    **Trusted axioms these statements rest on:** `Trusted.bigdecimalFromI64`,
    `bigdecimalFromU64`, `bigdecimalTryFromF32`, `bigdecimalTryFromF64`, `bigdecimalParseBytes`,
    `bigdecimalToString`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-! ### `impl FromValue for BigDecimal, impl From<BigDecimal> for Value` -/

/-- `TryFrom<Value> for ParseIr<BigDecimal>`: `Int`/`UInt` are converted, `Float`/`Double`
    converted when the opaque `TryFrom` succeeds (not for NaN/infinities), `Bytes` parsed
    (opaque); anything else is an error carrying the value. -/
recall value.convert.ParseIrBigDecimal.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
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
      | _ => .Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrBigDecimal.Insts.CoreConvertTryFromValueFromValueError.try_from_eq`

/-- `From<ParseIr<BigDecimal>>` for `BigDecimal` is `commit`, for `Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrBigDecimal.from_eq (x : bigdecimal.BigDecimal) (w : value.Value) :
    bigdecimal.BigDecimal.Insts.CoreConvertFromParseIrBigDecimal.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrBigDecimal.from (x, w) = ok w

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrBigDecimal.from_eq`

/-- `From<BigDecimal> for Value`: `Bytes` of its text (`to_string`, opaque). -/
recall value.Value.Insts.CoreConvertFromBigDecimal.from_spec (x : bigdecimal.BigDecimal) (h : (utf8 (Trusted.bigdecimalToString x)).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromBigDecimal.from x ⦃ w =>
      Val.ofValue w = .bytes (utf8 (Trusted.bigdecimalToString x)) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromBigDecimal.from_spec`

end mysql_common
