import Defs

/-! Statements for `impl FromValue for f64` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIrOpt<f64>`: total; `Double x` is `Ready x`, `Float x` is `Ready` of
    its widening (opaque, `Trusted.f32ToF64`), valid UTF-8 `Bytes` are parsed by
    `str::parse::<f64>` (opaque, `Trusted.parseF64`); everything else is an error. -/
theorem value.convert.ParseIrOptF64.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrOptF64.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Double x => .Ok (.Ready x)
      | .Float x => .Ok (.Ready (Trusted.f32ToF64 x))
      | .Bytes b =>
        if IsUtf8 b.val then
          match Trusted.parseF64 (alloc.vec.Vec.deref b) with
          | some x => .Ok (.Parsed x v)
          | none => .Err v
        else .Err v
      | _ => .Err v) := by
  sorry

/-- `From<ParseIrOpt<f64>> for Value` after `try_from`: the original value, except that a `Float`
    comes back as a `Double` (of its widening). -/
theorem value.Value.Insts.CoreConvertFromParseIrOptF64.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptF64.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptF64.from ir
      | .Err e => ok e) =
      ok (match v with | .Float x => .Double (Trusted.f32ToF64 x) | u => u) := by
  sorry

end mysql_common
