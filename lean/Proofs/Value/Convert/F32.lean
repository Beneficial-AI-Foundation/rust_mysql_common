import Defs

/-! Statements for `impl FromValue for f32` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIrOpt<f32>`: total; `Float x` is `Ready x` (bit for bit), valid
    UTF-8 `Bytes` are parsed by Rust's `str::parse::<f32>` (opaque, `Trusted.parseF32`);
    everything else, including `Double` (no narrowing), is an error. -/
theorem value.convert.ParseIrOptF32.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrOptF32.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Float x => .Ok (.Ready x)
      | .Bytes b =>
        if IsUtf8 b.val then
          match Trusted.parseF32 (alloc.vec.Vec.deref b) with
          | some x => .Ok (.Parsed x v)
          | none => .Err v
        else .Err v
      | _ => .Err v) := by
  sorry

/-- `From<ParseIrOpt<f32>> for Value` after `try_from` gives back the original value, bit for
    bit. -/
theorem value.Value.Insts.CoreConvertFromParseIrOptF32.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptF32.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptF32.from ir
      | .Err e => ok e) = ok v := by
  sorry

end mysql_common
