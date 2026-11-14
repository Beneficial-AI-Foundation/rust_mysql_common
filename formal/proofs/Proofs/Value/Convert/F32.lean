import Defs
import Proofs.Defs.LemmasG

/-! Statements for `impl FromValue for f32` (spec file: `Specs/Value/Convert.lean`). -/

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
  cases v with
  | Bytes b =>
    simp only [value.convert.ParseIrOptF32.Insts.CoreConvertTryFromValueFromValueError.try_from, value.convert.trusted.str_from_utf8,
      value.convert.trusted.str_parse_f32, bind_ok]
    have hv : (alloc.vec.Vec.deref b).val = b.val := by simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
    by_cases hu : IsUtf8 b.val
    · have hu' := (Defs.isUtf8_iff_isValidUTF8 b.val).mp hu
      rw [hv]
      simp only [hu', ite_true, hu]
      cases Trusted.parseF32 (alloc.vec.Vec.deref b) <;> rfl
    · have hu' : ¬ (Trusted.bytesOf b.val).IsValidUTF8 := fun h => hu ((Defs.isUtf8_iff_isValidUTF8 b.val).mpr h)
      rw [hv]
      simp only [hu', ite_false, hu]
  | _ => simp [value.convert.ParseIrOptF32.Insts.CoreConvertTryFromValueFromValueError.try_from,]

/-- `From<ParseIrOpt<f32>> for Value` after `try_from` gives back the original value, bit for
    bit. -/
theorem value.Value.Insts.CoreConvertFromParseIrOptF32.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptF32.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptF32.from ir
      | .Err e => ok e) = ok v := by
  rw [value.convert.ParseIrOptF32.Insts.CoreConvertTryFromValueFromValueError.try_from_eq, bind_ok]
  cases v with
  | Bytes b =>
    simp only
    split_ifs
    · cases Trusted.parseF32 (alloc.vec.Vec.deref b) <;>
        simp [value.Value.Insts.CoreConvertFromParseIrOptF32.from, value.convert.ParseIrOpt.rollback]
    · simp
  | _ => simp [value.Value.Insts.CoreConvertFromParseIrOptF32.from, value.convert.ParseIrOpt.rollback,
      value.Value.Insts.CoreConvertFromF32.from]

end mysql_common
