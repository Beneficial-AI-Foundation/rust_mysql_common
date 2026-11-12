import Defs
import Proofs.Util.ConvInts

/-! Statements for `impl FromValue for bool` (spec file: `Specs/Value/Convert.lean`). Helper lemmas: `Proofs/Util/ConvInts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIrOpt<bool>`: total; `Int`/`UInt` are `Ready (x ≠ 0)`, `Bytes "0"` and
    `Bytes "1"` are `Parsed`; anything else (other bytes, `"true"`, floats, `NULL`) is an
    error. -/
theorem value.convert.ParseIrOptBool.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrOptBool.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Int x => .Ok (.Ready (decide (x.val ≠ 0)))
      | .UInt x => .Ok (.Ready (decide (x.val ≠ 0)))
      | .Bytes b =>
        if b.val = [byte 48] then .Ok (.Parsed false v)
        else if b.val = [byte 49] then .Ok (.Parsed true v)
        else .Err v
      | _ => .Err v) := by
  cases v with
  | Int x =>
    simp only [value.convert.ParseIrOptBool.Insts.CoreConvertTryFromValueFromValueError.try_from]
    split
    · rfl
    · rename_i hx
      have : x.val ≠ 0 := by
        intro h; apply hx; have h0 : x = 0#i64 := by scalar_tac
        rw [h0]; rfl
      simp [this]
  | UInt x =>
    simp only [value.convert.ParseIrOptBool.Insts.CoreConvertTryFromValueFromValueError.try_from]
    split
    · rfl
    · rename_i hx
      have : x.val ≠ 0 := by
        intro h; apply hx; have h0 : x = 0#u64 := by scalar_tac
        rw [h0]; rfl
      simp [this]
  | Bytes b =>
    simp only [value.convert.ParseIrOptBool.Insts.CoreConvertTryFromValueFromValueError.try_from,
      alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
    have h48 : (48#u8 : U8) = byte 48 := rfl
    have h49 : (49#u8 : U8) = byte 49 := rfl
    have hu : ∀ h, Usize.ofNatCore 1 h = 1#usize := fun _ => rfl
    rcases hb : b.val with _ | ⟨c, _ | ⟨d, l⟩⟩
    all_goals simp [hb, h48, h49, hu]
    split_ifs <;> rfl
  | _ => rfl

/-- `from_value_opt::<bool>`: total; a nonzero integer is `true`, the text `"0"`/`"1"` is
    `false`/`true`. -/
theorem Bool.Insts.Mysql_commonValueConvertFromValueParseIrOptBool.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt Bool.Insts.Mysql_commonValueConvertFromValueParseIrOptBool v = ok (match Val.ofValue v with
      | .int x => .Ok (decide (x ≠ 0))
      | .uint x => .Ok (decide (x ≠ 0))
      | .bytes [c] => if c.val = 48 then .Ok false else if c.val = 49 then .Ok true else .Err v
      | _ => .Err v) := by
  have hd : value.convert.from_value_opt Bool.Insts.Mysql_commonValueConvertFromValueParseIrOptBool v =
      value.convert.FromValue.from_value_opt.default Bool.Insts.Mysql_commonValueConvertFromValueParseIrOptBool v := rfl
  rw [hd]
  simp only [value.convert.FromValue.from_value_opt.default, core.convert.IntoFrom.into,
    Bool.Insts.CoreConvertFromParseIrOptBool.from]
  rw [value.convert.ParseIrOptBool.Insts.CoreConvertTryFromValueFromValueError.try_from_eq, bind_ok]
  cases v with
  | Bytes b =>
    rcases hb : b.val with _ | ⟨c, _ | ⟨d, l⟩⟩ <;> simp [Val.ofValue, hb, ConvInts.byte_eq_iff, value.convert.ParseIrOpt.commit]
    split_ifs <;> simp
  | _ => simp [Val.ofValue, value.convert.ParseIrOpt.commit]

/-- `From<ParseIrOpt<bool>> for Value` after `try_from`: an integer comes back as `Int 0` or
    `Int 1` (so `UInt 7` comes back as `Int 1`); everything else unchanged. -/
theorem value.Value.Insts.CoreConvertFromParseIrOptBool.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptBool.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptBool.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = match Val.ofValue v with
        | .int x => .int (if x = 0 then 0 else 1)
        | .uint x => .int (if x = 0 then 0 else 1)
        | u => u ⦄ := by
  rw [value.convert.ParseIrOptBool.Insts.CoreConvertTryFromValueFromValueError.try_from_eq, bind_ok]
  cases v with
  | Int x =>
    by_cases hx : x.val = 0 <;>
      simp [hx, Val.ofValue, value.Value.Insts.CoreConvertFromParseIrOptBool.from,
        value.convert.ParseIrOpt.rollback, value.Value.Insts.CoreConvertFromBool.from]
  | UInt x =>
    by_cases hx : x.val = 0 <;>
      simp [hx, Val.ofValue, value.Value.Insts.CoreConvertFromParseIrOptBool.from,
        value.convert.ParseIrOpt.rollback, value.Value.Insts.CoreConvertFromBool.from]
  | Bytes b =>
    simp only
    split_ifs <;>
      simp [Val.ofValue, value.Value.Insts.CoreConvertFromParseIrOptBool.from,
        value.convert.ParseIrOpt.rollback]
  | _ => simp [Val.ofValue]

end mysql_common
