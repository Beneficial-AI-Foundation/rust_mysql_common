import Defs

/-! Statements for `impl FromValue for bool` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

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
  sorry

/-- `from_value_opt::<bool>`: total; a nonzero integer is `true`, the text `"0"`/`"1"` is
    `false`/`true`. -/
theorem Bool.Insts.Mysql_commonValueConvertFromValueParseIrOptBool.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt Bool.Insts.Mysql_commonValueConvertFromValueParseIrOptBool v = ok (match Val.ofValue v with
      | .int x => .Ok (decide (x ≠ 0))
      | .uint x => .Ok (decide (x ≠ 0))
      | .bytes [c] => if c.val = 48 then .Ok false else if c.val = 49 then .Ok true else .Err v
      | _ => .Err v) := by
  sorry

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
  sorry

end mysql_common
