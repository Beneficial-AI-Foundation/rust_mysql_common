import Defs

/-! Statements for `impl TryFrom<Value> for ParseIr<Time>` (spec file: `Specs/Value/Convert/Time.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<Time>` on a positive `TIME` with 0 days: total; converts exactly
    when time accepts the fields. -/
theorem value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_time (h m s : U8) (us : U32) :
    value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Time false 0#u32 h m s us) ⦃ r =>
      (okPart r = none → r = .Err (.Time false 0#u32 h m s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeTimeValid h.val m.val s.val us.val) ∧
      ∀ x w, r = .Ok (x, w) → w = .Time false 0#u32 h m s us ∧ timeTime x = (h.val, m.val, s.val, us.val) ⦄ := by
  sorry

/-- `TryFrom<Value> for ParseIr<Time>` on `Bytes`: not valid UTF-8 or fewer than 8 bytes is an
    error; 8 bytes: time's `hh:mm:ss` parser; more: the parser with a fraction (both opaque). -/
theorem value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes (b : alloc.vec.Vec U8) :
    value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (
      if IsUtf8 b.val then
        match (if b.val.length < 8 then .Err (.TryFromParsed .InsufficientInformation)
          else if b.val.length = 8 then Trusted.timeParseTime (alloc.vec.Vec.deref b)
          else Trusted.timeParseTimeMicro (alloc.vec.Vec.deref b)) with
        | .Ok x => .Ok (x, .Bytes b)
        | .Err _ => .Err (.Bytes b)
      else .Err (.Bytes b)) := by
  sorry

/-- `TryFrom<Value> for ParseIr<Time>`: any other value (including a negative `TIME` or one with
    days) is an error. -/
theorem value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other (v : value.Value) (hv : ∀ h m s us, v ≠ .Time false 0#u32 h m s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.ParseIrTime.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v) := by
  sorry

end mysql_common
