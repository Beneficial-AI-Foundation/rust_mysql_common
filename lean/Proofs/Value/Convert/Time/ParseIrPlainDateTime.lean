import Defs

/-! Statements for `impl TryFrom<Value> for ParseIr<PrimitiveDateTime>` (spec file: `Specs/Value/Convert/Time.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<PrimitiveDateTime>` on a `Date`: total; converts exactly when
    time accepts the date and the time, to the date-time with these fields. -/
theorem value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_date (y : U16) (mo d h mi s : U8) (us : U32) :
    value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Date y mo d h mi s us) ⦃ r =>
      (okPart r = none → r = .Err (.Date y mo d h mi s us)) ∧
      ((∃ p, r = .Ok p) ↔ timeDateValid y.val mo.val d.val ∧ timeTimeValid h.val mi.val s.val us.val) ∧
      ∀ x w, r = .Ok (x, w) → w = .Date y mo d h mi s us ∧
        timeDateTime x = (((y.val : ℤ), mo.val, d.val), (h.val, mi.val, s.val, us.val)) ⦄ := by
  sorry

/-- `TryFrom<Value> for ParseIr<PrimitiveDateTime>` on `Bytes`: not valid UTF-8 is an error;
    otherwise time's parser (opaque) with the format chosen by the length — more than 19 bytes:
    date-time with fraction; 19: date-time; 10 to 18: date only; fewer: an error. -/
theorem value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_bytes (b : alloc.vec.Vec U8) :
    value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from (.Bytes b) = ok (
      if IsUtf8 b.val then
        match (if 19 < b.val.length then Trusted.pdtParseDateTimeMicro (alloc.vec.Vec.deref b)
          else if b.val.length = 19 then Trusted.pdtParseDateTime (alloc.vec.Vec.deref b)
          else if 10 ≤ b.val.length then Trusted.pdtParseDate (alloc.vec.Vec.deref b)
          else .Err (.TryFromParsed .InsufficientInformation)) with
        | .Ok x => .Ok (x, .Bytes b)
        | .Err _ => .Err (.Bytes b)
      else .Err (.Bytes b)) := by
  sorry

/-- `TryFrom<Value> for ParseIr<PrimitiveDateTime>`: any other value is an error. -/
theorem value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from_other (v : value.Value) (hv : ∀ y mo d h mi s us, v ≠ .Date y mo d h mi s us) (hb : ∀ b, v ≠ .Bytes b) :
    value.convert.ParseIrPlainDateTime.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v) := by
  sorry

end mysql_common
