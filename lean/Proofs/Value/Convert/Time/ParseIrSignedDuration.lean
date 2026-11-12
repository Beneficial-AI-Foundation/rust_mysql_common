import Defs

/-! Statements for `impl TryFrom<Value> for ParseIr<time::Duration>` (spec file: `Specs/Value/Convert/Time.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIr<time::Duration>` (glue level: time's `Duration` arithmetic is
    opaque and may panic): on a `TIME`, or on `Bytes` (ASCII) holding a text `TIME` literal, if it
    returns, it returns `Ok` keeping the original value; on other `Bytes` or any other value it
    is an error carrying the value. -/
theorem value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii) (r : core.result.Result (value.convert.ParseIr time.signed_duration.SignedDuration) value.convert.FromValueError)
    (h : value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok r) :
    match Val.ofValue v with
    | .time .. => ∃ x, r = .Ok (x, v)
    | .bytes b => (timeStringRead b).isSome → ∃ x, r = .Ok (x, v)
    | _ => r = .Err v := by
  sorry

/-- `TryFrom<Value> for ParseIr<time::Duration>` is an error (no opaque call) on `Bytes` (ASCII)
    that are not a text `TIME` literal and on every value other than `TIME` and `Bytes`. -/
theorem value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_err (v : value.Value) (ha : (Val.ofValue v).bytesAscii)
    (hv : match Val.ofValue v with | .time .. => False | .bytes b => timeStringRead b = none | _ => True) :
    value.convert.ParseIrSignedDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Err v) := by
  sorry

end mysql_common
