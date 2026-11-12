import Defs

/-! Statements for `impl From<serde_json::Value> for Value` (spec file: `Specs/Value/Json/SerdeIntegration.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<serde_json::Value> for Value`: `Bytes` of `serde_json::to_string` (opaque), when that
    succeeds. -/
theorem value.Value.Insts.CoreConvertFromValue.from_spec (x : serde_json.value.Value) (s : String) (hs : Trusted.jsonToString x = some s) (h : (utf8 s).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromValue.from x ⦃ w => Val.ofValue w = .bytes (utf8 s) ⦄ := by
  sorry

/-- **Panic.** `From<serde_json::Value> for Value` panics when `serde_json::to_string` fails
    (`unwrap`). -/
theorem value.Value.Insts.CoreConvertFromValue.from_panic (x : serde_json.value.Value) (hs : Trusted.jsonToString x = none) :
    value.Value.Insts.CoreConvertFromValue.from x = fail .panic := by
  sorry

end mysql_common
