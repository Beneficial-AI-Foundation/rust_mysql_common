import Defs
import Proofs.Util.ConvDeps

/-! Statements for `impl From<serde_json::Value> for Value` (spec file: `Specs/Value/Json/SerdeIntegration.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<serde_json::Value> for Value`: `Bytes` of `serde_json::to_string` (opaque), when that
    succeeds. -/
theorem value.Value.Insts.CoreConvertFromValue.from_spec (x : serde_json.value.Value) (s : String) (hs : Trusted.jsonToString x = some s) (h : (utf8 s).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromValue.from x ⦃ w => Val.ofValue w = .bytes (utf8 s) ⦄ := by
  obtain ⟨b, hb, hv⟩ := ConvDeps.string_into_bytes_val _ h
  simp [value.Value.Insts.CoreConvertFromValue.from, value.convert.trusted.json_to_string, hs,
    core.option.Option.unwrap, hb, Val.ofValue, hv]

/-- **Panic.** `From<serde_json::Value> for Value` panics when `serde_json::to_string` fails
    (`unwrap`). -/
theorem value.Value.Insts.CoreConvertFromValue.from_panic (x : serde_json.value.Value) (hs : Trusted.jsonToString x = none) :
    value.Value.Insts.CoreConvertFromValue.from x = fail .panic := by
  simp [value.Value.Insts.CoreConvertFromValue.from, value.convert.trusted.json_to_string, hs,
    core.option.Option.unwrap]

end mysql_common
