import Defs

/-! Statements for `impl From<Uuid> for Value` (spec file: `Specs/Value/Convert/Uuid.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<Uuid> for Value`: `Bytes` of its 16 bytes. -/
theorem value.Value.Insts.CoreConvertFromUuid.from_spec (x : uuid.Uuid) :
    value.Value.Insts.CoreConvertFromUuid.from x ⦃ w => Val.ofValue w = .bytes (Array.val x) ⦄ := by
  sorry

/-- Round trip: `from_value_opt::<Uuid>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromUuid.roundtrip (x : uuid.Uuid) :
    (do let w ← value.Value.Insts.CoreConvertFromUuid.from x; value.convert.from_value_opt uuid.Uuid.Insts.Mysql_commonValueConvertFromValueParseIrUuid w) ⦃ r => r = .Ok x ⦄ := by
  sorry

end mysql_common
