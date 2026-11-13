import Defs
import Proofs.Util.ConvDeps
import Proofs.Value.Convert.Uuid.ParseIrUuid

/-! Statements for `impl From<Uuid> for Value` (spec file: `Specs/Value/Convert/Uuid.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<Uuid> for Value`: `Bytes` of its 16 bytes. -/
theorem value.Value.Insts.CoreConvertFromUuid.from_spec (x : uuid.Uuid) :
    value.Value.Insts.CoreConvertFromUuid.from x ⦃ w => Val.ofValue w = .bytes (Array.val x) ⦄ := by
  unfold value.Value.Insts.CoreConvertFromUuid.from
  simp only [uuid.Uuid.as_bytes]
  step*
  simp_all [Val.ofValue, alloc.vec.Vec.val, Array.to_slice]

/-- Round trip: `from_value_opt::<Uuid>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromUuid.roundtrip (x : uuid.Uuid) :
    (do let w ← value.Value.Insts.CoreConvertFromUuid.from x; value.convert.from_value_opt uuid.Uuid.Insts.Mysql_commonValueConvertFromValueParseIrUuid w) ⦃ r => r = .Ok x ⦄ := by
  apply WP.spec_bind (value.Value.Insts.CoreConvertFromUuid.from_spec x)
  intro w hw
  apply WP.spec_mono (uuid.Uuid.Insts.Mysql_commonValueConvertFromValueParseIrUuid.from_value_opt_spec w)
  rintro r ⟨h1, _⟩
  exact (h1 x).2 hw

end mysql_common
