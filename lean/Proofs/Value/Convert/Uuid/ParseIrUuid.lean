import Defs

/-! Statements for `impl TryFrom<Value> for ParseIr<Uuid>, fn uuid_from_slice` (spec file: `Specs/Value/Convert/Uuid.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `uuid_from_slice` (`Uuid::from_slice(b).ok()`): total; the uuid with these bytes exactly
    when there are 16 of them. -/
theorem value.convert.uuid.uuid_from_slice_spec (b : Slice U8) :
    value.convert.uuid.uuid_from_slice b ⦃ r => ∀ u : uuid.Uuid, r = some u ↔ Array.val u = b.val ⦄ := by
  sorry

/-- `TryFrom<Value> for ParseIr<Uuid>`: total; succeeds exactly on `Bytes` of length 16, keeping
    the original value for `rollback`. -/
theorem value.convert.ParseIrUuid.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrUuid.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (∀ u w, r = .Ok (u, w) ↔ w = v ∧ Val.ofValue v = .bytes (Array.val u)) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  sorry

/-- `from_value_opt::<Uuid>`: as `try_from`, committed. -/
theorem uuid.Uuid.Insts.Mysql_commonValueConvertFromValueParseIrUuid.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt uuid.Uuid.Insts.Mysql_commonValueConvertFromValueParseIrUuid v ⦃ r =>
      (∀ u, r = .Ok u ↔ Val.ofValue v = .bytes (Array.val u)) ∧ (okPart r = none → r = .Err v) ⦄ := by
  sorry

/-- `From<ParseIr<Uuid>> for Uuid` is `commit`, `From<ParseIr<Uuid>> for Value` is `rollback`. -/
theorem value.Value.Insts.CoreConvertFromParseIrUuid.from_eq (x : uuid.Uuid) (w : value.Value) :
    uuid.Uuid.Insts.CoreConvertFromParseIrUuid.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrUuid.from (x, w) = ok w := by
  sorry

end mysql_common
