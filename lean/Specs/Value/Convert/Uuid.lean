import Proofs.Value.Convert.Uuid.FromUuid
import Proofs.Value.Convert.Uuid.ParseIrUuid

/-!
# `src/value/convert/uuid.rs`
    `FromValue for uuid::Uuid` and `From<Uuid> for Value`. Translated for real (patch 46 copies
    the body of uuid 1.29.2's `Uuid::from_slice`; `Uuid` is its `[u8; 16]` field; only
    `Uuid::from_bytes`, the identity, is modelled in `FunsExternal.lean`): exact statements.

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/Value.lean` (`Val.ofValue`), `Defs/Bytes.lean` (`okPart`).

    **Trusted axioms:** none (`uuid.builder.Uuid.from_bytes` is a definition).

    **Behaviour to note.** A `Uuid` is read only from its 16 raw bytes (MySQL `BINARY(16)`); the
    text form (`"67e55044-10b1-426f-9247-bb680e5fe0c8"`) is rejected.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-! ### `impl From<Uuid> for Value` -/

/-- `From<Uuid> for Value`: `Bytes` of its 16 bytes. -/
recall value.Value.Insts.CoreConvertFromUuid.from_spec (x : uuid.Uuid) :
    value.Value.Insts.CoreConvertFromUuid.from x ⦃ w => Val.ofValue w = .bytes (Array.val x) ⦄

/-- [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromUuid.from_spec
/-- Round trip: `from_value_opt::<Uuid>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromUuid.roundtrip (x : uuid.Uuid) :
    (do let w ← value.Value.Insts.CoreConvertFromUuid.from x; value.convert.from_value_opt uuid.Uuid.Insts.Mysql_commonValueConvertFromValueParseIrUuid w) ⦃ r => r = .Ok x ⦄

/-- [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromUuid.roundtrip
/-! ### `impl TryFrom<Value> for ParseIr<Uuid>, fn uuid_from_slice` -/

/-- `uuid_from_slice` (`Uuid::from_slice(b).ok()`): total; the uuid with these bytes exactly
    when there are 16 of them. -/
recall value.convert.uuid.uuid_from_slice_spec (b : Slice U8) :
    value.convert.uuid.uuid_from_slice b ⦃ r => ∀ u : uuid.Uuid, r = some u ↔ Array.val u = b.val ⦄

/-- [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.uuid.uuid_from_slice_spec
/-- `TryFrom<Value> for ParseIr<Uuid>`: total; succeeds exactly on `Bytes` of length 16, keeping
    the original value for `rollback`. -/
recall value.convert.ParseIrUuid.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrUuid.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (∀ u w, r = .Ok (u, w) ↔ w = v ∧ Val.ofValue v = .bytes (Array.val u)) ∧
      (okPart r = none → r = .Err v) ⦄

/-- [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrUuid.Insts.CoreConvertTryFromValueFromValueError.try_from_spec
/-- `from_value_opt::<Uuid>`: as `try_from`, committed. -/
recall uuid.Uuid.Insts.Mysql_commonValueConvertFromValueParseIrUuid.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt uuid.Uuid.Insts.Mysql_commonValueConvertFromValueParseIrUuid v ⦃ r =>
      (∀ u, r = .Ok u ↔ Val.ofValue v = .bytes (Array.val u)) ∧ (okPart r = none → r = .Err v) ⦄

/-- [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms uuid.Uuid.Insts.Mysql_commonValueConvertFromValueParseIrUuid.from_value_opt_spec
/-- `From<ParseIr<Uuid>> for Uuid` is `commit`, `From<ParseIr<Uuid>> for Value` is `rollback`. -/
recall value.Value.Insts.CoreConvertFromParseIrUuid.from_eq (x : uuid.Uuid) (w : value.Value) :
    uuid.Uuid.Insts.CoreConvertFromParseIrUuid.from (x, w) = ok x ∧
    value.Value.Insts.CoreConvertFromParseIrUuid.from (x, w) = ok w

/-- [propext, choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrUuid.from_eq
end mysql_common
