import Defs

/-! Statements for `enum SessionStateChange and its impls` (spec file: `Specs/Packets/SessionStateChange.lean`).
Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `into_owned`: the same change. -/
theorem packets.session_state_change.SessionStateChange.into_owned_spec (self : packets.session_state_change.SessionStateChange) :
    packets.session_state_change.SessionStateChange.into_owned self ⦃ c => SsChange.of c = SsChange.of self ⦄ := by
  sorry

/-- `MyDeserialize for SessionStateChange`: `SIZE` is `None`. -/
theorem packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.SIZE_eq :
    packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.SIZE = none := by
  sorry

/-- `MyDeserialize for SessionStateChange` with the type `ty`: total; `ssChangeRead ty` (the
    protocol's `data` layout of that type; system variables until the input is exhausted;
    `IsTracked` is `true` exactly for `"1"`). -/
theorem packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.deserialize_spec
    (h64 : Target64) (ty : constants.SessionStateType) (buf : io.ParseBuf) :
    packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.deserialize ty buf ⦃ r rest =>
      ((okPart r).map SsChange.of, rest.val) = ssChangeRead ty buf.val ⦄ := by
  sorry

/-- Round trip: the `data` of a change (`ssChangeEnc`), read with the change's type, gives the
    change back (for system variables the data must end there, as the reader takes pairs until
    the input is exhausted). `Unsupported` has no type and is never read. -/
theorem packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.roundtrip
    (h64 : Target64) (c : packets.session_state_change.SessionStateChange) (ty : constants.SessionStateType)
    (hty : (SsChange.of c).type? = some ty)
    (tail : List U8) (htail : tail = [] ∨ ty ≠ .SESSION_TRACK_SYSTEM_VARIABLES) (buf : io.ParseBuf)
    (h : buf.val = ssChangeEnc (SsChange.of c) ++ tail) :
    packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.deserialize ty buf ⦃ r rest =>
      (okPart r).map SsChange.of = some (SsChange.of c) ∧ rest.val = tail ⦄ := by
  sorry

/-- `MySerialize for SessionStateChange`: appends `ssChangeEnc` (the protocol's `data`; for
    `IsTracked`, `"1"` or `"0"`). -/
theorem packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.session_state_change.SessionStateChange) (buf : alloc.vec.Vec U8)
    (h : buf.length + (ssChangeEnc (SsChange.of self)).length ≤ Usize.max) :
    packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ ssChangeEnc (SsChange.of self) ⦄ := by
  sorry

end mysql_common
