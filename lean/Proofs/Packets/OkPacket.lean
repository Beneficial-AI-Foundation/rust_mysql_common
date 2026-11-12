import Defs

/-! Statements for `struct OkPacket and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `TryFrom<OkPacketBody> for OkPacket`: never fails; `OkBody.toPkt` (a last insert id of 0 and empty strings become `None`). -/
theorem packets.OkPacket.Insts.CoreConvertTryFromOkPacketBodyError.try_from_spec (body : packets.OkPacketBody) :
    packets.OkPacket.Insts.CoreConvertTryFromOkPacketBodyError.try_from body ⦃ r =>
      (okPart r).map OkPkt.ofPacket = some (OkBody.ofBody body).toPkt ⦄ := by
  sorry

/-- `into_owned`: the same fields. -/
theorem packets.OkPacket.into_owned_spec (self : packets.OkPacket) :
    packets.OkPacket.into_owned self ⦃ p => OkPkt.ofPacket p = OkPkt.ofPacket self ⦄ := by
  sorry

/-- `affected_rows`: the field. -/
theorem packets.OkPacket.impl.affected_rows_eq (self : packets.OkPacket) :
    packets.OkPacket.impl.affected_rows self = ok self.affected_rows := by
  sorry

/-- `last_insert_id`: the field. -/
theorem packets.OkPacket.impl.last_insert_id_eq (self : packets.OkPacket) :
    packets.OkPacket.impl.last_insert_id self = ok self.last_insert_id := by
  sorry

/-- `status_flags`: the field. -/
theorem packets.OkPacket.impl.status_flags_eq (self : packets.OkPacket) :
    packets.OkPacket.impl.status_flags self = ok self.status_flags := by
  sorry

/-- `warnings`: the field. -/
theorem packets.OkPacket.impl.warnings_eq (self : packets.OkPacket) :
    packets.OkPacket.impl.warnings self = ok self.warnings := by
  sorry

/-- `info_ref`: the info bytes, if any. -/
theorem packets.OkPacket.info_ref_spec (self : packets.OkPacket) :
    packets.OkPacket.info_ref self ⦃ o => o.map (·.val) = self.info.map (fun rb => cowList rb.1) ⦄ := by
  sorry

/-- `session_state_info_ref`: the session state bytes, if any. -/
theorem packets.OkPacket.session_state_info_ref_spec (self : packets.OkPacket) :
    packets.OkPacket.session_state_info_ref self ⦃ o =>
      o.map (·.val) = self.session_state_info.map (fun rb => cowList rb.1) ⦄ := by
  sorry

end mysql_common
