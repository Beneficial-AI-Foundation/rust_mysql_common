import Defs
import Proofs.Util.PacketsOkErr

/-! Statements for `struct OkPacket and its impls` (spec file: `Specs/Packets.lean`). Helper lemmas: `Proofs/Util/PacketsOkErr.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts

namespace mysql_common

/-- `TryFrom<OkPacketBody> for OkPacket`: never fails; `OkBody.toPkt` (a last insert id of 0 and empty strings become `None`). -/
@[step]
theorem packets.OkPacket.Insts.CoreConvertTryFromOkPacketBodyError.try_from_spec (body : packets.OkPacketBody) :
    packets.OkPacket.Insts.CoreConvertTryFromOkPacketBodyError.try_from body ⦃ r =>
      (okPart r).map OkPkt.ofPacket = some (OkBody.ofBody body).toPkt ⦄ := by
  unfold packets.OkPacket.Insts.CoreConvertTryFromOkPacketBodyError.try_from
  step*
  split_ifs with h0 <;> step* <;> simp_all [OkPkt.ofPacket, OkBody.toPkt, OkBody.ofBody]
  · exact ⟨by simp [← i1_post], rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- `into_owned`: the same fields. -/
theorem packets.OkPacket.into_owned_spec (self : packets.OkPacket) :
    packets.OkPacket.into_owned self ⦃ p => OkPkt.ofPacket p = OkPkt.ofPacket self ⦄ := by
  unfold packets.OkPacket.into_owned
  rcases self with ⟨a, b, c, d, info, ssi⟩
  cases info <;> cases ssi <;> step* <;> simp_all [OkPkt.ofPacket]

/-- `affected_rows`: the field. -/
theorem packets.OkPacket.impl.affected_rows_eq (self : packets.OkPacket) :
    packets.OkPacket.impl.affected_rows self = ok self.affected_rows := by
  rfl

/-- `last_insert_id`: the field. -/
theorem packets.OkPacket.impl.last_insert_id_eq (self : packets.OkPacket) :
    packets.OkPacket.impl.last_insert_id self = ok self.last_insert_id := by
  rfl

/-- `status_flags`: the field. -/
theorem packets.OkPacket.impl.status_flags_eq (self : packets.OkPacket) :
    packets.OkPacket.impl.status_flags self = ok self.status_flags := by
  rfl

/-- `warnings`: the field. -/
theorem packets.OkPacket.impl.warnings_eq (self : packets.OkPacket) :
    packets.OkPacket.impl.warnings self = ok self.warnings := by
  rfl

/-- `info_ref`: the info bytes, if any. -/
theorem packets.OkPacket.info_ref_spec (self : packets.OkPacket) :
    packets.OkPacket.info_ref self ⦃ o => o.map (·.val) = self.info.map (fun rb => cowList rb.1) ⦄ := by
  unfold packets.OkPacket.info_ref
  step* <;> simp_all

/-- `session_state_info_ref`: the session state bytes, if any. -/
theorem packets.OkPacket.session_state_info_ref_spec (self : packets.OkPacket) :
    packets.OkPacket.session_state_info_ref self ⦃ o =>
      o.map (·.val) = self.session_state_info.map (fun rb => cowList rb.1) ⦄ := by
  unfold packets.OkPacket.session_state_info_ref
  step* <;> simp_all

end mysql_common
