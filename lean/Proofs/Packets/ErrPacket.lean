import Defs

/-! Statements for `enum ErrPacket and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `is_error`: an error, not a progress report. -/
theorem packets.ErrPacket.is_error_spec (self : packets.ErrPacket) :
    packets.ErrPacket.is_error self ⦃ b => (b ↔ ∃ e, self = .Error e) ⦄ := by
  sorry

/-- `is_progress_report`: a progress report. -/
theorem packets.ErrPacket.is_progress_report_spec (self : packets.ErrPacket) :
    packets.ErrPacket.is_progress_report self ⦃ b => (b ↔ ∃ p, self = .Progress p) ⦄ := by
  sorry

/-- `progress_report`: the report. -/
theorem packets.ErrPacket.progress_report_progress (p : packets.ProgressReport) :
    packets.ErrPacket.progress_report (.Progress p) = ok p := by
  sorry

/-- `progress_report` panics on an error (documented). -/
theorem packets.ErrPacket.progress_report_error (e : packets.ServerError) :
    packets.ErrPacket.progress_report (.Error e) = fail .panic := by
  sorry

/-- `server_error`: the error. -/
theorem packets.ErrPacket.server_error_error (e : packets.ServerError) :
    packets.ErrPacket.server_error (.Error e) = ok e := by
  sorry

/-- `server_error` panics on a progress report (documented). -/
theorem packets.ErrPacket.server_error_progress (p : packets.ProgressReport) :
    packets.ErrPacket.server_error (.Progress p) = fail .panic := by
  sorry

/-- `MyDeserialize for ErrPacket`: `SIZE` is `None`. -/
theorem packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq :
    packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE = none := by
  sorry

/-- `MyDeserialize for ErrPacket`: total; `errPacketRead` (header, code, then a progress report or the SQL state and message). -/
theorem packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      ((okPart r).map ErrPkt.of, rest.val) = errPacketRead caps.val buf.val ⦄ := by
  sorry

/-- `MySerialize for ErrPacket`: appends `errPacketEnc` (the progress truncated to 3 bytes). -/
theorem packets.ErrPacket.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ErrPacket) (buf : alloc.vec.Vec U8)
    (h : buf.length + (errPacketEnc (ErrPkt.of self)).length ≤ Usize.max) :
    packets.ErrPacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ errPacketEnc (ErrPkt.of self) ⦄ := by
  sorry

/-- Round trip: an ERR packet is read back when it fits the capabilities (`errCompatible`: SQL state iff `CLIENT_PROTOCOL_41`, no error code `0xFFFF` under `CLIENT_PROGRESS_OBSOLETE`, progress reports only under it). The packet is the whole buffer (the message extends to its end). -/
theorem packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip (h64 : Target64) (caps : constants.CapabilityFlags) (e : packets.ErrPacket)
    (hc : errCompatible caps.val (ErrPkt.of e)) (buf : io.ParseBuf) (h : buf.val = errPacketEnc (ErrPkt.of e)) :
    packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      (okPart r).map ErrPkt.of = some (ErrPkt.of e) ∧ rest.val = [] ⦄ := by
  sorry

end mysql_common
