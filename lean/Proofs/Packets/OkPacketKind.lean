import Defs

/-! Statements for `trait OkPacketKind and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `HEADER` is `0xFE`. -/
theorem packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq :
    packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER = 254#u8 := by
  sorry

/-- `HEADER` is `0xFE`. -/
theorem packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq :
    packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER = 254#u8 := by
  sorry

/-- `HEADER` is `0xFE`. -/
theorem packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq :
    packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER = 254#u8 := by
  sorry

/-- `HEADER` is `0x00`. -/
theorem packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq :
    packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER = 0#u8 := by
  sorry

/-- `OkPacketKind::parse_body for ResultSetTerminator`: total; the OK packet fields after the header (`rsTerminatorBodyRead`): affected rows and last insert id are read but reported as 0. -/
theorem packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body caps buf ⦃ r rest =>
      ((okPart r).map OkBody.ofBody, rest.val) = rsTerminatorBodyRead caps.val buf.val ⦄ := by
  sorry

/-- `OkPacketKind::parse_body for OldEofPacket`: total; `warnings` and `status_flags` (`eofBodyRead`). -/
theorem packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body caps buf ⦃ r rest =>
      ((okPart r).map OkBody.ofBody, rest.val) = eofBodyRead buf.val ⦄ := by
  sorry

/-- `OkPacketKind::parse_body for NetworkStreamTerminator`: total; as `OldEofPacket` (`eofBodyRead`). -/
theorem packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body caps buf ⦃ r rest =>
      ((okPart r).map OkBody.ofBody, rest.val) = eofBodyRead buf.val ⦄ := by
  sorry

/-- `OkPacketKind::parse_body for CommonOkPacket`: total; the OK packet fields after the header (`okBodyRead`). -/
theorem packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body caps buf ⦃ r rest =>
      ((okPart r).map OkBody.ofBody, rest.val) = okBodyRead caps.val buf.val ⦄ := by
  sorry

end mysql_common
