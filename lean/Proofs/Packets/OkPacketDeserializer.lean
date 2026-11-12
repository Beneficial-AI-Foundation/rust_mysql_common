import Defs

/-! Statements for `struct OkPacketDeserializer and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `into_inner`: the packet. -/
theorem packets.OkPacketDeserializer.into_inner_eq {T : Type} (self : packets.OkPacketDeserializer T) :
    packets.OkPacketDeserializer.into_inner self = ok self.1 := by
  sorry

/-- `MyDeserialize for OkPacketDeserializer<T>`: `SIZE` is `None`. -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq {T : Type} (inst : packets.OkPacketKind T) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE inst = none := by
  sorry

/-- `MyDeserialize for OkPacketDeserializer<ResultSetTerminator>`: total; `okPacketRead .resultSetTerminator` (header byte, body, conversion to `OkPacket`). -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_resultSetTerminator (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      ((okPart r).map (fun d => OkPkt.ofPacket d.1), rest.val) = okPacketRead .resultSetTerminator caps.val buf.val ⦄ := by
  sorry

/-- `MyDeserialize for OkPacketDeserializer<OldEofPacket>`: total; `okPacketRead .oldEof` (header byte, body, conversion to `OkPacket`). -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_oldEof (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      ((okPart r).map (fun d => OkPkt.ofPacket d.1), rest.val) = okPacketRead .oldEof caps.val buf.val ⦄ := by
  sorry

/-- `MyDeserialize for OkPacketDeserializer<NetworkStreamTerminator>`: total; `okPacketRead .networkStreamTerminator` (header byte, body, conversion to `OkPacket`). -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_networkStreamTerminator (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      ((okPart r).map (fun d => OkPkt.ofPacket d.1), rest.val) = okPacketRead .networkStreamTerminator caps.val buf.val ⦄ := by
  sorry

/-- `MyDeserialize for OkPacketDeserializer<CommonOkPacket>`: total; `okPacketRead .commonOk` (header byte, body, conversion to `OkPacket`). -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_commonOk (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      ((okPart r).map (fun d => OkPkt.ofPacket d.1), rest.val) = okPacketRead .commonOk caps.val buf.val ⦄ := by
  sorry

/-- Round trip: an OK packet (`okPacketEnc 0x00`, in the protocol page's form or, `compact`, as MySQL's `net_send_ok` writes it) is read back by `OkPacketDeserializer<CommonOkPacket>` (as `OkBody.toPkt`), when its status has only known flags and it carries a session state only if both `CLIENT_SESSION_TRACK` and `SERVER_SESSION_STATE_CHANGED` are set. The packet is the whole buffer. -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_commonOk (h64 : Target64) (caps : constants.CapabilityFlags) (b : OkBody) (hb : b.affectedRows < 2 ^ 64 ∧ b.lastInsertId < 2 ^ 64 ∧ b.status < 2 ^ 16 ∧
      statusRead b.status = some b.status ∧ b.warnings < 2 ^ 16)
    (hssi : (hasFlag caps.val CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = [])
    (compact : Bool) (buf : io.ParseBuf) (h : buf.val = okPacketEnc 0x00 caps.val compact b) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      (okPart r).map (fun d => OkPkt.ofPacket d.1) = some b.toPkt ∧ rest.val = [] ⦄ := by
  sorry

/-- Round trip: an OK packet with header `0xFE` (either form) is read back by `OkPacketDeserializer<ResultSetTerminator>`, with affected rows and last insert id 0. -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_resultSetTerminator (h64 : Target64) (caps : constants.CapabilityFlags) (b : OkBody) (hb : b.affectedRows < 2 ^ 64 ∧ b.lastInsertId < 2 ^ 64 ∧ b.status < 2 ^ 16 ∧
      statusRead b.status = some b.status ∧ b.warnings < 2 ^ 16)
    (hssi : (hasFlag caps.val CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = [])
    (compact : Bool) (buf : io.ParseBuf) (h : buf.val = okPacketEnc 0xFE caps.val compact b) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      (okPart r).map (fun d => OkPkt.ofPacket d.1) =
        some { b with affectedRows := 0, lastInsertId := 0 }.toPkt ∧ rest.val = [] ⦄ := by
  sorry

/-- Round trip: an EOF packet is read back by `OkPacketDeserializer<OldEofPacket>` when its status has only known flags. -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_oldEof (caps : constants.CapabilityFlags) (w s : Nat) (hw : w < 2 ^ 16) (hs : s < 2 ^ 16)
    (hsk : statusRead s = some s) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = eofPacketEnc w s ++ tail) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      (okPart r).map (fun d => OkPkt.ofPacket d.1) = some ⟨0, none, s, w, none, none⟩ ∧ rest.val = tail ⦄ := by
  sorry

/-- Round trip: an EOF packet is read back by `OkPacketDeserializer<NetworkStreamTerminator>` when its status has only known flags. -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_networkStreamTerminator (caps : constants.CapabilityFlags) (w s : Nat) (hw : w < 2 ^ 16) (hs : s < 2 ^ 16)
    (hsk : statusRead s = some s) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = eofPacketEnc w s ++ tail) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      (okPart r).map (fun d => OkPkt.ofPacket d.1) = some ⟨0, none, s, w, none, none⟩ ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
