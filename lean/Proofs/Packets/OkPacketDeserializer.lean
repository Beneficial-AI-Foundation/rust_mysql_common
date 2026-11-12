import Defs
import Proofs.Util.PacketsOkErr
import Proofs.Packets.OkPacketKind
import Proofs.Packets.OkPacket

/-! Statements for `struct OkPacketDeserializer and its impls` (spec file: `Specs/Packets.lean`). Helper lemmas: `Proofs/Util/PacketsOkErr.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts

namespace mysql_common

private theorem deser_generic {T : Type} (inst : packets.OkPacketKind T) (k : OkKind) (hdr : U8)
    (hH : inst.HEADER = ok hdr) (hk : hdr.val = k.header) (caps : constants.CapabilityFlags)
    (hP : ∀ b : io.ParseBuf, inst.parse_body caps b ⦃ r rest =>
      ((okPart r).map OkBody.ofBody, rest.val) = k.bodyRead caps.val b.val ⦄)
    (buf : io.ParseBuf) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize inst caps buf ⦃ r rest =>
      ((okPart r).map (fun d => OkPkt.ofPacket d.1), rest.val) = okPacketRead k caps.val buf.val ⦄ := by
  unfold packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize
  step with U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec as ⟨r, buf1, h1⟩
  cases hb : (↑buf : List U8) with
  | nil =>
    have hl : ¬ 1 ≤ Slice.length buf := by simp [Slice.length, hb]
    rw [if_neg hl] at h1
    obtain ⟨hr, rfl⟩ := h1
    cases r with
    | Ok _ => simp at hr
    | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, okPacketRead, hb]
  | cons h t =>
    have hl : 1 ≤ Slice.length buf := by simp [Slice.length, hb]
    rw [if_pos hl, hb] at h1
    obtain ⟨hr, hb1⟩ := h1
    cases r with
    | Err e => simp at hr
    | Ok v =>
      simp [leNat] at hr hb1
      simp only [CoreOpsTry.branch, bind_tc_ok]
      step with rawint_deref_spec as ⟨i, hi⟩
      simp only [hH, bind_tc_ok, Std.bind_ok]
      subst hi
      simp only [okPacketRead]
      by_cases heq : v.1 = hdr
      · have hv : h.val = k.header := by rw [← hr, heq, hk]
        rw [if_pos heq]
        simp only [hv, ne_eq, not_true_eq_false, ite_false]
        step with hP buf1 as ⟨r1, buf2, h2⟩
        rw [hb1] at h2
        rw [← h2]
        cases r1 with
        | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok opb =>
          simp only [CoreOpsTry.branch, bind_tc_ok, okPart_Ok, Option.map_some]
          step with packets.OkPacket.Insts.CoreConvertTryFromOkPacketBodyError.try_from_spec as ⟨r2, h3⟩
          cases r2 with
          | Err e => simp at h3
          | Ok op =>
            simp only [okPart_Ok, Option.map_some, Option.some.injEq] at h3
            simp [CoreOpsTry.branch]
            exact ⟨(op, ()), rfl, h3⟩
      · have hv : ¬ h.val = k.header := by
          rw [← hr, ← hk]; intro hh; apply heq; scalar_tac
        rw [if_neg heq]
        simp only [hv, ne_eq, not_false_eq_true, ite_true]
        simp [misc.io_error_from, hb1]


/-- `into_inner`: the packet. -/
theorem packets.OkPacketDeserializer.into_inner_eq {T : Type} (self : packets.OkPacketDeserializer T) :
    packets.OkPacketDeserializer.into_inner self = ok self.1 := by
  rfl

/-- `MyDeserialize for OkPacketDeserializer<T>`: `SIZE` is `None`. -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq {T : Type} (inst : packets.OkPacketKind T) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE inst = none := by
  simp [packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE]

/-- `MyDeserialize for OkPacketDeserializer<ResultSetTerminator>`: total; `okPacketRead .resultSetTerminator` (header byte, body, conversion to `OkPacket`). -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_resultSetTerminator (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      ((okPart r).map (fun d => OkPkt.ofPacket d.1), rest.val) = okPacketRead .resultSetTerminator caps.val buf.val ⦄ := by
  exact deser_generic _ .resultSetTerminator 254#u8
    (by rw [← packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq]) (by rfl) caps
    (fun b => packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec h64 caps b) buf

/-- `MyDeserialize for OkPacketDeserializer<OldEofPacket>`: total; `okPacketRead .oldEof` (header byte, body, conversion to `OkPacket`). -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_oldEof (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      ((okPart r).map (fun d => OkPkt.ofPacket d.1), rest.val) = okPacketRead .oldEof caps.val buf.val ⦄ := by
  exact deser_generic _ .oldEof 254#u8
    (by rw [← packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq]) (by rfl) caps
    (fun b => packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec caps b) buf

/-- `MyDeserialize for OkPacketDeserializer<NetworkStreamTerminator>`: total; `okPacketRead .networkStreamTerminator` (header byte, body, conversion to `OkPacket`). -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_networkStreamTerminator (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      ((okPart r).map (fun d => OkPkt.ofPacket d.1), rest.val) = okPacketRead .networkStreamTerminator caps.val buf.val ⦄ := by
  exact deser_generic _ .networkStreamTerminator 254#u8
    (by rw [← packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq]) (by rfl) caps
    (fun b => packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec caps b) buf

/-- `MyDeserialize for OkPacketDeserializer<CommonOkPacket>`: total; `okPacketRead .commonOk` (header byte, body, conversion to `OkPacket`). -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_commonOk (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      ((okPart r).map (fun d => OkPkt.ofPacket d.1), rest.val) = okPacketRead .commonOk caps.val buf.val ⦄ := by
  exact deser_generic _ .commonOk 0#u8
    (by rw [← packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq]) (by rfl) caps
    (fun b => packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec h64 caps b) buf

/-- Round trip: an OK packet (`okPacketEnc 0x00`, in the protocol page's form or, `compact`, as MySQL's `net_send_ok` writes it) is read back by `OkPacketDeserializer<CommonOkPacket>` (as `OkBody.toPkt`), when its status has only known flags and it carries a session state only if both `CLIENT_SESSION_TRACK` and `SERVER_SESSION_STATE_CHANGED` are set. The packet is the whole buffer. -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_commonOk (h64 : Target64) (caps : constants.CapabilityFlags) (b : OkBody) (hb : b.affectedRows < 2 ^ 64 ∧ b.lastInsertId < 2 ^ 64 ∧ b.status < 2 ^ 16 ∧
      statusRead b.status = some b.status ∧ b.warnings < 2 ^ 16)
    (hssi : (hasFlag caps.val CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = [])
    (compact : Bool) (buf : io.ParseBuf) (h : buf.val = okPacketEnc 0x00 caps.val compact b) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      (okPart r).map (fun d => OkPkt.ofPacket d.1) = some b.toPkt ∧ rest.val = [] ⦄ := by
  have hlen := slice_len_lt buf
  rw [h] at hlen
  apply WP.spec_mono (packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_commonOk h64 caps buf)
  rintro ⟨r, rest⟩ hr
  rw [h, okPacketRead_commonOk _ _ _ hb hssi hlen] at hr
  simpa only [Prod.mk.injEq] using hr

/-- Round trip: an OK packet with header `0xFE` (either form) is read back by `OkPacketDeserializer<ResultSetTerminator>`, with affected rows and last insert id 0. -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_resultSetTerminator (h64 : Target64) (caps : constants.CapabilityFlags) (b : OkBody) (hb : b.affectedRows < 2 ^ 64 ∧ b.lastInsertId < 2 ^ 64 ∧ b.status < 2 ^ 16 ∧
      statusRead b.status = some b.status ∧ b.warnings < 2 ^ 16)
    (hssi : (hasFlag caps.val CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = [])
    (compact : Bool) (buf : io.ParseBuf) (h : buf.val = okPacketEnc 0xFE caps.val compact b) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      (okPart r).map (fun d => OkPkt.ofPacket d.1) =
        some { b with affectedRows := 0, lastInsertId := 0 }.toPkt ∧ rest.val = [] ⦄ := by
  have hlen := slice_len_lt buf
  rw [h] at hlen
  apply WP.spec_mono (packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_resultSetTerminator h64 caps buf)
  rintro ⟨r, rest⟩ hr
  rw [h, okPacketRead_rs _ _ _ hb hssi hlen] at hr
  simpa only [Prod.mk.injEq] using hr

/-- Round trip: an EOF packet is read back by `OkPacketDeserializer<OldEofPacket>` when its status has only known flags. -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_oldEof (caps : constants.CapabilityFlags) (w s : Nat) (hw : w < 2 ^ 16) (hs : s < 2 ^ 16)
    (hsk : statusRead s = some s) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = eofPacketEnc w s ++ tail) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      (okPart r).map (fun d => OkPkt.ofPacket d.1) = some ⟨0, none, s, w, none, none⟩ ∧ rest.val = tail ⦄ := by
  have hlen := slice_len_lt buf
  rw [h] at hlen
  apply WP.spec_mono (packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_oldEof caps buf)
  rintro ⟨r, rest⟩ hr
  rw [h, okPacketRead_eof _ (.inl rfl) _ _ _ hw hs hsk] at hr
  simpa only [Prod.mk.injEq] using hr

/-- Round trip: an EOF packet is read back by `OkPacketDeserializer<NetworkStreamTerminator>` when its status has only known flags. -/
theorem packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_networkStreamTerminator (caps : constants.CapabilityFlags) (w s : Nat) (hw : w < 2 ^ 16) (hs : s < 2 ^ 16)
    (hsk : statusRead s = some s) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = eofPacketEnc w s ++ tail) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      (okPart r).map (fun d => OkPkt.ofPacket d.1) = some ⟨0, none, s, w, none, none⟩ ∧ rest.val = tail ⦄ := by
  have hlen := slice_len_lt buf
  rw [h] at hlen
  apply WP.spec_mono (packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_networkStreamTerminator caps buf)
  rintro ⟨r, rest⟩ hr
  rw [h, okPacketRead_eof _ (.inr rfl) _ _ _ hw hs hsk] at hr
  simpa only [Prod.mk.injEq] using hr

end mysql_common
