import Defs
import Proofs.Util.PacketsOkErr
import Proofs.Packets.ProgressReport
import Proofs.Packets.ServerError
import Proofs.Packets.SqlState

/-! Statements for `enum ErrPacket and its impls` (spec file: `Specs/Packets.lean`). Helper lemmas: `Proofs/Util/PacketsOkErr.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts

namespace mysql_common

private theorem parse_progress_spec (h64 : Target64) (buf : io.ParseBuf) :
    io.ParseBuf.parse packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple buf () ⦃ r rest =>
      ((okPart r).map Progress.of, rest.val) = progressRead buf.val ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq])]
  exact packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf

private theorem parse_server_error_spec (code : U16) (p41 : Bool) (buf : io.ParseBuf) :
    io.ParseBuf.parse packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool buf (code, p41) ⦃ r rest =>
      ((okPart r).map ErrPkt.ofServerError, rest.val) = serverErrorRead code.val p41 buf.val ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.SIZE_eq])]
  exact packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.deserialize_spec code p41 buf

private theorem parse_unchecked_err_header_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple
        255#u8 packets.InvalidErrPacketHeader.Insts.CoreErrorError
        packets.InvalidErrPacketHeader.Insts.CoreDefaultDefault) buf () ⦃ r rest =>
      ((okPart r).isSome ↔ leNat (buf.val.take 1) = 255) ∧ rest.val = buf.val.drop 1 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  exact misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec 255#u8
    packets.InvalidErrPacketHeader.Insts.CoreErrorError packets.InvalidErrPacketHeader.Insts.CoreDefaultDefault
    ((WP.spec_ok _).mpr trivial) buf h

private theorem server_error_ser (self : packets.ServerError) (buf : alloc.vec.Vec U8)
    (h : buf.length + (match self.state with | some s => byte 0x23 :: s.state.val | none => []).length
      + (cowList self.message.1).length ≤ Usize.max) :
    packets.ServerError.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ (match self.state with | some s => byte 0x23 :: s.state.val | none => [])
        ++ cowList self.message.1 ⦄ := by
  unfold packets.ServerError.Insts.Mysql_commonProtoMySerialize.serialize
  cases hs : self.state with
  | none =>
    simp only [hs, List.length_nil, add_zero] at h
    simp only
    apply WP.spec_mono (eof_ser _ _ (by omega))
    intro b hb; simp [hb]
  | some st =>
    simp only [hs, List.length_cons, Std.Array.length_eq] at h
    simp only
    step with packets.SqlState.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨buf1, h1⟩
    apply WP.spec_mono (eof_ser _ _ (by
      have : buf1.length = buf.length + 6 := by
        simp [alloc.vec.Vec.length, h1]
      have h5 : ((5#usize : Usize) : Nat) = 5 := rfl
      omega))
    intro b hb; simp [hb, h1]

private theorem constu8_new_spec (T : Type) (N : U8) : misc.raw.int.ConstU8.new T N ⦃ _ => True ⦄ := by
  unfold misc.raw.int.ConstU8.new; exact (WP.spec_ok _).mpr trivial

private theorem errPacketRead_enc (caps : Nat) (e : packets.ErrPacket) (hc : errCompatible caps (ErrPkt.of e))
    (hlen : (errPacketEnc (ErrPkt.of e)).length < 2 ^ 64) :
    errPacketRead caps (errPacketEnc (ErrPkt.of e)) = (some (ErrPkt.of e), []) := by
  cases e with
  | Error se =>
    rcases se with ⟨code, state, msg⟩
    simp only [ErrPkt.of, ErrPkt.ofServerError, errCompatible] at hc ⊢
    obtain ⟨hs, hcode⟩ := hc
    have hcv : code.1.val < 2 ^ 16 := by scalar_tac
    have hl := leNat_leBytes 2 code.1.val
    rw [Nat.mod_eq_of_lt (by simpa using hcv)] at hl
    have hc01 : leBytes 2 code.1.val = [byte code.1.val, byte (code.1.val / 256)] := rfl
    simp only [errPacketEnc]
    unfold errPacketRead
    rw [hc01] at hl ⊢
    simp only [List.cons_append, List.nil_append, List.length_cons, List.drop_succ_cons, List.drop_zero,
      List.take_succ_cons, List.take_zero, List.getD_cons_zero, hl, byte_val]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [ite_eq_right (by
      rintro ⟨h1, h2⟩
      rcases hcode with h3 | h3
      · exact h3 h1
      · simp [h3] at h2)]
    cases state with
    | none =>
      have hp : hasFlag caps CLIENT_PROTOCOL_41 = false := by simpa using hs
      simp [serverErrorRead, hp]
    | some st =>
      have hp : hasFlag caps CLIENT_PROTOCOL_41 = true := by simpa using hs
      have h5 : st.state.val.length = 5 := by simp
      simp [serverErrorRead, hp, byte_val, h5]
  | Progress pr =>
    simp only [ErrPkt.of, errCompatible] at hc ⊢
    obtain ⟨hp, hpr⟩ := hc
    simp only [errPacketEnc]
    unfold errPacketRead
    have hc01 : leBytes 2 0xFFFF = [byte 0xFFFF, byte (0xFFFF / 256)] := rfl
    simp only [hc01, List.cons_append, List.nil_append, List.length_cons, List.drop_succ_cons, List.drop_zero,
      List.take_succ_cons, List.take_zero, List.getD_cons_zero, byte_val, leNat]
    rw [ite_eq_right (by omega)]
    simp only [ErrPkt.of, errPacketEnc, hc01, List.length_cons, List.cons_append, List.nil_append] at hlen
    have hi : (Progress.of pr).info.length < 2 ^ 64 := by
      simp only [progressEnc, lenencStr, List.length_cons, List.length_append] at hlen; omega
    rw [show progressEnc (Progress.of pr) = progressEnc (Progress.of pr) ++ [] by simp,
      progressRead_enc _ _ (by simp [Progress.of]; scalar_tac) (by simp [Progress.of]; scalar_tac) hpr hi]
    simp [hp]



/-- `is_error`: an error, not a progress report. -/
theorem packets.ErrPacket.is_error_spec (self : packets.ErrPacket) :
    packets.ErrPacket.is_error self ⦃ b => (b ↔ ∃ e, self = .Error e) ⦄ := by
  unfold packets.ErrPacket.is_error
  cases self <;> simp

/-- `is_progress_report`: a progress report. -/
theorem packets.ErrPacket.is_progress_report_spec (self : packets.ErrPacket) :
    packets.ErrPacket.is_progress_report self ⦃ b => (b ↔ ∃ p, self = .Progress p) ⦄ := by
  unfold packets.ErrPacket.is_progress_report packets.ErrPacket.is_error
  cases self <;> simp

/-- `progress_report`: the report. -/
theorem packets.ErrPacket.progress_report_progress (p : packets.ProgressReport) :
    packets.ErrPacket.progress_report (.Progress p) = ok p := by
  rfl

/-- `progress_report` panics on an error (documented). -/
theorem packets.ErrPacket.progress_report_error (e : packets.ServerError) :
    packets.ErrPacket.progress_report (.Error e) = fail .panic := by
  rfl

/-- `server_error`: the error. -/
theorem packets.ErrPacket.server_error_error (e : packets.ServerError) :
    packets.ErrPacket.server_error (.Error e) = ok e := by
  rfl

/-- `server_error` panics on a progress report (documented). -/
theorem packets.ErrPacket.server_error_progress (p : packets.ProgressReport) :
    packets.ErrPacket.server_error (.Progress p) = fail .panic := by
  rfl

/-- `MyDeserialize for ErrPacket`: `SIZE` is `None`. -/
theorem packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq :
    packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE = none := by
  simp [packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE]

/-- `MyDeserialize for ErrPacket`: total; `errPacketRead` (header, code, then a progress report or the SQL state and message). -/
@[step]
theorem packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      ((okPart r).map ErrPkt.of, rest.val) = errPacketRead caps.val buf.val ⦄ := by
  unfold packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize errPacketRead
  step with parse_usize_spec as ⟨r, buf1, h1⟩
  split_ifs at h1 with hl
  · obtain ⟨h1a, h1b⟩ := h1
    have hl' : (↑buf : List U8).length ≥ 3 := hl
    rw [ite_eq_right (by omega)]
    obtain ⟨a0, a1, a2, rest, hbuf⟩ : ∃ a0 a1 a2 rest, (↑buf : List U8) = a0 :: a1 :: a2 :: rest := by
      match h : (↑buf : List U8), hl' with
      | a0 :: a1 :: a2 :: rest, _ => exact ⟨a0, a1, a2, rest, rfl⟩
    rw [hbuf] at h1a h1b ⊢
    cases r with
    | Err e => simp at h1a
    | Ok pb =>
      simp at h1a h1b
      simp only [CoreOpsTry.branch, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
        List.take_zero, List.getD_cons_zero]
      step with parse_unchecked_err_header_spec as ⟨r1, sbuf, h2a, h2b⟩
      rw [h1a] at h2a h2b
      simp [leNat] at h2a h2b
      cases r1 with
      | Err e =>
        have ha : a0.val ≠ 0xFF := by intro h; simp [h] at h2a
        rw [ite_eq_left ha, ← h1b]
        simp [CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok hd =>
        have ha : a0.val = 0xFF := by simpa using h2a
        rw [ite_eq_right (by simp [ha])]
        simp only
        step with parse_unchecked_leu16_spec as ⟨r2, sbuf2, h3a, h3b⟩
        cases r2 with
        | Err e => simp at h3a
        | Ok cv =>
        simp only [okPart_Ok, Option.map_some, Option.some.injEq, h2b] at h3a
        simp only [List.take_succ_cons, List.take_zero, leNat] at h3a
        simp only
        step with rawint_deref_spec as ⟨i, hi⟩
        subst hi
        rw [← h1b]
        have hcode : leNat [a1, a2] = cv.1.val := by simp [leNat, h3a]
        rw [hcode]
        by_cases hff : cv.1 = 65535#u16
        · have hffv : cv.1.val = 0xFFFF := by rw [hff]; rfl
          rw [ite_eq_left hff]
          step with caps_contains_spec as ⟨b, hb⟩
          subst hb
          simp only [CLIENT_PROGRESS_OBSOLETE_val]
          by_cases hp : hasFlag (↑caps) CLIENT_PROGRESS_OBSOLETE = true
          · rw [ite_eq_left hp, ite_eq_left ⟨hffv, hp⟩]
            step with parse_progress_spec h64 as ⟨r3, buf2, h4⟩
            rw [← h4]
            cases r3 with
            | Err e => simp
            | Ok pr => simp [ErrPkt.of]
          · rw [ite_eq_right hp, ite_eq_right (by simp [hp])]
            step with caps_contains_spec as ⟨b1, hb1⟩
            subst hb1
            simp only [CLIENT_PROTOCOL_41_val]
            step with parse_server_error_spec as ⟨r3, buf2, h4⟩
            rw [← h4]
            cases r3 with
            | Err e => simp
            | Ok se => simp [ErrPkt.of]
        · have hffv : cv.1.val ≠ 0xFFFF := by intro h; apply hff; scalar_tac
          rw [ite_eq_right hff, ite_eq_right (by simp [hffv])]
          step with caps_contains_spec as ⟨b1, hb1⟩
          subst hb1
          simp only [CLIENT_PROTOCOL_41_val]
          step with parse_server_error_spec as ⟨r3, buf2, h4⟩
          rw [← h4]
          cases r3 with
          | Err e => simp
          | Ok se => simp [ErrPkt.of]
  · obtain ⟨h1a, rfl⟩ := h1
    rw [ite_eq_left (by simp only [Slice.length] at hl; omega)]
    cases r with
    | Ok _ => simp at h1a
    | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]

/-- `MySerialize for ErrPacket`: appends `errPacketEnc` (the progress truncated to 3 bytes). -/
@[step]
theorem packets.ErrPacket.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ErrPacket) (buf : alloc.vec.Vec U8)
    (h : buf.length + (errPacketEnc (ErrPkt.of self)).length ≤ Usize.max) :
    packets.ErrPacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ errPacketEnc (ErrPkt.of self) ⦄ := by
  unfold packets.ErrPacket.Insts.Mysql_commonProtoMySerialize.serialize
  have h1l : 1 ≤ (errPacketEnc (ErrPkt.of self)).length := by
    cases self with
    | Error se => simp [ErrPkt.of, ErrPkt.ofServerError, errPacketEnc]
    | Progress p => simp [ErrPkt.of, errPacketEnc]
  step with constu8_new_spec
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨buf1, h1⟩
  cases self with
  | Error se =>
    rcases se with ⟨code, state, msg⟩
    simp only
    simp only [errPacketEnc, ErrPkt.of, ErrPkt.ofServerError, List.length_cons, List.length_append,
      length_leBytes, vec_len] at h
    step with rawint_leu16_ser as ⟨buf2, h2⟩
    · simp [h1]; omega
    apply WP.spec_mono (server_error_ser _ _ (by
      cases state <;> simp_all <;> omega))
    intro b hb
    rw [hb, h2, h1]
    cases state <;> simp [errPacketEnc, ErrPkt.of, ErrPkt.ofServerError] <;> rfl
  | Progress pr =>
    simp only
    simp only [errPacketEnc, ErrPkt.of, List.length_cons, List.length_append, length_leBytes, vec_len] at h
    step with rawint_new_spec as ⟨ri, hri⟩
    step with rawint_leu16_ser as ⟨buf2, h2⟩
    · simp [h1]; omega
    apply WP.spec_mono (packets.ProgressReport.Insts.Mysql_commonProtoMySerialize.serialize_spec _ _ (by
      simp [h2, h1]; omega))
    intro b hb
    rw [hb, h2, h1, hri]
    simp [errPacketEnc, ErrPkt.of]
    rfl

/-- Round trip: an ERR packet is read back when it fits the capabilities (`errCompatible`: SQL state iff `CLIENT_PROTOCOL_41`, no error code `0xFFFF` under `CLIENT_PROGRESS_OBSOLETE`, progress reports only under it). The packet is the whole buffer (the message extends to its end). -/
theorem packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip (h64 : Target64) (caps : constants.CapabilityFlags) (e : packets.ErrPacket)
    (hc : errCompatible caps.val (ErrPkt.of e)) (buf : io.ParseBuf) (h : buf.val = errPacketEnc (ErrPkt.of e)) :
    packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      (okPart r).map ErrPkt.of = some (ErrPkt.of e) ∧ rest.val = [] ⦄ := by
  have hlen := slice_len_lt buf
  rw [h] at hlen
  apply WP.spec_mono (packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec h64 caps buf)
  rintro ⟨r, rest⟩ hr
  rw [h, errPacketRead_enc _ _ hc hlen] at hr
  simpa only [Prod.mk.injEq] using hr

end mysql_common
