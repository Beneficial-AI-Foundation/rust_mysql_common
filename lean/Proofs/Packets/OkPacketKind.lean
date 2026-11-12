import Defs
import Proofs.Util.PacketsOkErr

/-! Statements for `trait OkPacketKind and its impls` (spec file: `Specs/Packets.lean`). Helper lemmas: `Proofs/Util/PacketsOkErr.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts

namespace mysql_common

/-- `HEADER` is `0xFE`. -/
theorem packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq :
    packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER = 254#u8 := by
  simp [packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER]

/-- `HEADER` is `0xFE`. -/
theorem packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq :
    packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER = 254#u8 := by
  simp [packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER]

/-- `HEADER` is `0xFE`. -/
theorem packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq :
    packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER = 254#u8 := by
  simp [packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER]

/-- `HEADER` is `0x00`. -/
theorem packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq :
    packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER = 0#u8 := by
  simp [packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER]

/-- `OkPacketKind::parse_body for ResultSetTerminator`: total; the OK packet fields after the header (`rsTerminatorBodyRead`): affected rows and last insert id are read but reported as 0. -/
@[step]
theorem packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body caps buf ⦃ r rest =>
      ((okPart r).map OkBody.ofBody, rest.val) = rsTerminatorBodyRead caps.val buf.val ⦄ := by
  unfold packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body rsTerminatorBodyRead okBodyRead
  step with misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec as ⟨r, buf1, h1⟩
  rw [← h1]
  cases r with
  | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok ar =>
    simp only [CoreOpsTry.branch, okPart_Ok, Option.map_some]
    step with misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec as ⟨r1, buf2, h2⟩
    rw [← h2]
    cases r1 with
    | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok li =>
      simp only [okPart_Ok, Option.map_some]
      step with parse_usize_spec as ⟨r2, buf3, h3⟩
      unfold okStatusRead
      split_ifs at h3 with hlen
      · obtain ⟨h3a, h3b⟩ := h3
        have hlen' : (↑buf2 : List U8).length ≥ 4 := hlen
        rw [ite_eq_right (by omega)]
        cases r2 with
        | Err e => simp at h3a
        | Ok pb =>
        simp only [okPart_Ok, Option.map_some, Option.some.injEq] at h3a
        simp only
        step with parse_unchecked_status_spec as ⟨r3, sbuf, h4a, h4b⟩
        have e1 : List.take 2 (↑pb : List U8) = List.take 2 (↑buf2 : List U8) := by
          rw [h3a, List.take_take]; simp
        rw [e1] at h4a
        cases r3 with
        | Err e =>
          simp only [okPart_Err, Option.map_none] at h4a
          rw [← h4a, ← h3b]
          simp [CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok st =>
          simp only [okPart_Ok, Option.map_some] at h4a
          rw [← h4a]
          simp only [Option.map_some]
          step with parse_unchecked_leu16_spec as ⟨r4, buf4, h5a, h5b⟩
          · simp only [Slice.length]; rw [h4b, h3a]; simp; omega
          cases r4 with
          | Err e => simp at h5a
          | Ok w =>
          simp only [okPart_Ok, Option.map_some, Option.some.injEq] at h5a
          have e2 : leNat (List.take 2 (↑sbuf : List U8)) = leNat (List.take 2 (List.drop 2 (↑buf2 : List U8))) := by
            rw [h4b, h3a]; simp [List.drop_take, List.take_take]
          rw [e2] at h5a
          simp only
          rw [← h3b]
          step with caps_contains_spec as ⟨b, hb⟩
          unfold okTailRead
          simp only [CLIENT_SESSION_TRACK_val] at hb
          subst hb
          by_cases hst : hasFlag (↑caps) CLIENT_SESSION_TRACK = true
          · simp only [hst, ite_true]
            step with io.ParseBuf.is_empty_spec as ⟨b1, hb1⟩
            by_cases hemp : (↑buf3 : List U8) = []
            · have hb1' : b1 = true := by simpa [hemp] using hb1
              subst hb1'
              simp only [ite_true]
              step with rawbytes_default_spec as ⟨rb, hrb⟩
              step with rawint_new_spec as ⟨ri, hri⟩
              simp [hri, hemp, OkBody.ofBody, hrb, h5a]
            · have hb1' : b1 = false := by simpa [hemp] using hb1
              subst hb1'
              simp only [Bool.false_eq_true, ite_false]
              step with parse_lenenc_bytes_spec h64 as ⟨r5, buf5, h6⟩
              simp only [ne_eq, hemp, not_false_eq_true, ite_true]
              rw [← h6]
              cases r5 with
              | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok rb =>
                simp only [okPart_Ok, Option.map_some]
                step with const_deref_spec as ⟨sf, hsf⟩
                step with status_contains_spec as ⟨b2, hb2⟩
                subst hsf hb2
                simp only [SERVER_SESSION_STATE_CHANGED_val]
                by_cases hss : hasFlag (↑st.1) SERVER_SESSION_STATE_CHANGED = true
                · simp only [hss, ite_true]
                  step with parse_lenenc_bytes_spec h64 as ⟨r6, buf6, h7⟩
                  rw [← h7]
                  cases r6 with
                  | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
                  | Ok rb1 =>
                    simp only
                    step with rawint_new_spec as ⟨ri, hri⟩
                    simp [hri, OkBody.ofBody, h5a]
                · simp only [hss, Bool.false_eq_true, ite_false]
                  step with rawbytes_default_spec as ⟨rb1, hrb1⟩
                  step with rawint_new_spec as ⟨ri, hri⟩
                  simp [hri, OkBody.ofBody, h5a, hrb1]
          · simp only [hst, Bool.false_eq_true, ite_false]
            step with io.ParseBuf.is_empty_spec as ⟨b1, hb1⟩
            by_cases hemp : (↑buf3 : List U8) = []
            · have hb1' : b1 = true := by simpa [hemp] using hb1
              subst hb1'
              simp only [ite_true]
              step with rawbytes_default_spec as ⟨rb, hrb⟩
              step with rawint_new_spec as ⟨ri, hri⟩
              simp [hri, hemp, OkBody.ofBody, hrb, h5a]
            · have hb1' : b1 = false := by simpa [hemp] using hb1
              subst hb1'
              simp only [Bool.false_eq_true, ite_false]
              obtain ⟨x, t, hxt⟩ : ∃ x t, (↑buf3 : List U8) = x :: t := by
                cases h : (↑buf3 : List U8) with
                | nil => exact absurd h hemp
                | cons x t => exact ⟨x, t, rfl⟩
              step as ⟨i, hi⟩
              have hix : i = x := by simp [hi, hxt]
              subst hix
              simp only [false_and, ite_false, hxt]
              by_cases hx : i > 0#u8
              · have hx' : 0 < i.val := by scalar_tac
                simp only [hx, ite_true, hx']
                step with parse_lenenc_bytes_spec h64 as ⟨r5, buf5, h6⟩
                rw [hxt] at h6
                rw [← h6]
                cases r5 with
                | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
                | Ok rb =>
                  simp only [okPart_Ok, Option.map_some]
                  step with rawbytes_default_spec as ⟨rb1, hrb1⟩
                  step with rawint_new_spec as ⟨ri, hri⟩
                  simp [hri, OkBody.ofBody, h5a, hrb1]
              · have hx' : ¬ 0 < i.val := by scalar_tac
                simp only [hx, ite_false, hx']
                step with rawbytes_default_spec as ⟨rb, hrb⟩
                step with rawint_new_spec as ⟨ri, hri⟩
                simp [hri, OkBody.ofBody, h5a, hrb, hxt]
      · obtain ⟨h3a, rfl⟩ := h3
        have hlen' : ¬ (↑buf3 : List U8).length ≥ 4 := hlen
        rw [ite_eq_left (by omega)]
        cases r2 with
        | Ok _ => simp at h3a
        | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]

/-- `OkPacketKind::parse_body for OldEofPacket`: total; `warnings` and `status_flags` (`eofBodyRead`). -/
@[step]
theorem packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body caps buf ⦃ r rest =>
      ((okPart r).map OkBody.ofBody, rest.val) = eofBodyRead buf.val ⦄ := by
  unfold packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body
  step with parse_usize_spec as ⟨r, buf1, h1⟩
  split_ifs at h1 with hlen
  · obtain ⟨hr, hb1⟩ := h1
    cases r with
    | Err e => simp [okPart] at hr
    | Ok pb =>
      simp only [okPart, Option.map_some, Option.some.injEq] at hr
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      step with parse_unchecked_leu16_spec as ⟨r1, buf2, h2a, h2b⟩
      cases r1 with
      | Err e => simp [okPart] at h2a
      | Ok w =>
        simp only [okPart, Option.map_some, Option.some.injEq] at h2a
        simp only
        step with parse_unchecked_status_spec as ⟨r2, buf3, h3a, h3b⟩
        · have := hlen; simp only [Slice.length] at *; rw [h2b, hr]; simp; omega
        have hl : (↑buf : List U8).length ≥ 4 := hlen
        have e1 : List.take 2 (↑buf2 : List U8) = List.take 2 (List.drop 2 (↑buf : List U8)) := by
          rw [h2b, hr]; simp [List.drop_take]
        have e2 : List.take 2 (↑pb : List U8) = List.take 2 (↑buf : List U8) := by
          rw [hr, List.take_take]; simp
        unfold eofBodyRead
        rw [ite_eq_right (by simp only [Slice.length] at hlen; omega)]
        cases r2 with
        | Err e =>
          simp [okPart,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h3a ⊢
          rw [e1] at h3a; rw [← h3a, hb1]; simp
        | Ok st =>
          simp [okPart] at h3a ⊢
          step*
          rw [e1] at h3a; rw [← h3a]
          simp_all [OkBody.ofBody]
  · obtain ⟨hr, rfl⟩ := h1
    cases r with
    | Ok _ => simp at hr
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, eofBodyRead]
      simp only [Slice.length] at hlen; omega

/-- `OkPacketKind::parse_body for NetworkStreamTerminator`: total; as `OldEofPacket` (`eofBodyRead`). -/
@[step]
theorem packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body caps buf ⦃ r rest =>
      ((okPart r).map OkBody.ofBody, rest.val) = eofBodyRead buf.val ⦄ := by
  unfold packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body
  exact packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec caps buf

/-- `OkPacketKind::parse_body for CommonOkPacket`: total; the OK packet fields after the header (`okBodyRead`). -/
@[step]
theorem packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body caps buf ⦃ r rest =>
      ((okPart r).map OkBody.ofBody, rest.val) = okBodyRead caps.val buf.val ⦄ := by
  unfold packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body okBodyRead
  step with misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec as ⟨r, buf1, h1⟩
  rw [← h1]
  cases r with
  | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok ar =>
    simp only [CoreOpsTry.branch, okPart_Ok, Option.map_some]
    step with misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec as ⟨r1, buf2, h2⟩
    rw [← h2]
    cases r1 with
    | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok li =>
      simp only [okPart_Ok, Option.map_some]
      step with parse_usize_spec as ⟨r2, buf3, h3⟩
      unfold okStatusRead
      split_ifs at h3 with hlen
      · obtain ⟨h3a, h3b⟩ := h3
        have hlen' : (↑buf2 : List U8).length ≥ 4 := hlen
        rw [ite_eq_right (by omega)]
        cases r2 with
        | Err e => simp at h3a
        | Ok pb =>
        simp only [okPart_Ok, Option.map_some, Option.some.injEq] at h3a
        simp only
        step with parse_unchecked_status_spec as ⟨r3, sbuf, h4a, h4b⟩
        have e1 : List.take 2 (↑pb : List U8) = List.take 2 (↑buf2 : List U8) := by
          rw [h3a, List.take_take]; simp
        rw [e1] at h4a
        cases r3 with
        | Err e =>
          simp only [okPart_Err, Option.map_none] at h4a
          rw [← h4a, ← h3b]
          simp [CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok st =>
          simp only [okPart_Ok, Option.map_some] at h4a
          rw [← h4a]
          simp only [Option.map_some]
          step with parse_unchecked_leu16_spec as ⟨r4, buf4, h5a, h5b⟩
          · simp only [Slice.length]; rw [h4b, h3a]; simp; omega
          cases r4 with
          | Err e => simp at h5a
          | Ok w =>
          simp only [okPart_Ok, Option.map_some, Option.some.injEq] at h5a
          have e2 : leNat (List.take 2 (↑sbuf : List U8)) = leNat (List.take 2 (List.drop 2 (↑buf2 : List U8))) := by
            rw [h4b, h3a]; simp [List.drop_take, List.take_take]
          rw [e2] at h5a
          simp only
          rw [← h3b]
          step with caps_contains_spec as ⟨b, hb⟩
          unfold okTailRead
          simp only [CLIENT_SESSION_TRACK_val] at hb
          subst hb
          by_cases hst : hasFlag (↑caps) CLIENT_SESSION_TRACK = true
          · simp only [hst, ite_true]
            step with io.ParseBuf.is_empty_spec as ⟨b1, hb1⟩
            by_cases hemp : (↑buf3 : List U8) = []
            · have hb1' : b1 = true := by simpa [hemp] using hb1
              subst hb1'
              simp only [ite_true]
              step with rawbytes_default_spec as ⟨rb, hrb⟩
              simp [hemp, OkBody.ofBody, hrb, h5a]
            · have hb1' : b1 = false := by simpa [hemp] using hb1
              subst hb1'
              simp only [Bool.false_eq_true, ite_false]
              step with parse_lenenc_bytes_spec h64 as ⟨r5, buf5, h6⟩
              simp only [ne_eq, hemp, not_false_eq_true, ite_true]
              rw [← h6]
              cases r5 with
              | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok rb =>
                simp only [okPart_Ok, Option.map_some]
                step with const_deref_spec as ⟨sf, hsf⟩
                step with status_contains_spec as ⟨b2, hb2⟩
                subst hsf hb2
                simp only [SERVER_SESSION_STATE_CHANGED_val]
                by_cases hss : hasFlag (↑st.1) SERVER_SESSION_STATE_CHANGED = true
                · simp only [hss, ite_true]
                  step with parse_lenenc_bytes_spec h64 as ⟨r6, buf6, h7⟩
                  rw [← h7]
                  cases r6 with
                  | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
                  | Ok rb1 =>
                    simp [OkBody.ofBody, h5a]
                · simp only [hss, Bool.false_eq_true, ite_false]
                  step with rawbytes_default_spec as ⟨rb1, hrb1⟩
                  simp [OkBody.ofBody, h5a, hrb1]
          · simp only [hst, Bool.false_eq_true, ite_false]
            step with io.ParseBuf.is_empty_spec as ⟨b1, hb1⟩
            by_cases hemp : (↑buf3 : List U8) = []
            · have hb1' : b1 = true := by simpa [hemp] using hb1
              subst hb1'
              simp only [ite_true]
              step with rawbytes_default_spec as ⟨rb, hrb⟩
              simp [hemp, OkBody.ofBody, hrb, h5a]
            · have hb1' : b1 = false := by simpa [hemp] using hb1
              subst hb1'
              simp only [Bool.false_eq_true, ite_false]
              obtain ⟨x, t, hxt⟩ : ∃ x t, (↑buf3 : List U8) = x :: t := by
                cases h : (↑buf3 : List U8) with
                | nil => exact absurd h hemp
                | cons x t => exact ⟨x, t, rfl⟩
              step as ⟨i, hi⟩
              have hix : i = x := by simp [hi, hxt]
              subst hix
              simp only [false_and, ite_false, hxt]
              by_cases hx : i > 0#u8
              · have hx' : 0 < i.val := by scalar_tac
                simp only [hx, ite_true, hx']
                step with parse_lenenc_bytes_spec h64 as ⟨r5, buf5, h6⟩
                rw [hxt] at h6
                rw [← h6]
                cases r5 with
                | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
                | Ok rb =>
                  simp only [okPart_Ok, Option.map_some]
                  step with rawbytes_default_spec as ⟨rb1, hrb1⟩
                  simp [OkBody.ofBody, h5a, hrb1]
              · have hx' : ¬ 0 < i.val := by scalar_tac
                simp only [hx, ite_false, hx']
                step with rawbytes_default_spec as ⟨rb, hrb⟩
                simp [OkBody.ofBody, h5a, hrb, hxt]
      · obtain ⟨h3a, rfl⟩ := h3
        have hlen' : ¬ (↑buf3 : List U8).length ≥ 4 := hlen
        rw [ite_eq_left (by omega)]
        cases r2 with
        | Ok _ => simp at h3a
        | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]

end mysql_common
