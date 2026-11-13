import Defs
import Proofs.Util.PacketsColStmt
import Proofs.Io.ParseBuf
import Proofs.Packets.SessionStateInfo

/-! Statements for `OkPacket::session_state_info` (spec file: `Specs/Packets/StmtBinlog.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

private theorem lenencIntDecode_length (bs : List U8) (n : Nat) (r : List U8)
    (h : lenencIntDecode bs = some (n, r)) : r.length ≤ bs.length := by
  cases bs with
  | nil => simp [lenencIntDecode] at h
  | cons b rest =>
    simp only [lenencIntDecode, readLE] at h
    split_ifs at h <;> simp at h <;> (obtain ⟨_, rfl⟩ := h; simp) <;> omega

private theorem checkedLenencInt_snd_length (bs : List U8) :
    (checkedLenencInt bs).2.length ≤ bs.length := by
  unfold checkedLenencInt
  split
  · simp
  · rename_i b rest
    split_ifs
    · simp
    · split
      · rename_i n rest' h
        exact lenencIntDecode_length _ _ _ h
      · simp

private theorem checkedLenencStr_snd_length (bs : List U8) :
    (checkedLenencStr bs).2.length ≤ bs.length := by
  have := checkedLenencInt_snd_length bs
  unfold checkedLenencStr
  split
  · rename_i rest h; rw [h] at this; exact this
  · rename_i n rest h
    rw [h] at this
    simp only at this
    split_ifs <;> simp <;> omega

private theorem ssInfoRead_snd_length (b : U8) (bs : List U8) :
    (ssInfoRead (b :: bs)).2.length < (b :: bs).length := by
  have := checkedLenencStr_snd_length bs
  simp only [ssInfoRead]
  split
  · simp
  · split <;> simp_all

private theorem parse_ssi (h64 : Target64) (buf : io.ParseBuf) :
    io.ParseBuf.parse packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple buf () ⦃ r rest =>
      ((okPart r).map SsInfo.of, rest.val) = ssInfoRead buf.val ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq])]
  exact packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf

private theorem parse_infos_spec (h64 : Target64) (n : Nat) :
    ∀ (data : io.ParseBuf) (entries : alloc.vec.Vec packets.SessionStateInfo),
      data.val.length ≤ n → entries.val.length + data.val.length ≤ Usize.max →
      packets.parse_session_state_infos data entries ⦃ r _ =>
        (okPart r).map (fun v => v.val.map SsInfo.of) =
          (ssInfosFuel n data.val).map (entries.val.map SsInfo.of ++ ·) ⦄ := by
  induction n with
  | zero =>
    intro data entries hn _
    have hd : data.val = [] := List.eq_nil_of_length_eq_zero (by omega)
    unfold packets.parse_session_state_infos
    step with io.ParseBuf.is_empty_spec as ⟨ b, hb ⟩
    have : b = true := by simpa using hb.mpr hd
    simp [this, hd, ssInfosFuel, okPart]
  | succ m ih =>
    intro data entries hn hlen
    unfold packets.parse_session_state_infos
    step with io.ParseBuf.is_empty_spec as ⟨ b, hb ⟩
    cases b with
    | true =>
      have hd : data.val = [] := hb.mp rfl
      simp [hd, ssInfosFuel, okPart]
    | false =>
      have hd : data.val ≠ [] := fun h => by simpa using hb.mpr h
      obtain ⟨x, t, hxt⟩ := List.exists_cons_of_ne_nil hd
      simp only [Bool.false_eq_true, ite_false]
      step with parse_ssi h64 data as ⟨ r, data1, hr ⟩
      have hl := ssInfoRead_snd_length x t
      rw [hxt] at hr
      rw [← hr] at hl
      simp only [hxt, ssInfosFuel, ← hr]
      cases r with
      | Ok ssi =>
        simp only [okPart, Option.map_some]
        step as ⟨ entries1, he1 ⟩
        apply WP.spec_mono (ih data1 entries1 (by simp [hxt] at hl hn; omega)
          (by simp [hxt, he1] at hl hlen ⊢; omega))
        rintro ⟨r', rest'⟩ h'
        simp only [WP.uncurry', okPart] at h' ⊢
        rw [h']
        cases ssInfosFuel m data1.val <;> simp [he1]
      | Err e => simp [okPart]

/-- `OkPacket::session_state_info`: total; no entries without session state, otherwise the
    entries of the session state string read until it is exhausted (`ssInfos`), an error if one
    is malformed. -/
theorem packets.OkPacket.impl.session_state_info_spec (h64 : Target64) (self : packets.OkPacket) :
    packets.OkPacket.impl.session_state_info self ⦃ r =>
      (okPart r).map (fun v => v.val.map SsInfo.of) =
        match self.session_state_info with
        | none => some []
        | some rb => ssInfos (cowList rb.1) ⦄ := by
  unfold packets.OkPacket.impl.session_state_info packets.OkPacket.session_state_info_ref
  cases self.session_state_info with
  | none => simp [okPart]
  | some rb =>
    simp only
    step with PCSUtil.lenenc_as_bytes as ⟨ s, hs ⟩
    step with parse_infos_spec h64 s.val.length s (alloc.vec.Vec.new packets.SessionStateInfo)
      le_rfl (by simp) as ⟨ r, rest, hr ⟩
    simp only [ssInfos, ← hs]
    rw [hr]
    cases ssInfosFuel s.val.length s.val <;> simp

end mysql_common
