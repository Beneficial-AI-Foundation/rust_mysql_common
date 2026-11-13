import Defs
import Proofs.Util.ConnHandshake
import Proofs.Packets.AuthPlugin

/-! Statements for `struct HandshakePacket and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.ConnHSUtil
open core.result.Result.Insts

namespace mysql_common

attribute [local step] barebytes_len parse_barebytes_spec io.ParseBuf.eat_all_spec

local macro "lenTac" : tactic => `(tactic| (simp only [alloc.vec.Vec.length] at *; simp [*, PBUtil.length_leBytes] at *; omega))

/-- `MyDeserialize for HandshakePacket`: `SIZE` is `None`. -/
theorem packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  unfold packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

private theorem plug_tail_spec (sl : Slice U8) (b5 : io.ParseBuf) :
    ((if sl.len > 0#usize then do
            let i10 ← sl.len - 1#usize
            let i11 ← sl.index_usize i10
            let (c1, pd1) ←
              if i11 = 0#u8 then do
                  let s ← core.slice.index.SliceIndexRangeToUsizeSlice.index { «end» := i10 } sl
                  let rb2 ←
                    misc.raw.bytes.RawBytes.new misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple
                        (core.convert.IntoFrom
                          (alloc.borrow.CowASliceVec.Insts.CoreConvertFromSharedASlice core.clone.CloneU8))
                        s
                  let (c2, pd2) := rb2
                  ok (c2, pd2)
                else do
                  let rb2 ←
                    misc.raw.bytes.RawBytes.new misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple
                        (core.convert.IntoFrom
                          (alloc.borrow.CowASliceVec.Insts.CoreConvertFromSharedASlice core.clone.CloneU8))
                        sl
                  let (c2, pd2) := rb2
                  ok (c2, pd2)
            ok (b5, c1, pd1)
          else do
            let rb2 ←
              misc.raw.bytes.RawBytes.new misc.raw.bytes.NullBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple
                  (core.convert.IntoFrom
                    (alloc.borrow.CowASliceVec.Insts.CoreConvertFromSharedASlice core.clone.CloneU8))
                  sl
            let (c1, pd1) := rb2
            ok (b5, c1, pd1)) : Result (io.ParseBuf × alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8) ×
        core.marker.PhantomData misc.raw.bytes.NullBytes))
      ⦃ r => r.1 = b5 ∧ cowList r.2.1 = dropTrailingNul sl.val ⦄ := by
  split
  · step as ⟨i6, hi6, hi6'⟩
    step as ⟨i7, hi7⟩
    split
    · rename_i hl h0
      step as ⟨s0, hs0, hs0'⟩
      step as ⟨rb1, hrb1⟩
      obtain ⟨c1, pd1⟩ := rb1
      step*
      rw [dropTrailingNul_last_zero _ (by scalar_tac)]
      · rw [hrb1, hs0]; simp only [List.slice, List.drop_zero, Nat.sub_zero]; congr 1
      · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by scalar_tac)]
        simp only [Option.getD_some]
        rw [← h0, hi7]; congr 1; scalar_tac
    · rename_i hl h0
      step as ⟨rb1, hrb1⟩
      obtain ⟨c1, pd1⟩ := rb1
      step*
      rw [dropTrailingNul_last_ne _ (by scalar_tac)]
      · exact hrb1
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by scalar_tac)]
      simp only [Option.getD_some]
      intro h1; apply h0; rw [hi7]; rw [← h1]
      have : i6.val = sl.val.length - 1 := by scalar_tac
      simp only [this]
  · rename_i hl
    apply WP.spec_bind (rawbytes_new_borrowed sl)
    intro rb1 hrb1
    obtain ⟨c1, pd1⟩ := rb1
    step*
    have : sl.val = [] := by
      have : sl.len.val = 0 := by scalar_tac
      simpa using this
    rw [this]; rw [this] at hrb1; exact hrb1

set_option maxHeartbeats 400000 in
/-- `MyDeserialize for HandshakePacket`: on any input where it does not panic, exactly `handshakeRead` (fields, errors, and what is left of the buffer). -/
theorem packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) (h : ¬ handshakePanics buf.val) :
    packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map Handshake.of, rest.val) = handshakeRead buf.val ⦄ := by
  unfold packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec as ⟨r, buf1, h1⟩
  split_ifs at h1 with hl
  swap
  · obtain ⟨h1a, hb1⟩ := h1
    have : buf.val = [] := by simp [Slice.length] at hl; exact hl
    cases r with
    | Ok _ => simp [okPart] at h1a
    | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, this, hb1, handshakeRead]
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨pv, r1, hbuf⟩ : ∃ pv r1, buf.val = pv :: r1 := by
    cases hh : buf.val with
    | nil => simp [Slice.length, hh] at hl
    | cons pv r1 => exact ⟨pv, r1, rfl⟩
  rw [hbuf] at h1a h1b h
  simp only [List.drop_succ_cons, List.drop_zero] at h1b
  rw [hbuf]
  cases r with
  | Err e => simp [okPart] at h1a
  | Ok v0 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with CAUtil.parse_null_bytes_spec as ⟨r2, buf2, h2⟩
  rw [h1b] at h2
  unfold handshakeRead handshakePanics at *
  rcases hn : nulStrRead r1 with ⟨_ | sv, r2v⟩ <;> rw [hn] at h2 <;> simp only [hn] at h ⊢ <;>
    simp only [Prod.mk.injEq] at h2
  · obtain ⟨h2a, h2b⟩ := h2
    cases r2 with
    | Ok _ => simp [okPart] at h2a
    | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, okPart, h2b]
  obtain ⟨h2a, h2b⟩ := h2
  cases r2 with
  | Err e => simp [okPart] at h2a
  | Ok rb =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with parse_usize_spec as ⟨r3, buf3, h3⟩
  rw [h2b] at h3
  split_ifs at h3 with hl3
  swap
  · obtain ⟨h3a, rfl⟩ := h3
    have hs : r2v.length < 31 := by simp [Slice.length, h2b] at hl3 ⊢; omega
    cases r3 with
    | Ok _ => simp [okPart] at h3a
    | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, okPart, h2b, hs]
  have hr2 : 31 ≤ r2v.length := by simp [Slice.length, h2b] at hl3; omega
  have hr2' : ¬ r2v.length < 31 := by omega
  obtain ⟨h3a, h3b⟩ := h3
  cases r3 with
  | Err e => simp [okPart] at h3a
  | Ok pb =>
  have hpb : pb.val = r2v.take 31 := Option.some.inj h3a
  have hpl : pb.val.length = 31 := by rw [hpb]; simp; omega
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with pu_rawint_leu32 as ⟨q1, s1, k1a, k1b⟩
  cases q1 with
  | Err e => simp [okPart] at k1a
  | Ok w1 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with pu_array as ⟨q2, s2, k2a, k2b⟩
  cases q2 with
  | Err e => simp [okPart] at k2a
  | Ok w2 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with pu_skip as ⟨q3, s3, k3a, k3b⟩
  cases q3 with
  | Err e => simp [okPart] at k3a
  | Ok w3 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with pu_rawconst_lower as ⟨q4, s4, k4a, k4b⟩
  cases q4 with
  | Err e => simp [okPart] at k4a
  | Ok w4 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with parse_unchecked_u8_spec as ⟨q5, s5, k5a, k5b⟩
  cases q5 with
  | Err e => simp [okPart] at k5a
  | Ok w5 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with parse_unchecked_status_spec as ⟨q6, s6, k6a, k6b⟩
  have e1 : s1.val = (r2v.take 31).drop 4 := by rw [k1b, hpb]
  have e2 : s2.val = (r2v.take 31).drop 12 := by rw [k2b, e1, List.drop_drop]
  have e3 : s3.val = (r2v.take 31).drop 13 := by rw [k3b, e2, List.drop_drop]
  have e4 : s4.val = (r2v.take 31).drop 15 := by rw [k4b, e3, List.drop_drop]
  have e5 : s5.val = (r2v.take 31).drop 16 := by rw [k5b, e4, List.drop_drop]
  have e6 : s6.val = (r2v.take 31).drop 18 := by rw [k6b, e5, List.drop_drop]
  cases q6 with
  | Err e =>
    have hst : statusRead (leNat (((r2v.take 31).drop 16).take 2)) = none := by
      rw [← e5]; simpa [okPart] using k6a.symm
    simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, okPart, h3b, hr2', hst]
  | Ok w6 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with pu_rawconst_upper as ⟨q7, s7, k7a, k7b⟩
  cases q7 with
  | Err e => simp [okPart] at k7a
  | Ok w7 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with parse_unchecked_u8_spec as ⟨q8, s8, k8a, k8b⟩
  cases q8 with
  | Err e => simp [okPart] at k8a
  | Ok w8 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with pu_skip as ⟨q9, s9, k9a, k9b⟩
  cases q9 with
  | Err e => simp [okPart] at k9a
  | Ok w9 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  step with pu_rawconst_leu32 as ⟨q10, s10, k10a, k10b⟩
  cases q10 with
  | Err e => simp [okPart] at k10a
  | Ok w10 =>
  step as ⟨cfx, hcfx⟩
  subst hcfx
  have e7 : s7.val = (r2v.take 31).drop 20 := by rw [k7b, e6, List.drop_drop]
  have e8 : s8.val = (r2v.take 31).drop 21 := by rw [k8b, e7, List.drop_drop]
  have e9 : s9.val = (r2v.take 31).drop 27 := by rw [k9b, e8, List.drop_drop]
  obtain ⟨cl, ph0⟩ := w4
  obtain ⟨cu, ph7⟩ := w7
  obtain ⟨lb, ph8⟩ := w8
  obtain ⟨mcv, ph10⟩ := w10
  simp only [okPart, Option.map_some, Option.some.injEq] at k1a k2a k4a k5a k6a k7a k8a k10a
  rw [e1] at k2a; rw [e3] at k4a; rw [e4] at k5a; rw [e5] at k6a; rw [e6] at k7a; rw [e7] at k8a; rw [e9] at k10a
  rw [hpb] at k1a
  have v0e : cl.val = leNat ((r2v.drop 13).take 2) := by
    rw [← field_take31 _ _ _ (by norm_num)]; exact Option.some.inj k4a
  have v7e : cu.val = leNat ((r2v.drop 18).take 2) * 2 ^ 16 := by
    rw [← field_take31 _ _ _ (by norm_num)]; exact Option.some.inj k7a
  have v8e : lb.val = (r2v.getD 20 (byte 0)).val := by
    rw [← leNat_take1_drop _ _ (by omega), ← field_take31 _ _ _ (by norm_num)]; exact Option.some.inj k8a
  have v6 : statusRead (leNat ((r2v.drop 16).take 2)) ≠ none := by
    intro hn; rw [field_take31 _ _ _ (by norm_num), hn] at k6a; simp at k6a
  have hnp : hasFlag cl.val CLIENT_SECURE_CONNECTION = true → ¬ (128 ≤ lb.val ∧ lb.val < 136) := by
    intro hs hb; apply h; rw [v0e] at hs; rw [v8e] at hb; exact ⟨hr2, v6, hs, hb⟩
  have hsecv : (constants.CapabilityFlags.CLIENT_SECURE_CONNECTION).val = 2 ^ 15 := by
    simp [constants.CapabilityFlags.CLIENT_SECURE_CONNECTION]
  have hpav : (constants.CapabilityFlags.CLIENT_PLUGIN_AUTH).val = 2 ^ 19 := by
    simp [constants.CapabilityFlags.CLIENT_PLUGIN_AUTH]
  have hc13 : leNat (List.take 2 (List.drop 13 (List.take 31 r2v))) = cl.val := by
    rw [v0e, field_take31 _ _ _ (by norm_num)]
  have hc16 : statusRead (leNat (List.take 2 (List.drop 16 (List.take 31 r2v)))) = some w6.1.val := k6a.symm
  have hc18 : leNat (List.take 2 (List.drop 18 (List.take 31 r2v))) * 2 ^ 16 = cu.val := by
    rw [v7e, field_take31 _ _ _ (by norm_num)]
  have hc20 : leNat (List.take 1 (List.drop 20 (List.take 31 r2v))) = lb.val := (Option.some.inj k8a).symm
  have hsec_iff : ∀ i1 i2 : U32, i1 = constants.CapabilityFlags.CLIENT_SECURE_CONNECTION →
      i2.val = (cl &&& i1).val → (i2 > 0#u32 ↔ hasFlag cl.val CLIENT_SECURE_CONNECTION = true) := by
    intro i1 i2 h1 h2
    have hi2 : i2 = cl &&& i1 := UScalar.eq_of_val_eq h2
    rw [hi2, u32_and_pos_iff cl i1 15 (by rw [h1, hsecv])]; rfl
  have hpa_iff : ∀ i8 i9 : U32, i8 = constants.CapabilityFlags.CLIENT_PLUGIN_AUTH →
      i9.val = (cu &&& i8).val → (i9 > 0#u32 ↔ hasFlag cu.val CLIENT_PLUGIN_AUTH = true) := by
    intro i8 i9 h1 h2
    have hi9 : i9 = cu &&& i8 := UScalar.eq_of_val_eq h2
    rw [hi9, u32_and_pos_iff cu i8 19 (by rw [h1, hpav])]; rfl
  have hpv : v0.1.val = pv.val := by simpa [okPart, leNat] using h1a
  have hsv : cowList rb.1 = sv := Option.some.inj h2a
  have hstat : w6.1.val = leNat (List.take 2 (List.drop 16 (List.take 31 r2v))) := by
    have := hc16; unfold statusRead at this; split_ifs at this; simp at this; exact this.symm
  have hmc : mcv.val = leNat (List.take 4 (List.drop 27 (List.take 31 r2v))) := Option.some.inj k10a
  have hcl : cl.val &&& capabilityFlagsAll = cl.val := and_all32 _ (by scalar_tac)
  have hcu : cu.val &&& capabilityFlagsAll = cu.val := and_all32 _ (by scalar_tac)
  step*
  case hmin =>
    have hs : i2 > 0#u32 := by assumption
    have hi2 : i2 = cl &&& i1 := UScalar.eq_of_val_eq i2_post
    rw [hi2] at hs
    have hf := (u32_and_pos_iff cl i1 15 (by rw [i1_post, hsecv])).1 hs
    have hb := hnp (by simpa [CLIENT_SECURE_CONNECTION] using hf)
    rw [i4_post, hcast_i8_val]
    have : lb.val < 256 := by scalar_tac
    simp only [I8.min]
    split_ifs <;> simp [I8.numBits] <;> omega
  on_goal 2 =>
    have hs : i2 > 0#u32 := by assumption
    have hsf := (hsec_iff i1 i2 i1_post i2_post).1 hs
    have hl := scramble_len_val lb i4 i5 i6 len i4_post i5_post i6_post len_post
    rename_i hr13
    subst hr13
    simp only [okPart] at r13_post
    split_ifs at r13_post with hle
    · simp at r13_post
    · obtain ⟨-, hb4⟩ := r13_post
      have hlt : r2v.length - 31 < len.val := by
        simp only [Slice.length, h3b, List.length_drop] at hle; omega
      rw [hb4, h3b, hc13, hc20, ← hl]
      simp [hr2', hc16, hsf, hlt, okPart]
  all_goals try split
  on_goal 2 =>
    step as ⟨f1, hf1⟩
    step as ⟨c1, hc1⟩
    step as ⟨f2, hf2⟩
    step as ⟨c2, hc2⟩
    step as ⟨f3, hf3⟩
    step as ⟨c3, hc3⟩
    have hs : i2 > 0#u32 := by assumption
    have hsf := (hsec_iff i1 i2 i1_post i2_post).1 hs
    have hl := scramble_len_val lb i4 i5 i6 len i4_post i5_post i6_post len_post
    have hpf : hasFlag cu.val CLIENT_PLUGIN_AUTH = false := by
      have := (hpa_iff i8 i9 i8_post i9_post).not.1 (by assumption); simpa using this
    have hr13 : r13 = core.result.Result.Ok rb1 := by assumption
    subst hr13
    simp only [okPart] at r13_post
    split_ifs at r13_post with hle
    · obtain ⟨hrb1, hb4⟩ := r13_post
      have hle' : ¬ r2v.length - 31 < len.val := by
        simp only [Slice.length, h3b, List.length_drop] at hle; omega
      rw [hb4, h3b, hc13, hc20, ← hl]
      have hc18' : leNat (List.take 2 (List.drop 18 (List.take 31 r2v))) * 65536 = cu.val := hc18
      simp [hc18', hc16, hsf, hle', hpf, okPart, Handshake.of, hf1, hf2, hf3, hc1, hc2, hc3, hpv, hsv, hstat, hmc, k1a, k2a, k5a,
        hcl, hcu, Option.some.inj hrb1, h3b]
      rfl
    · simp at r13_post
  on_goal 3 =>
    step as ⟨f1, hf1⟩
    step as ⟨c1, hc1⟩
    step as ⟨f2, hf2⟩
    step as ⟨c2, hc2⟩
    step as ⟨f3, hf3⟩
    step as ⟨c3, hc3⟩
    have hsf : hasFlag cl.val CLIENT_SECURE_CONNECTION = false := by
      have := (hsec_iff i1 i2 i1_post i2_post).not.1 (by assumption); simpa using this
    have hpf : hasFlag cu.val CLIENT_PLUGIN_AUTH = false := by
      have := (hpa_iff i4 i5 i4_post i5_post).not.1 (by assumption); simpa using this
    rw [h3b, hc13]
    have hc18' : leNat (List.take 2 (List.drop 18 (List.take 31 r2v))) * 65536 = cu.val := hc18
    simp [hc18', hc16, hsf, hpf, okPart, Handshake.of, hf1, hf2, hf3, hc1, hc2, hc3, hpv, hsv, hstat, hmc, k1a, k2a, k5a,
      hcl, hcu, ← hc20]
    rfl
  on_goal 1 =>
    step with io.ParseBuf.eat_all_spec as ⟨pr0, hsl, hb6⟩
    obtain ⟨sl, b6⟩ := pr0
    step with plug_tail_spec as ⟨pr, hpr1, hpr2⟩
    obtain ⟨b5, cc, pdd⟩ := pr
    simp only at hpr1 hpr2
    subst hpr1
    rw [hsl] at hpr2
    step as ⟨f1, hf1⟩
    step as ⟨c1, hc1⟩
    step as ⟨f2, hf2⟩
    step as ⟨c2, hc2⟩
    step as ⟨f3, hf3⟩
    step as ⟨c3, hc3⟩
    have hs : i2 > 0#u32 := by assumption
    have hsf := (hsec_iff i1 i2 i1_post i2_post).1 hs
    have hl := scramble_len_val lb i4 i5 i6 len i4_post i5_post i6_post len_post
    have hpf : hasFlag cu.val CLIENT_PLUGIN_AUTH = true := (hpa_iff i8 i9 i8_post i9_post).1 (by assumption)
    have hr13 : r13 = core.result.Result.Ok rb1 := by assumption
    subst hr13
    simp only [okPart] at r13_post
    split_ifs at r13_post with hle
    · obtain ⟨hrb1, hb4⟩ := r13_post
      have hle' : ¬ r2v.length - 31 < len.val := by
        simp only [Slice.length, h3b, List.length_drop] at hle; omega
      rw [hb4, h3b] at hpr2
      rw [hc13, hc20, ← hl]
      have hc18' : leNat (List.take 2 (List.drop 18 (List.take 31 r2v))) * 65536 = cu.val := hc18
      simp [hc18', hc16, hsf, hle', hpf, okPart, Handshake.of, hf1, hf2, hf3, hc1, hc2, hc3, hpv, hsv, hstat, hmc, k1a, k2a, k5a,
        hcl, hcu, Option.some.inj hrb1, hb6]
      refine ⟨by rw [h3b], ?_⟩
      show some (cowList cc) = _
      rw [hpr2, List.drop_drop]
    · simp at r13_post
  on_goal 1 =>
    step with io.ParseBuf.eat_all_spec as ⟨pr0, hsl, hb6⟩
    obtain ⟨sl, b6⟩ := pr0
    step with plug_tail_spec as ⟨pr, hpr1, hpr2⟩
    obtain ⟨b5, cc, pdd⟩ := pr
    simp only at hpr1 hpr2
    subst hpr1
    rw [hsl] at hpr2
    step as ⟨f1, hf1⟩
    step as ⟨c1, hc1⟩
    step as ⟨f2, hf2⟩
    step as ⟨c2, hc2⟩
    step as ⟨f3, hf3⟩
    step as ⟨c3, hc3⟩
    have hsf : hasFlag cl.val CLIENT_SECURE_CONNECTION = false := by
      have := (hsec_iff i1 i2 i1_post i2_post).not.1 (by assumption); simpa using this
    have hpf : hasFlag cu.val CLIENT_PLUGIN_AUTH = true := (hpa_iff i4 i5 i4_post i5_post).1 (by assumption)
    rw [h3b] at hpr2
    rw [hc13]
    have hc18' : leNat (List.take 2 (List.drop 18 (List.take 31 r2v))) * 65536 = cu.val := hc18
    simp [hc18', hc16, hsf, hpf, okPart, Handshake.of, hf1, hf2, hf3, hc1, hc2, hc3, hpv, hsv, hstat, hmc, k1a, k2a, k5a,
      hcl, hcu, ← hc20, hb6]
    show some (cowList cc) = _
    rw [hpr2]

/-- **Bug: `MyDeserialize for HandshakePacket` panics on a server-supplied length byte in `128..135`** (with `CLIENT_SECURE_CONNECTION`): `auth_plugin_data_len as i8 - 8` overflows (`handshakePanics`). A server, or anyone in the middle before TLS, can crash a client built with overflow checks (e.g. a debug build) with the first packet. (Without overflow checks the subtraction wraps to exactly `b - 8`, the protocol's value, and the packet is read correctly.) -/
theorem packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics (buf : io.ParseBuf) (h : handshakePanics buf.val) :
    packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf = fail .integerOverflow := by
  unfold packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  obtain ⟨pv, r1, hbuf⟩ : ∃ pv r1, buf.val = pv :: r1 := by
    cases hh : buf.val with
    | nil => rw [hh] at h; exact absurd h id
    | cons pv r1 => exact ⟨pv, r1, rfl⟩
  rw [hbuf] at h
  unfold handshakePanics at h
  rcases hn : nulStrRead r1 with ⟨_ | sv, r2v⟩ <;> simp only [hn] at h
  obtain ⟨hr2, hst, hsec, hb1, hb2⟩ := h
  apply bind_fail_pair (U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec buf)
  intro r b1 hr
  have hl : 1 ≤ buf.length := by simp [Slice.length, hbuf]
  simp only [hl, ite_true, hbuf] at hr
  obtain ⟨hra, hrb⟩ := hr
  cases r with
  | Err e => simp [okPart] at hra
  | Ok v0 =>
  apply PBUtil.bind_fail_of_spec (branch_ok_spec v0)
  rintro c rfl
  split
  rotate_left
  · rename_i hh; cases hh
  rename_i hh; cases hh
  have hb1 : b1.val = r1 := by simpa using hrb
  apply bind_fail_pair (CAUtil.parse_null_bytes_spec b1)
  intro r2 b2 h2
  simp only [hb1, hn, Prod.mk.injEq] at h2
  obtain ⟨h2a, h2b⟩ := h2
  cases r2 with
  | Err e => simp [okPart] at h2a
  | Ok rb =>
  apply PBUtil.bind_fail_of_spec (branch_ok_spec rb)
  rintro c rfl
  split
  rotate_left
  · rename_i hh; cases hh
  rename_i hh; cases hh
  apply bind_fail_pair (parse_usize_spec b2 31#usize)
  intro r3 b3 h3
  have hl3 : (31#usize).val ≤ b2.length := by simp [Slice.length, h2b]; omega
  simp only [hl3, ite_true, h2b] at h3
  obtain ⟨h3a, h3b⟩ := h3
  cases r3 with
  | Err e => simp [okPart] at h3a
  | Ok pb =>
  have hpb : pb.val = r2v.take 31 := Option.some.inj h3a
  apply PBUtil.bind_fail_of_spec (branch_ok_spec pb)
  rintro c rfl
  split
  rotate_left
  · rename_i hh; cases hh
  rename_i hh; cases hh
  apply bind_fail_pair (pu_rawint_leu32 pb (by simp only [Slice.length, hpb]; simp; omega))
  intro q1 s1 k1
  obtain ⟨k1a, k1b⟩ := k1
  cases q1 with
  | Err e => simp [okPart] at k1a
  | Ok w1 =>
  apply PBUtil.bind_fail_of_spec (branch_ok_spec w1)
  rintro c rfl
  split
  rotate_left
  · rename_i hh; cases hh
  rename_i hh; cases hh
  apply bind_fail_pair (pu_array 8#usize s1 (by simp only [Slice.length, k1b, hpb]; simp; omega))
  intro q2 s2 k2
  obtain ⟨k2a, k2b⟩ := k2
  cases q2 with
  | Err e => simp [okPart] at k2a
  | Ok w2 =>
  apply PBUtil.bind_fail_of_spec (branch_ok_spec w2)
  rintro c rfl
  split
  rotate_left
  · rename_i hh; cases hh
  rename_i hh; cases hh
  apply bind_fail_pair (pu_skip 1#usize s2 (by simp only [Slice.length, k2b, k1b, hpb]; simp; omega))
  intro q3 s3 k3
  obtain ⟨k3a, k3b⟩ := k3
  cases q3 with
  | Err e => simp [okPart] at k3a
  | Ok w3 =>
  apply PBUtil.bind_fail_of_spec (branch_ok_spec w3)
  rintro c rfl
  split
  rotate_left
  · rename_i hh; cases hh
  rename_i hh; cases hh
  apply bind_fail_pair (pu_rawconst_lower constants.CapabilityFlags s3 (by simp only [Slice.length, k3b, k2b, k1b, hpb]; simp; omega))
  intro q4 s4 k4
  obtain ⟨k4a, k4b⟩ := k4
  cases q4 with
  | Err e => simp [okPart] at k4a
  | Ok w4 =>
  apply PBUtil.bind_fail_of_spec (branch_ok_spec w4)
  rintro c rfl
  split
  rotate_left
  · rename_i hh; cases hh
  rename_i hh; cases hh
  apply bind_fail_pair (parse_unchecked_u8_spec s4 (by simp only [Slice.length, k4b, k3b, k2b, k1b, hpb]; simp; omega))
  intro q5 s5 k5
  obtain ⟨k5a, k5b⟩ := k5
  cases q5 with
  | Err e => simp [okPart] at k5a
  | Ok w5 =>
  apply PBUtil.bind_fail_of_spec (branch_ok_spec w5)
  rintro c rfl
  split
  rotate_left
  · rename_i hh; cases hh
  rename_i hh; cases hh
  apply bind_fail_pair (parse_unchecked_status_spec s5 (by simp only [Slice.length, k5b, k4b, k3b, k2b, k1b, hpb]; simp; omega))
  intro q6 s6 k6
  obtain ⟨k6a, k6b⟩ := k6
  cases q6 with
  | Err e =>
    exfalso; apply hst
    have e5 : s5.val = (r2v.take 31).drop 16 := by
      rw [k5b, k4b, k3b, k2b, k1b, hpb]; simp [List.drop_drop]
    have : statusRead (leNat (((r2v.take 31).drop 16).take 2)) = none := by
      rw [← e5, ← k6a]; rfl
    rwa [field_take31 r2v 16 2 (by norm_num)] at this
  | Ok w6 =>
  apply PBUtil.bind_fail_of_spec (branch_ok_spec w6)
  rintro c rfl
  split
  rotate_left
  · rename_i hh; cases hh
  rename_i hh; cases hh
  apply bind_fail_pair (pu_rawconst_upper constants.CapabilityFlags s6 (by simp only [Slice.length, k6b, k5b, k4b, k3b, k2b, k1b, hpb]; simp; omega))
  intro q7 s7 k7
  obtain ⟨k7a, k7b⟩ := k7
  cases q7 with
  | Err e => simp [okPart] at k7a
  | Ok w7 =>
  apply PBUtil.bind_fail_of_spec (branch_ok_spec w7)
  rintro c rfl
  split
  rotate_left
  · rename_i hh; cases hh
  rename_i hh; cases hh
  apply bind_fail_pair (parse_unchecked_u8_spec s7 (by simp only [Slice.length, k7b, k6b, k5b, k4b, k3b, k2b, k1b, hpb]; simp; omega))
  intro q8 s8 k8
  obtain ⟨k8a, k8b⟩ := k8
  cases q8 with
  | Err e => simp [okPart] at k8a
  | Ok w8 =>
  apply PBUtil.bind_fail_of_spec (branch_ok_spec w8)
  rintro c rfl
  split
  rotate_left
  · rename_i hh; cases hh
  rename_i hh; cases hh
  apply bind_fail_pair (pu_skip 6#usize s8 (by simp only [Slice.length, k8b, k7b, k6b, k5b, k4b, k3b, k2b, k1b, hpb]; simp; omega))
  intro q9 s9 k9
  obtain ⟨k9a, k9b⟩ := k9
  cases q9 with
  | Err e => simp [okPart] at k9a
  | Ok w9 =>
  apply PBUtil.bind_fail_of_spec (branch_ok_spec w9)
  rintro c rfl
  split
  rotate_left
  · rename_i hh; cases hh
  rename_i hh; cases hh
  apply bind_fail_pair (pu_rawconst_leu32 constants.MariadbCapabilities s9 (by simp only [Slice.length, k9b, k8b, k7b, k6b, k5b, k4b, k3b, k2b, k1b, hpb]; simp; omega))
  intro q10 s10 k10
  obtain ⟨k10a, k10b⟩ := k10
  cases q10 with
  | Err e => simp [okPart] at k10a
  | Ok w10 =>
  apply PBUtil.bind_fail_of_spec (branch_ok_spec w10)
  rintro c rfl
  split
  rotate_left
  · rename_i hh; cases hh
  rename_i hh; cases hh
  obtain ⟨cl, ph4⟩ := w4
  obtain ⟨lb, ph8⟩ := w8
  rw [Std.uncurry_apply_pair]
  apply PBUtil.bind_fail_of_spec (caps_bits_spec _)
  rintro i1 rfl
  apply PBUtil.bind_fail_of_spec (show lift (cl &&& constants.CapabilityFlags.CLIENT_SECURE_CONNECTION) ⦃ r =>
    r = cl &&& constants.CapabilityFlags.CLIENT_SECURE_CONNECTION ⦄ by simp [lift])
  rintro i2 rfl
  have e3 : s3.val = (r2v.take 31).drop 13 := by
    rw [k3b, k2b, k1b, hpb]; simp [List.drop_drop]
  have e7 : s7.val = (r2v.take 31).drop 20 := by
    rw [k7b, k6b, k5b, k4b, k3b, k2b, k1b, hpb]; simp [List.drop_drop]
  have vcl : cl.val = leNat ((r2v.drop 13).take 2) := by
    rw [← field_take31 _ _ _ (by norm_num), ← e3]; exact Option.some.inj k4a
  have vlb : lb.val = (r2v.getD 20 (byte 0)).val := by
    rw [← leNat_take1_drop _ _ (by omega), ← field_take31 _ _ _ (by norm_num), ← e7]; exact Option.some.inj k8a
  have hsecv : (constants.CapabilityFlags.CLIENT_SECURE_CONNECTION).val = 2 ^ 15 := by
    simp [constants.CapabilityFlags.CLIENT_SECURE_CONNECTION]
  have hpos : cl &&& constants.CapabilityFlags.CLIENT_SECURE_CONNECTION > 0#u32 :=
    (u32_and_pos_iff cl _ 15 hsecv).2 (by rw [vcl]; simpa [CLIENT_SECURE_CONNECTION] using hsec)
  rw [ite_eq_left hpos, Std.uncurry_apply_pair]
  apply PBUtil.bind_fail_of_spec (show lift (UScalar.hcast .I8 lb) ⦃ r => r = UScalar.hcast .I8 lb ⦄ by simp [lift])
  rintro i4 rfl
  apply PBUtil.bind_fail_left
  apply i8_sub_fail
  have := hcast_i8_val lb
  have h8 : (8#i8 : I8).val = 8 := by rfl
  rw [this, h8, vlb]
  split_ifs <;> omega

private theorem serialize_tail_spec
    (s2 : Option (misc.raw.bytes.RawBytes (misc.raw.bytes.BareBytes 247#usize) Usize))
    (pn : Option (misc.raw.bytes.RawBytes misc.raw.bytes.NullBytes Unit)) (buf : alloc.vec.Vec U8)
    (h : buf.length + ((s2.map (fun rb => (cowList rb.1).take 247)).getD [] ++
      (pn.map (fun rb => nulStr (cowList rb.1))).getD []).length ≤ Usize.max) :
    packets.serialize_handshake_tail s2 pn buf ⦃ b => b.val = buf.val ++
      ((s2.map (fun rb => (cowList rb.1).take 247)).getD [] ++ (pn.map (fun rb => nulStr (cowList rb.1))).getD []) ⦄ := by
  unfold packets.serialize_handshake_tail packets.serialize_handshake_auth_plugin_name
  rcases s2 with _ | rb <;> rcases pn with _ | rb2 <;> simp only [Option.map_none, Option.map_some, Option.getD_none,
    Option.getD_some, List.append_nil, List.nil_append, List.length_append] at h ⊢
  · simp
  · step*
  · step*
  · step*

/-- `MySerialize for HandshakePacket`: appends `handshakeEnc` of the fields. -/
theorem packets.HandshakePacket.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.HandshakePacket) (buf : alloc.vec.Vec U8)
    (h : buf.length + (handshakeEnc (Handshake.of self)).length ≤ Usize.max) :
    packets.HandshakePacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ handshakeEnc (Handshake.of self) ⦄ := by
  unfold packets.HandshakePacket.Insts.Mysql_commonProtoMySerialize.serialize
  have hl : buf.val.length + (handshakeEnc (Handshake.of self)).length ≤ Usize.max := h
  simp only [handshakeEnc, Handshake.of, List.length_cons, List.length_append, PBUtil.length_leBytes,
    List.length_replicate] at hl
  step with PCSUtil.rawint_u8_serialize as ⟨b1, h1⟩
  step with nullbytes_raw_ser as ⟨b2, h2⟩
  all_goals try lenTac
  step with PCSUtil.rawint_u32_serialize as ⟨b3, h3⟩
  all_goals try lenTac
  step with ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨b4, h4⟩
  all_goals try lenTac
  step with PKUtil.put_u8_spec as ⟨b5, h5⟩
  all_goals try lenTac
  step with const_caps_lower_ser as ⟨b6, h6⟩
  all_goals try lenTac
  step with PCSUtil.rawint_u8_serialize as ⟨b7, h7⟩
  all_goals try lenTac
  step with const_status_ser as ⟨b8, h8⟩
  all_goals try lenTac
  step with const_caps_upper_ser as ⟨b9, h9⟩
  all_goals try lenTac
  step
  step with PKUtil.caps_contains_spec as ⟨bb, hbb⟩
  step with handshake_auth_plugin_data_len_spec as ⟨li, hli⟩
  step with PKUtil.put_u8_spec as ⟨b10, h10⟩
  all_goals try lenTac
  step with PCSUtil.skip_serialize as ⟨b11, h11⟩
  all_goals try lenTac
  step with const_mariadb_u32_ser as ⟨b12, h12⟩
  all_goals try lenTac
  have hpa : (constants.CapabilityFlags.CLIENT_PLUGIN_AUTH).val = CLIENT_PLUGIN_AUTH := by
    simp [constants.CapabilityFlags.CLIENT_PLUGIN_AUTH, CLIENT_PLUGIN_AUTH]
  have hli' : li = byte (handshakeLenByte (Handshake.of self)) := by
    apply UScalar.eq_of_val_eq
    rw [hli, PBUtil.byte_val, hbb, cf_post, hpa]
    simp only [handshakeLenByte, Handshake.of]
    by_cases hf : hasFlag self.capabilities_2.1.val CLIENT_PLUGIN_AUTH = true <;>
      rcases self.scramble_2 with _ | rb <;> simp [hf]
    omega
  have hz : (0#u8 : U8) = byte 0 := rfl
  rcases hs2 : self.scramble_2 with _ | rb <;> rcases hpn : self.auth_plugin_name with _ | pn <;>
    simp only [hs2, hpn, Option.map_none, Option.map_some] at hl ⊢
  all_goals
    step with serialize_tail_spec as ⟨b13, h13⟩
    · simp only [alloc.vec.Vec.length] at *
      simp [h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, PBUtil.length_leBytes] at *
      omega
    simp [h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, hli', hz, handshakeEnc, Handshake.of, hs2, hpn]

/-- Round trip: a `Handshake.Compatible` handshake written by `handshakeEnc` reads back with the same fields (the stored length byte is the one written). With `CLIENT_PLUGIN_AUTH` the plugin name is the rest of the packet, so nothing may follow. (With `CLIENT_PLUGIN_AUTH`, a scramble of 120–127 bytes makes the reader panic instead: `Defs.handshakePanics_handshakeEnc`.) -/
theorem packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (hs : Handshake) (hc : hs.Compatible) (tail : List U8)
    (ht : hasFlag hs.capsUpper CLIENT_PLUGIN_AUTH = true → tail = []) (buf : io.ParseBuf)
    (h : buf.val = handshakeEnc hs ++ tail) :
    packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map Handshake.of = some { hs with authDataLen := handshakeLenByte hs } ∧ rest.val = tail ⦄ := by
  obtain ⟨hr, hnp⟩ := handshakeRead_enc hs hc tail ht
  apply WP.spec_mono (packets.HandshakePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf
    (by rw [h]; exact hnp))
  rintro ⟨r, rest⟩ hrr
  simp only [WP.uncurry'_pair] at hrr ⊢
  rw [h, hr] at hrr
  simp only [Prod.mk.injEq] at hrr
  exact hrr

/-- `new`: the given fields; the capabilities are split into their lower and upper 16 bits, MariaDB's capabilities are empty. The stored length byte is the scramble's length (at most 247), **without the protocol's `+ 8`**; it is not used by `serialize` (which recomputes it) or any accessor, but the derived `PartialEq`/`Debug` see it, so `new(..)` differs from `deserialize(serialize(new(..)))`. -/
theorem packets.HandshakePacket.new_spec {T1 T2 T3 : Type} (into1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (into2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (into3 : core.convert.Into T3 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (protocol_version : U8) (server_version : T1) (connection_id : U32) (scramble_1 : Array U8 8#usize)
    (scramble_2 : Option T2) (capabilities : constants.CapabilityFlags) (default_collation : U8)
    (status_flags : constants.StatusFlags) (auth_plugin_name : Option T3)
    (c1 c2 c3 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h1 : into1.into server_version = ok c1)
    (h2 : ∀ x, scramble_2 = some x → into2.into x = ok c2)
    (h3 : ∀ x, auth_plugin_name = some x → into3.into x = ok c3) :
    packets.HandshakePacket.new into1 into2 into3 protocol_version server_version connection_id scramble_1 scramble_2
      capabilities default_collation status_flags auth_plugin_name ⦃ p =>
      Handshake.of p =
        { protocolVersion := protocol_version.val, serverVersion := cowList c1,
          connectionId := connection_id.val, scramble1 := scramble_1.val,
          capsLower := capabilities.val &&& 0xFFFF, collation := default_collation.val,
          status := status_flags.val, capsUpper := capabilities.val &&& 0xFFFF0000,
          authDataLen := (scramble_2.map (fun _ => min (cowList c2).length 247)).getD 0,
          mariadbCaps := 0, scramble2 := scramble_2.map (fun _ => cowList c2),
          pluginName := auth_plugin_name.map (fun _ => cowList c3) } ⦄ := by
  unfold packets.HandshakePacket.new
  simp only [constants.CapabilityFlags.bits, constants.CapabilityFlags.from_bits_retain_eq,
    constants.MariadbCapabilities.empty, bind_ok]
  step*
  rcases scramble_2 with _ | x2 <;> rcases auth_plugin_name with _ | x3 <;> simp only
  all_goals first
    | (have h2' := h2 x2 rfl; have h3' := h3 x3 rfl
       step*
       simp_all [Handshake.of])
    | (have h2' := h2 x2 rfl
       step*
       simp_all [Handshake.of])
    | (have h3' := h3 x3 rfl
       step*
       simp_all [Handshake.of])
    | (step*
       simp_all [Handshake.of])

/-- `with_mariadb_ext_capabilities`: replaces MariaDB's capabilities. -/
theorem packets.HandshakePacket.with_mariadb_ext_capabilities_spec (self : packets.HandshakePacket) (flags : constants.MariadbCapabilities) :
    packets.HandshakePacket.with_mariadb_ext_capabilities self flags ⦃ p =>
      Handshake.of p = { Handshake.of self with mariadbCaps := flags.val } ⦄ := by
  unfold packets.HandshakePacket.with_mariadb_ext_capabilities
  step*
  simp_all [Handshake.of]

/-- `into_owned`: the same fields. -/
theorem packets.HandshakePacket.into_owned_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.into_owned self ⦃ p => Handshake.of p = Handshake.of self ⦄ := by
  unfold packets.HandshakePacket.into_owned
  step with PCSUtil.raw_into_owned as ⟨rb, hrb⟩
  rcases hs2 : self.scramble_2 with _ | s2 <;> rcases hpn : self.auth_plugin_name with _ | pn <;> simp only
  · simp [Handshake.of, hs2, hpn, hrb]
  · step with PCSUtil.raw_into_owned as ⟨rb2, hrb2⟩
    simp [Handshake.of, hs2, hpn, hrb, hrb2]
  · step with PCSUtil.raw_into_owned as ⟨rb2, hrb2⟩
    simp [Handshake.of, hs2, hpn, hrb, hrb2]
  · step with PCSUtil.raw_into_owned as ⟨rb2, hrb2⟩
    step with PCSUtil.raw_into_owned as ⟨rb3, hrb3⟩
    simp [Handshake.of, hs2, hpn, hrb, hrb2, hrb3]

/-- `protocol_version`: the field. -/
theorem packets.HandshakePacket.impl.protocol_version_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.protocol_version self = ok self.protocol_version.1 := by
  rfl

/-- `server_version_ref`: the server version. -/
theorem packets.HandshakePacket.server_version_ref_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.server_version_ref self ⦃ s => s.val = cowList self.server_version.1 ⦄ := by
  unfold packets.HandshakePacket.server_version_ref
  step*

/-- `server_version_str`: the server version, lossily converted to UTF-8 (`LossyUtf8`). -/
theorem packets.HandshakePacket.server_version_str_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.server_version_str self ⦃ c => LossyUtf8 (cowList self.server_version.1) c ⦄ := by
  unfold packets.HandshakePacket.server_version_str
  step*

/-- `server_version_parsed`, exactly: the trusted `VERSION_RE` captures of the server version, each read by `btoi::<u16>`, **panicking** if one does not parse (`versionOfCaptures`). The regex is opaque (`Trusted.versionReCaptures`). -/
theorem packets.HandshakePacket.server_version_parsed_eq (self : packets.HandshakePacket) (s : Slice U8) (hs : s.val = cowList self.server_version.1) :
    packets.HandshakePacket.server_version_parsed self = versionOfCaptures (Trusted.versionReCaptures s) := by
  unfold packets.HandshakePacket.server_version_parsed
  have hr : packets.HandshakePacket.server_version_ref self = ok s := by
    obtain ⟨v, hv, hp⟩ := spec_eq_ok (packets.HandshakePacket.server_version_ref_spec self)
    rw [hv]; congr 1; exact Slice.ext _ _ (hp.trans hs.symm)
  rw [hr, bind_ok]
  simp only [misc.trusted.version_re_captures, bind_ok, misc.trusted.btoi_u16]
  unfold versionOfCaptures
  rcases Trusted.versionReCaptures s with _ | ⟨a, b, c⟩
  · rfl
  · simp only [core.option.Option.unwrap]
    cases ha : Trusted.btoiUnsigned .U16 a <;> cases hb : Trusted.btoiUnsigned .U16 b <;>
      cases hc : Trusted.btoiUnsigned .U16 c <;> simp [ha, hb, hc]

/-- `server_version_parsed` never returns a wrong version: on ASCII input the result is the version that `^(\d{1,2})\.(\d{1,2})\.(\d{1,3})(.*)` captures (`versionReMatch`, by the trusted `Trusted.versionReCaptures_ascii`), and there is no panic. **Bug** (as for the date/time parsers): off ASCII, `\d` is Unicode-aware but `btoi` is not, so a server version with non-ASCII digits that the regex matches panics (`unwrap`; `server_version_parsed_eq`). -/
theorem packets.HandshakePacket.server_version_parsed_ascii (self : packets.HandshakePacket) (s : Slice U8) (hs : s.val = cowList self.server_version.1)
    (h : ∀ b ∈ s.val, b.val < 128) :
    packets.HandshakePacket.server_version_parsed self ⦃ r => versionVal r = digitsTriple (versionReMatch s.val) ⦄ := by
  rw [packets.HandshakePacket.server_version_parsed_eq self s hs]
  have hax := Trusted.versionReCaptures_ascii s h
  have := versionOfCaptures_good (Trusted.versionReCaptures s) (by
    intro a b c hc
    rw [hc] at hax
    exact versionReMatch_good s.val _ _ _ hax.symm)
  unfold versionReMatch
  rw [← hax]
  exact this

/-- `maria_db_server_version_parsed`, exactly: as `server_version_parsed_eq` with `MARIADB_VERSION_RE` (`Trusted.mariadbVersionReCaptures`). -/
theorem packets.HandshakePacket.maria_db_server_version_parsed_eq (self : packets.HandshakePacket) (s : Slice U8) (hs : s.val = cowList self.server_version.1) :
    packets.HandshakePacket.maria_db_server_version_parsed self = versionOfCaptures (Trusted.mariadbVersionReCaptures s) := by
  unfold packets.HandshakePacket.maria_db_server_version_parsed
  have hr : packets.HandshakePacket.server_version_ref self = ok s := by
    obtain ⟨v, hv, hp⟩ := spec_eq_ok (packets.HandshakePacket.server_version_ref_spec self)
    rw [hv]; congr 1; exact Slice.ext _ _ (hp.trans hs.symm)
  rw [hr, bind_ok]
  simp only [misc.trusted.mariadb_version_re_captures, bind_ok, misc.trusted.btoi_u16]
  unfold versionOfCaptures
  rcases Trusted.mariadbVersionReCaptures s with _ | ⟨a, b, c⟩
  · rfl
  · simp only [core.option.Option.unwrap]
    cases ha : Trusted.btoiUnsigned .U16 a <;> cases hb : Trusted.btoiUnsigned .U16 b <;>
      cases hc : Trusted.btoiUnsigned .U16 c <;> simp [ha, hb, hc]

/-- `maria_db_server_version_parsed` never returns a wrong version: as `server_version_parsed_ascii`, with `mariadbVersionReMatch` (`Trusted.mariadbVersionReCaptures_ascii`). Same **bug** off ASCII. -/
theorem packets.HandshakePacket.maria_db_server_version_parsed_ascii (self : packets.HandshakePacket) (s : Slice U8) (hs : s.val = cowList self.server_version.1)
    (h : ∀ b ∈ s.val, b.val < 128) :
    packets.HandshakePacket.maria_db_server_version_parsed self ⦃ r => versionVal r = digitsTriple (mariadbVersionReMatch s.val) ⦄ := by
  rw [packets.HandshakePacket.maria_db_server_version_parsed_eq self s hs]
  have hax := Trusted.mariadbVersionReCaptures_ascii s h
  have := versionOfCaptures_good (Trusted.mariadbVersionReCaptures s) (by
    intro a b c hc
    rw [hc] at hax
    exact mariadbVersionReMatch_good s.val _ _ _ hax.symm)
  unfold mariadbVersionReMatch
  rw [← hax]
  exact this

/-- `connection_id`: the field. -/
theorem packets.HandshakePacket.impl.connection_id_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.connection_id self = ok self.connection_id.1 := by
  rfl

/-- `scramble_1_ref`: the 8 bytes. -/
theorem packets.HandshakePacket.scramble_1_ref_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.scramble_1_ref self ⦃ s => s.val = self.scramble_1.val ⦄ := by
  unfold packets.HandshakePacket.scramble_1_ref
  simp only [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeFullSlice, core.slice.index.SliceIndexRangeFullSlice.index]
  step*

/-- `scramble_2_ref`: the scramble, if any (at most 247 bytes: the `BareBytes<247>` maximum; documented: may include the terminating `0`). -/
theorem packets.HandshakePacket.scramble_2_ref_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.scramble_2_ref self ⦃ o => o.map (·.val) = self.scramble_2.map (fun rb => (cowList rb.1).take 247) ⦄ := by
  unfold packets.HandshakePacket.scramble_2_ref
  rcases hs2 : self.scramble_2 with _ | s2 <;> simp only
  · simp
  · step*
    simp_all

private theorem nonce_scramble_2_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.nonce_scramble_2 self ⦃ s =>
      s.val = match self.scramble_2 with
        | some rb => dropTrailingNul ((cowList rb.1).take 247)
        | none => [] ⦄ := by
  unfold packets.HandshakePacket.nonce_scramble_2
  step with packets.HandshakePacket.scramble_2_ref_spec as ⟨o, ho⟩
  rcases hs : self.scramble_2 with _ | rb <;> rw [hs] at ho <;> rcases o with _ | sl <;> simp at ho
  · simp only
    apply (WP.spec_ok _).mpr
    rfl
  · simp only
    step*
    · rename_i h0
      rw [← ho, dropTrailingNul_last_zero _ (by scalar_tac)]
      · rw [s_post]; simp only [List.slice, List.drop_zero, Nat.sub_zero]; congr 1
      · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by scalar_tac)]
        simp only [Option.getD_some]
        rw [← h0, i1_post]; congr 1; scalar_tac
    · rename_i h0
      rw [← ho, dropTrailingNul_last_ne _ (by scalar_tac)]
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by scalar_tac)]
      simp only [Option.getD_some]
      intro h1; apply h0; rw [i1_post]; rw [← h1]
      have : i.val = sl.val.length - 1 := by scalar_tac
      simp only [this]
    · rename_i h0
      have : sl.val = [] := by
        have : sl.len.val = 0 := by scalar_tac
        simpa using this
      rw [← ho, this]; rfl

/-- `nonce`: `scramble_1` then `scramble_2` without its trailing `0`, zero-padded to 20 bytes (`handshakeNonce`). -/
theorem packets.HandshakePacket.nonce_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.nonce self ⦃ v =>
      v.val = handshakeNonce self.scramble_1.val (self.scramble_2.map (fun rb => (cowList rb.1).take 247)) ⦄ := by
  unfold packets.HandshakePacket.nonce
  step with packets.HandshakePacket.scramble_1_ref_spec as ⟨s, hs⟩
  step with alloc.slice.Slice.to_vec_spec as ⟨out, hout⟩
  step with nonce_scramble_2_spec as ⟨s1, hs1⟩
  have hl1 : s1.val.length ≤ 247 := by
    rw [hs1]; split
    · exact le_trans (dropTrailingNul_length_le _) (by simp)
    · simp
  have hout' : out.val = self.scramble_1.val := by rw [← hs, hout]; rfl
  have h8 : self.scramble_1.val.length = 8 := by simp
  have hb : out.length + s1.length ≤ Usize.max := by
    have : out.length = 8 := by simp [alloc.vec.Vec.length, hout', h8]
    have : s1.length ≤ 247 := hl1
    scalar_tac
  have hn : handshakeNonce self.scramble_1.val (self.scramble_2.map (fun rb => (cowList rb.1).take 247)) =
      (self.scramble_1.val ++ s1.val) ++ List.replicate (20 - (self.scramble_1.val ++ s1.val).length) (byte 0) := by
    unfold handshakeNonce
    rw [hs1]
    rcases self.scramble_2 with _ | rb <;> rfl
  rw [hn]
  have hS : auth.plugins.mysql_native_password.SCRAMBLE_LENGTH = 20#usize := by
    unfold auth.plugins.mysql_native_password.SCRAMBLE_LENGTH; rfl
  have hz : byte 0 = 0#u8 := rfl
  step*
  · rename_i hlt
    rw [hS] at hlt
    have hlt' : out1.val.length < 20 := by scalar_tac
    rw [v_post, out1_post, hout', hz, List.resize]
    rw [out1_post, hout'] at hlt'
    simp only [ge_iff_le, Nat.zero_le, ite_true]
    rw [List.take_of_length_le (by omega)]
  · rename_i hlt
    rw [hS] at hlt
    have hlt' : 20 ≤ out1.val.length := by scalar_tac
    rw [out1_post, hout'] at hlt' ⊢
    rw [show 20 - (self.scramble_1.val ++ s1.val).length = 0 by omega]
    simp

/-- `capabilities`: the two halves together. -/
theorem packets.HandshakePacket.capabilities_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.capabilities self ⦃ c => c.val = self.capabilities_1.1.val ||| self.capabilities_2.1.val ⦄ := by
  unfold packets.HandshakePacket.capabilities
  unfold constants.CapabilityFlags.Insts.CoreOpsBitBitOrCapabilityFlagsCapabilityFlags.bitor
  rcases h1 : self.capabilities_1 with ⟨c1, p1⟩
  rcases h2 : self.capabilities_2 with ⟨c2, p2⟩
  simp only
  step*

/-- `mariadb_ext_capabilities`: the field. -/
theorem packets.HandshakePacket.impl.mariadb_ext_capabilities_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.mariadb_ext_capabilities self = ok self.mariadb_ext_capabilities.1 := by
  rfl

/-- `default_collation`: the field. -/
theorem packets.HandshakePacket.impl.default_collation_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.default_collation self = ok self.default_collation.1 := by
  rfl

/-- `status_flags`: the field. -/
theorem packets.HandshakePacket.impl.status_flags_eq (self : packets.HandshakePacket) :
    packets.HandshakePacket.impl.status_flags self = ok self.status_flags.1 := by
  rfl

/-- `auth_plugin_name_ref`: the plugin name, if any. -/
theorem packets.HandshakePacket.auth_plugin_name_ref_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.auth_plugin_name_ref self ⦃ o => o.map (·.val) = self.auth_plugin_name.map (fun rb => cowList rb.1) ⦄ := by
  unfold packets.HandshakePacket.auth_plugin_name_ref
  rcases hs2 : self.auth_plugin_name with _ | s2 <;> simp only
  · simp
  · step*
    simp_all

/-- `auth_plugin_name_str`: the plugin name, if any, lossily converted to UTF-8. -/
theorem packets.HandshakePacket.auth_plugin_name_str_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.auth_plugin_name_str self ⦃ o =>
      optMatch (fun rb c => LossyUtf8 (cowList rb.1) c) self.auth_plugin_name o ⦄ := by
  unfold packets.HandshakePacket.auth_plugin_name_str
  rcases hs2 : self.auth_plugin_name with _ | s2 <;> simp only
  · simp [optMatch]
  · step*
    simp_all [optMatch]

/-- `auth_plugin`: `AuthPlugin::from_bytes` of the plugin name without a trailing `0`. (`from_bytes` removes another trailing `0`: **a quirk**, two are removed in all.) -/
theorem packets.HandshakePacket.auth_plugin_spec (self : packets.HandshakePacket) :
    packets.HandshakePacket.auth_plugin self ⦃ o =>
      optMatch (fun rb r => PluginFromBytes (dropTrailingNul (cowList rb.1)) r) self.auth_plugin_name o ⦄ := by
  unfold packets.HandshakePacket.auth_plugin
  rcases hs : self.auth_plugin_name with _ | rb
  · simp only
    apply (WP.spec_ok _).mpr
    trivial
  · simp only
    step with nullbytes_as_bytes as ⟨sl, ho⟩
    step*
    · rename_i h0
      step with packets.AuthPlugin.from_bytes_spec as ⟨ap, hap⟩
      simp only [optMatch]
      rw [← ho, dropTrailingNul_last_zero _ (by scalar_tac)]
      · rw [s_post] at hap; simp only [List.slice, List.drop_zero, Nat.sub_zero] at hap
        have : i.val = sl.val.length - 1 := by scalar_tac
        rw [this] at hap; exact hap
      · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by scalar_tac)]
        simp only [Option.getD_some]
        rw [← h0, i1_post]; congr 1; scalar_tac
    · rename_i h0
      step with packets.AuthPlugin.from_bytes_spec as ⟨ap, hap⟩
      simp only [optMatch]
      rw [← ho, dropTrailingNul_last_ne _ (by scalar_tac)]
      · exact hap
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by scalar_tac)]
      simp only [Option.getD_some]
      intro h1; apply h0; rw [i1_post]; rw [← h1]
      have : i.val = sl.val.length - 1 := by scalar_tac
      simp only [this]
    · rename_i h0
      step with packets.AuthPlugin.from_bytes_spec as ⟨ap, hap⟩
      have : sl.val = [] := by
        have : sl.len.val = 0 := by scalar_tac
        simpa using this
      simp only [optMatch]
      rw [← ho, this]; rw [this] at hap; exact hap

end mysql_common
