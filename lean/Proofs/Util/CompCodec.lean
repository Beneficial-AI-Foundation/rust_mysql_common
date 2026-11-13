import Defs
import Proofs.Util.ParseBuf
import Proofs.Util.ConvInts

/-! Helper lemmas for the compressed-codec proofs (group CompCodec: `Proofs/Proto/Codec/Comp*.lean`,
`Compress*.lean`, `PacketCodec*.lean`, `Proofs/Defs/LemmasComp.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.CompCodec

open proto.codec.buf_model

/-! ## Step lemmas for `VecBuf` -/

@[step]
theorem vb_advance_spec (src : VecBuf) (cnt : Usize) (h : cnt.val ≤ src.val.length) :
    VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf.advance src cnt ⦃ r => r.val = src.val.drop cnt.val ⦄ := by
  unfold VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf.advance
  step*
  subst_vars; assumption

@[step]
theorem vb_put_slice_spec (dst : VecBuf) (s : Slice U8) (h : dst.val.length + s.val.length ≤ Usize.max) :
    VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut.put_slice dst s ⦃ r => r.val = dst.val ++ s.val ⦄ := by
  unfold VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut.put_slice alloc.vec.Vec.extend_from_slice
  simp only [dite_eq_left h]
  have := List.clone_spec (clone := core.clone.CloneU8.clone) (l := s.val) (by intros; rfl)
  obtain ⟨l, hl, hp⟩ := PBUtil.spec_eq_ok this
  simp [hl, hp.1]

@[step]
theorem vb_deref_spec (v : VecBuf) : VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref v ⦃ s => s.val = v.val ⦄ := by
  simp [VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, alloc.vec.Vec.deref]

@[step]
theorem vb_reserve_spec (v : VecBuf) (n : Usize) :
    VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve.reserve v n ⦃ r => r = v ⦄ := by
  simp [VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve.reserve]

@[step]
theorem vb_clear_spec (v : VecBuf) :
    VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear.clear v ⦃ r => r.val = [] ⦄ := by
  simp [VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear.clear]

/-! ## Lemmas about the definitions of `Defs/Compression.lean` -/

open Defs

theorem chunksOf_nil (n : Nat) : chunksOf n [] = [] := by
  rw [chunksOf]; simp

theorem chunksOf_cons (n : Nat) (hn : 0 < n) (bs : List U8) (hbs : bs ≠ []) :
    chunksOf n bs = bs.take n :: chunksOf n (bs.drop n) := by
  rw [chunksOf]; simp [hbs]; omega

theorem leNat_take3_lt (bs : List U8) : leNat (bs.take 3) < 2 ^ 24 := by
  have := PBUtil.leNat_lt (bs.take 3)
  have : 2 ^ (8 * (bs.take 3).length) ≤ 2 ^ 24 :=
    Nat.pow_le_pow_right (by norm_num) (by simp; omega)
  omega

theorem compHeaderRead_lt (bs : List U8) :
    (compHeaderRead bs).1 < 2 ^ 24 ∧ (compHeaderRead bs).2.2 < 2 ^ 24 :=
  ⟨leNat_take3_lt bs, leNat_take3_lt (bs.drop 4)⟩

theorem deflates_len (chunk z : List U8) (hz : Deflates chunk z) : 0 < z.length ∧ z.length < chunk.length := by
  obtain ⟨d, c, v, hc, hv, hr⟩ := hz
  have := Trusted.deflateResult_short d c v hr
  subst hc hv; exact this

theorem inflateList_deflates (i : flate2.mem.Decompress) (chunk z : List U8) (hz : Deflates chunk z) :
    inflateList i z chunk.length = .Ok chunk := by
  obtain ⟨d, c, v, hc, hv, hr⟩ := hz
  have hzl : z.length ≤ Usize.max := by rw [← hv]; scalar_tac
  have hcl : chunk.length ≤ Usize.max := by rw [← hc]; scalar_tac
  unfold inflateList
  rw [dite_eq_left hzl]
  obtain ⟨w, hw, hwv⟩ := Trusted.inflate_deflate d c v hr i (Slice.from z hzl) (by simp [hv])
  have e : (⟨BitVec.ofNat _ chunk.length⟩ : Usize) = Slice.len c := by
    apply UScalar.eq_of_val_eq
    simp only [Slice.len_val]
    show (BitVec.ofNat _ chunk.length).toNat = _
    simp only [BitVec.toNat_ofNat]
    have hlen : c.length = chunk.length := by rw [← hc]
    rw [hlen]
    apply Nat.mod_eq_of_lt
    have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by simp [Usize.max, Usize.numBits]
    have : 0 < 2 ^ UScalarTy.Usize.numBits := by positivity
    omega
  rw [e, hw]
  simp [hwv, hc]

theorem dropWhile_append_all {α : Type} (p : α → Bool) (l r : List α) (h : ∀ x ∈ l, p x = true) :
    (l ++ r).dropWhile p = r.dropWhile p := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem takeWhile_append_all {α : Type} (p : α → Bool) (l r : List α) (h : ∀ x ∈ l, p x = true) :
    (l ++ r).takeWhile p = l ++ r.takeWhile p := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem decimal_digit (a : Nat) : ∀ x ∈ decimalBytes (a : Int), 48 ≤ x.val ∧ x.val ≤ 57 := by
  intro x hx
  simp only [decimalBytes, show ¬ ((a : Int) < 0) by omega, ↓reduceIte, List.nil_append, List.mem_map] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  have := ConvInts.digit_bounds _ c hc
  rw [ConvInts.byte_val _ (by omega)]
  exact this

theorem versionPart_decimal (a : Nat) (ha : a < 256) : versionPart (decimalBytes (a : Int)) = some (byte a) := by
  simp only [versionPart, ConvInts.asciiInt_decimalBytes, Option.bind_some]
  rw [ite_eq_left_of_eq_true _ _ (by simp; omega)]
  simp

end mysql_common.CompCodec
