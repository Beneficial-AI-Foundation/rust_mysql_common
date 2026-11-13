import Defs
import Proofs.Util.PacketsOkErr
import Proofs.Util.PacketsColStmt
import Proofs.Util.Constants
import Proofs.Misc.Raw.Bytes.U32Bytes
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Misc.Raw.Int.LeU64
import Proofs.Misc.Raw.Const.Const
import Proofs.Misc.VarlenUintSize
import Proofs.Defs.LemmasG
import Proofs.Packets.Sid
import Proofs.Util.Replication

/-! Statements for `struct ComBinlogDumpGtid and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts mysql_common.PCSUtil

namespace mysql_common

namespace GtidUtil

@[step] theorem constu8_default_spec {T : Type} (N : U8) (d : core.default.Default T) :
    misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default N d ⦃ _ => True ⦄ := by
  have e : misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default N d = ok () := by
    simp [misc.raw.int.ConstU8.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]
  rw [e]; exact (WP.spec_ok _).mpr trivial

@[step] theorem rawint_u64_default_spec :
    misc.raw.int.RawInt.Insts.CoreDefaultDefault.default misc.raw.int.LeU64.Insts.CoreDefaultDefault
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64 core.default.DefaultU64 ⦃ r => r.1.val = 0 ⦄ := by
  have e : misc.raw.int.RawInt.Insts.CoreDefaultDefault.default misc.raw.int.LeU64.Insts.CoreDefaultDefault
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64 core.default.DefaultU64 = ok (0#u64, ()) := by
    simp [misc.raw.int.RawInt.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default]
    rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

@[step] theorem const_flags_default_spec :
    misc.raw._const.Const.Insts.CoreDefaultDefault.default packets.BinlogDumpFlags.Insts.CoreDefaultDefault
      misc.raw.int.LeU16.Insts.CoreDefaultDefault ⦃ r => r.1.val = 0 ⦄ := by
  have e : misc.raw._const.Const.Insts.CoreDefaultDefault.default packets.BinlogDumpFlags.Insts.CoreDefaultDefault
      misc.raw.int.LeU16.Insts.CoreDefaultDefault = ok (0#u16, ()) := by
    simp [misc.raw._const.Const.Insts.CoreDefaultDefault.default, core.marker.PhantomData.Insts.CoreDefaultDefault.default,
      packets.BinlogDumpFlags.Insts.CoreDefaultDefault.default, packets.BinlogDumpFlags.empty]
    rfl
  rw [e]; exact (WP.spec_ok _).mpr rfl

theorem seq_sid_new_vec (v : alloc.vec.Vec packets.Sid) :
    misc.raw.seq.Seq.new misc.raw.int.LeU64 packets.Sid.Insts.CoreCloneClone
      (core.convert.IntoFrom (alloc.borrow.CowASliceVec.Insts.CoreConvertFromVec
        packets.Sid.Insts.CoreCloneClone)) v = ok (.Owned v, ()) :=
  misc.raw.seq.Seq.new_eq _ _ _ _ _ rfl

@[step] theorem seq_sid_default_spec :
    misc.raw.seq.Seq.Insts.CoreDefaultDefault.default misc.raw.int.LeU64 packets.Sid.Insts.CoreCloneClone
      ⦃ r => cowList r.1 = [] ⦄ := by
  unfold misc.raw.seq.Seq.Insts.CoreDefaultDefault.default
  rw [seq_sid_new_vec]
  exact (WP.spec_ok _).mpr (by simp [cowList, alloc.vec.Vec.new])

@[step] theorem seq_is_empty_spec {T U : Type} (cl : core.clone.Clone T) (s : misc.raw.seq.Seq T U) :
    misc.raw.seq.Seq.is_empty cl s ⦃ b => b = decide (cowList s.1 = []) ⦄ := by
  unfold misc.raw.seq.Seq.is_empty
  obtain ⟨c, u⟩ := s
  step with cow_deref_spec as ⟨sl, hsl⟩
  simp [core.slice.Slice.is_empty, hsl]

@[step] theorem flags_remove_spec (f g : packets.BinlogDumpFlags) :
    packets.BinlogDumpFlags.remove f g ⦃ r => r.val = andNot 16 f.val g.val ⦄ := by
  simp [packets.BinlogDumpFlags.remove, packets.BinlogDumpFlags.difference, lift, andNot,
    ConstUtil.u16_val_not]

@[step] theorem flags_insert_spec (f g : packets.BinlogDumpFlags) :
    packets.BinlogDumpFlags.insert f g ⦃ r => r.val = f.val ||| g.val ⦄ := by
  simp [packets.BinlogDumpFlags.insert, packets.BinlogDumpFlags.union, lift]

theorem through_gtid_val : (packets.BinlogDumpFlags.BINLOG_THROUGH_GTID : U16).val = BINLOG_THROUGH_GTID := by
  simp [packets.BinlogDumpFlags.BINLOG_THROUGH_GTID, BINLOG_THROUGH_GTID]

theorem u32bytes_as_bytes_spec (rb : misc.raw.bytes.RawBytes misc.raw.bytes.U32Bytes Unit) :
    misc.raw.bytes.RawBytes.as_bytes misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ s => s.val = (cowList rb.1).take (2 ^ 32 - 1) ⦄ := by
  have ⟨m, hm, hmv⟩ := spec_eq_ok misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec
  apply WP.spec_mono (misc.raw.bytes.RawBytes.as_bytes_spec _ m hm rb)
  intro s hs; rw [hs, hmv]

theorem u32bytes_as_str_spec (rb : misc.raw.bytes.RawBytes misc.raw.bytes.U32Bytes Unit) :
    misc.raw.bytes.RawBytes.as_str misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ c => LossyUtf8Valid ((cowList rb.1).take (2 ^ 32 - 1)) c ⦄ := by
  unfold misc.raw.bytes.RawBytes.as_str
  step with u32bytes_as_bytes_spec as ⟨s, hs⟩
  simp only [misc.trusted.from_utf8_lossy, WP.spec_ok]
  intro hu
  rw [← hs] at hu
  rw [ite_eq_left_iff.mpr (fun h => absurd ((Defs.isUtf8_iff_isValidUTF8 _).1 hu) h)]
  exact ⟨s, rfl, hs⟩

theorem eq_ok_of_spec {α : Type} {m : Result α} {x : α} (h : m ⦃ y => y = x ⦄) : m = ok x := by
  obtain ⟨y, hy, rfl⟩ := spec_eq_ok h; exact hy

theorem tag_clone_eq (t : packets.Tag) (ht : (strCowBytes t).length ≤ Usize.max) :
    packets.Tag.Insts.CoreCloneClone.clone t = ok t := by
  apply eq_ok_of_spec
  unfold packets.Tag.Insts.CoreCloneClone.clone
  apply WP.spec_bind (Pₘ := fun c => c = t)
  · cases t with
    | Borrowed b => exact (WP.spec_ok _).mpr rfl
    | Owned o =>
      have hu := CBTUtil.u8sOf_toUTF8 o
      simp only [String.toUTF8_eq_toByteArray] at hu
      simp only [strCowBytes] at ht
      simp only [alloc.borrow.Cow.Insts.CoreCloneClone.clone]
      apply WP.spec_bind (Pₘ := fun b : Str => b.val = utf8 o)
      · simp only [alloc.string.String.Insts.CoreBorrowBorrowStr.borrow, hu,
          String.toUTF8_eq_toByteArray]
        rw [dite_eq_left_of_eq_true (eq_true ht)]
        exact (WP.spec_ok _).mpr (Slice.from_val _ _)
      · intro b hb
        apply WP.spec_bind (Pₘ := fun o' => o' = o)
        · simp only [Str.Insts.AllocBorrowToOwnedString.to_owned, hb,
            CBTUtil.fromUTF8?_utf8]
          exact (WP.spec_ok _).mpr rfl
        · intro o' ho'; exact (WP.spec_ok _).mpr (by rw [ho'])
  · intro c hc; exact (WP.spec_ok _).mpr hc

theorem sid_clone_eq (x : packets.Sid) (ht : ∀ t, x.tag = some t → (strCowBytes t).length ≤ Usize.max) :
    packets.Sid.Insts.CoreCloneClone.clone x = ok x := by
  obtain ⟨u, tag, ⟨c, pd⟩⟩ := x
  apply eq_ok_of_spec
  unfold packets.Sid.Insts.CoreCloneClone.clone
  apply WP.spec_bind (Pₘ := fun a => a = u)
  · exact WP.spec_mono (core.array.CloneArray.clone_spec core.clone.CloneU8 u (by intros; rfl)) (fun _ h => h.symm)
  intro a ha
  apply WP.spec_bind (Pₘ := fun o => o = tag)
  · cases tag with
    | none => exact (WP.spec_ok _).mpr rfl
    | some t =>
      simp only [core.option.Option.Insts.CoreCloneClone.clone]
      rw [tag_clone_eq t (ht t rfl)]
      simp
  intro o ho
  apply WP.spec_bind (Pₘ := fun s => s = ((c, pd) : misc.raw.seq.Seq packets.GnoInterval misc.raw.int.LeU64))
  · unfold misc.raw.seq.Seq.Insts.CoreCloneClone.clone
    apply WP.spec_bind (Pₘ := fun c1 => c1 = c)
    · cases c with
      | Borrowed b => exact (WP.spec_ok _).mpr rfl
      | Owned v =>
        simp only [alloc.borrow.Cow.Insts.CoreCloneClone.clone, Slice.Insts.AllocBorrowToOwnedVec.to_owned]
        apply WP.spec_bind (Pₘ := fun b => b = v.deref) ((WP.spec_ok _).mpr rfl)
        intro b hb
        subst hb
        apply WP.spec_bind (alloc.slice.Slice.to_vec_spec packets.GnoInterval.Insts.CoreCloneClone
          (alloc.vec.Vec.deref v) (fun y _ => rfl))
        intro v' hv'
        have : v' = v := by
          apply alloc.vec.Vec.ext
          have := congrArg (fun x : Slice packets.GnoInterval => x.val) hv'
          simpa [alloc.vec.Vec.deref, alloc.vec.Vec.val] using this.symm
        subst this
        exact (WP.spec_ok _).mpr rfl
    · intro c1 hc1
      simp only [core.marker.PhantomData.Insts.CoreCloneClone.clone, hc1]
      apply WP.spec_bind (Pₘ := fun p => p = pd) ((WP.spec_ok _).mpr rfl)
      intro p hp; subst hp
      exact (WP.spec_ok _).mpr rfl
  intro s hs
  exact (WP.spec_ok _).mpr (by rw [ha, ho, hs])

theorem sat_add_val {ty : UScalarTy} (x y : UScalar ty) (h : x.val + y.val ≤ UScalar.max ty) :
    (UScalar.saturating_add x y).val = x.val + y.val := by
  simp only [UScalar.saturating_add, Nat.min_eq_right h]
  have : x.val + y.val < 2 ^ ty.numBits := by
    have := UScalar.max_def ty; have : 0 < 2 ^ ty.numBits := Nat.two_pow_pos _; omega
  rw [PBUtil.val_mk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]

@[step] theorem seq_len_spec {T U : Type} (cl : core.clone.Clone T) (s : misc.raw.seq.Seq T U) :
    misc.raw.seq.Seq.len cl s ⦃ n => n.val = (cowList s.1).length ⦄ := by
  unfold misc.raw.seq.Seq.len
  obtain ⟨c, u⟩ := s
  step with cow_deref_spec as ⟨sl, hsl⟩
  simp [Slice.len, hsl]

theorem sid_len_spec (x : packets.Sid) (h : (sidEnc (SidV.of x)).length < 2 ^ 32) :
    packets.Sid.len x ⦃ n => n.val = (sidEnc (SidV.of x)).length ⦄ := by
  rw [Replication.length_sidEnc] at *
  simp only [SidV.of, List.length_map] at *
  unfold packets.Sid.len
  step*
  have hu : (↑x.uuid : List U8).length = 16 := by simp
  have hl : len.val = 16 := by rw [len_post]; simp [packets.UUID_LEN]
  have hi2 : i2.val = i1.val := by rw [i2_post]; simp
  have hl1 : len1.val = 24 := by
    rw [len1_post, core.num.U64.saturating_add, sat_add_val _ _ (by rw [hl]; simp [UScalar.max_def])]
    rw [hl]; simp
  simp only [core.num.U64.saturating_add]
  rw [sat_add_val _ _ (by rw [hl1, hi2, i1_post, i_post, UScalar.max_def]; simp; omega), hl1, hi2, i1_post, i_post, hu]
  omega

theorem sid_tagged_len_spec (x : packets.Sid) (h : (sidTaggedEnc (SidV.of x)).length < 2 ^ 32) :
    packets.Sid.tagged_len x ⦃ n => n.val = (sidTaggedEnc (SidV.of x)).length ⦄ := by
  have hlen : (sidTaggedEnc (SidV.of x)).length = 16 + varlenUintSize ((x.tag.map strCowBytes).getD []).length
      + ((x.tag.map strCowBytes).getD []).length + 8 + 16 * (cowList x.intervals.1).length := by
    have hu : (↑x.uuid : List U8).length = 16 := by simp
    simp only [sidTaggedEnc, SidV.of, intervalsEnc, List.length_append, IntAndMisc.varlenUint_length',
      PBUtil.length_leBytes, Replication.length_flatMap_gnoEnc, List.length_map, hu]
    omega
  rw [hlen] at h ⊢
  unfold packets.Sid.tagged_len
  have hmax := Replication.usize_max_ge
  step with SidUtil.tag_str_spec x (by omega) as ⟨ts, hts⟩
  step*
  apply WP.spec_bind (Pₘ := fun i : Usize => i.val = ts.val.length) ((WP.spec_ok _).mpr (by simp [Slice.len]))
  intro i hi
  step*
  step with misc.varlen_uint_size_spec as ⟨i2, hi2⟩
  step*
  have hl : len.val = 16 := by rw [len_post]; simp [packets.UUID_LEN]
  have hm : UScalar.max .U64 = 2 ^ 64 - 1 := by simp [UScalar.max_def]
  have e1 : i1.val = ts.val.length := by rw [i1_post]; simp [hi]
  have e3 : i3.val = varlenUintSize ts.val.length := by rw [i3_post]; simp [hi2, e1]
  have e4 : i4.val = ts.val.length := by rw [i4_post]; simp [hi]
  have e7 : i7.val = 16 * (cowList x.intervals.1).length := by rw [i7_post]; simp [i6_post, i5_post]; ring
  have h8 : (8#u64).val = 8 := rfl
  rw [hts] at e1 e3 e4
  simp only [core.num.U64.saturating_add] at len1_post len2_post len3_post ⊢
  have f1 : len1.val = 16 + varlenUintSize ((Option.map strCowBytes x.tag).getD []).length := by
    rw [len1_post, sat_add_val _ _ (by rw [hm, hl, e3]; omega), hl, e3]
  have f2 : len2.val = len1.val + ((Option.map strCowBytes x.tag).getD []).length := by
    rw [len2_post, sat_add_val _ _ (by rw [hm, f1, e4]; omega), e4]
  have f3 : len3.val = len2.val + 8 := by
    rw [len3_post, sat_add_val _ _ (by rw [hm, f2, f1, h8]; omega), h8]
  rw [sat_add_val _ _ (by rw [hm, f3, f2, f1, e7]; omega)]
  omega

/-- The SID encoder of a format. -/
def encOf (tagged : Bool) : SidV → List U8 := if tagged then sidTaggedEnc else sidEnc

theorem any_sid_tagged_spec (sids : Slice packets.Sid) (k : Nat) : ∀ (i : Usize), sids.length = i.val + k →
    packets.any_sid_tagged sids i ⦃ b => b = (sids.val.drop i.val).any (fun s => s.tag.isSome) ⦄ := by
  induction k with
  | zero =>
    intro i hi
    unfold packets.any_sid_tagged
    have : ¬ i < Slice.len sids := by simp [Slice.len] at *; scalar_tac
    simp only [this, ↓reduceIte]
    apply (WP.spec_ok _).mpr
    simp only [Slice.length] at hi
    rw [List.drop_of_length_le (by omega)]; rfl
  | succ k ih =>
    intro i hi
    unfold packets.any_sid_tagged
    have : i < Slice.len sids := by simp [Slice.len] at *; scalar_tac
    simp only [this, ↓reduceIte]
    step as ⟨x, hx⟩
    rw [packets.Sid.impl.tag_eq]
    apply spec_bind_ok
    have hlt : i.val < sids.val.length := by simp [Slice.length] at hi; omega
    have hd : sids.val.drop i.val = x :: sids.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt, hx]
    rw [hd]
    by_cases ht : x.tag.isSome = true
    · simp only [ht, ↓reduceIte]
      apply (WP.spec_ok _).mpr
      simp [ht]
    · simp only [ht, Bool.false_eq_true, ↓reduceIte]
      step as ⟨i2, hi2⟩
      apply WP.spec_mono (ih i2 (by simp [Slice.length] at hi ⊢; omega))
      intro b hb
      simp at ht
      simp [hb, hi2, ht]

theorem sid_block_len_from_spec (sids : Slice packets.Sid) (tagged : Bool) (k : Nat) :
    ∀ (i : Usize) (len : U32), sids.length = i.val + k →
    len.val + (((sids.val.drop i.val).map SidV.of).flatMap (encOf tagged)).length < 2 ^ 32 →
    packets.sid_block_len_from sids tagged i len ⦃ r =>
      r.val = len.val + (((sids.val.drop i.val).map SidV.of).flatMap (encOf tagged)).length ⦄ := by
  induction k with
  | zero =>
    intro i len hi _
    unfold packets.sid_block_len_from
    have : ¬ i < Slice.len sids := by simp [Slice.len] at *; scalar_tac
    simp only [this, ↓reduceIte]
    apply (WP.spec_ok _).mpr
    simp only [Slice.length] at hi
    rw [List.drop_of_length_le (by omega)]; simp
  | succ k ih =>
    intro i len hi hb
    unfold packets.sid_block_len_from
    have : i < Slice.len sids := by simp [Slice.len] at *; scalar_tac
    simp only [this, ↓reduceIte]
    have hlt : i.val < sids.val.length := by simp [Slice.length] at hi; omega
    have hm : UScalar.max .U32 = 2 ^ 32 - 1 := by simp [UScalar.max_def]
    split
    · rename_i htg
      subst htg
      step as ⟨i2, hi2⟩
      step as ⟨x, hx⟩
      have hd : sids.val.drop i.val = x :: sids.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt, hx]
      rw [hd] at hb ⊢
      simp only [List.map_cons, List.flatMap_cons, List.length_append, encOf, ↓reduceIte] at hb ⊢
      step with sid_tagged_len_spec x (by omega) as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have e4 : i4.val = (sidTaggedEnc (SidV.of x)).length := by
        rw [hi4]; simp only [UScalar.cast_val_eq, hi3]; apply Nat.mod_eq_of_lt; simp; omega
      step as ⟨i5, hi5⟩
      have e5 : i5.val = len.val + (sidTaggedEnc (SidV.of x)).length := by
        rw [hi5, core.num.U32.saturating_add, sat_add_val _ _ (by rw [hm, e4]; omega), e4]
      apply WP.spec_mono (ih i2 i5 (by simp [Slice.length] at hi ⊢; omega)
        (by rw [hi2, e5]; simp only [encOf, ↓reduceIte] at hb ⊢; omega))
      intro r hr
      rw [hr, e5, hi2]; simp only [encOf, ↓reduceIte]; omega
    · step as ⟨i2, hi2⟩
      step as ⟨x, hx⟩
      have hd : sids.val.drop i.val = x :: sids.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt, hx]
      rename_i htg
      have htf : tagged = false := by simpa using htg
      subst htf
      rw [hd] at hb ⊢
      simp only [List.map_cons, List.flatMap_cons, List.length_append, encOf, Bool.false_eq_true,
        ↓reduceIte] at hb ⊢
      step with sid_len_spec x (by omega) as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have e4 : i4.val = (sidEnc (SidV.of x)).length := by
        rw [hi4]; simp only [UScalar.cast_val_eq, hi3]; apply Nat.mod_eq_of_lt; simp; omega
      step as ⟨i5, hi5⟩
      have e5 : i5.val = len.val + (sidEnc (SidV.of x)).length := by
        rw [hi5, core.num.U32.saturating_add, sat_add_val _ _ (by rw [hm, e4]; omega), e4]
      apply WP.spec_mono (ih i2 i5 (by simp [Slice.length] at hi ⊢; omega)
        (by rw [hi2, e5]; simp only [encOf, Bool.false_eq_true, ↓reduceIte] at hb ⊢; omega))
      intro r hr
      rw [hr, e5, hi2]; simp only [encOf, Bool.false_eq_true, ↓reduceIte] at hr ⊢; omega

theorem serialize_sids_from_spec (sids : Slice packets.Sid) (tagged : Bool) (k : Nat) :
    ∀ (i : Usize) (buf : alloc.vec.Vec U8), sids.length = i.val + k →
    buf.length + (((sids.val.drop i.val).map SidV.of).flatMap (encOf tagged)).length ≤ Usize.max →
    packets.serialize_sids_from sids tagged i buf ⦃ b =>
      b.val = buf.val ++ ((sids.val.drop i.val).map SidV.of).flatMap (encOf tagged) ⦄ := by
  induction k with
  | zero =>
    intro i buf hi _
    unfold packets.serialize_sids_from
    have : ¬ i < Slice.len sids := by simp [Slice.len] at *; scalar_tac
    simp only [this, ↓reduceIte]
    apply (WP.spec_ok _).mpr
    simp only [Slice.length] at hi
    rw [List.drop_of_length_le (by omega)]; simp
  | succ k ih =>
    intro i buf hi hb
    unfold packets.serialize_sids_from
    have : i < Slice.len sids := by simp [Slice.len] at *; scalar_tac
    simp only [this, ↓reduceIte]
    have hlt : i.val < sids.val.length := by simp [Slice.length] at hi; omega
    split
    · rename_i htg
      subst htg
      step as ⟨x, hx⟩
      have hd : sids.val.drop i.val = x :: sids.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt, hx]
      rw [hd] at hb ⊢
      simp only [List.map_cons, List.flatMap_cons, List.length_append, encOf, ↓reduceIte] at hb ⊢
      step with packets.Sid.serialize_tagged_spec x buf (by omega) as ⟨b1, hb1⟩
      step as ⟨i2, hi2⟩
      apply WP.spec_mono (ih i2 b1 (by simp [Slice.length] at hi ⊢; omega)
        (by simp only [alloc.vec.Vec.length, hb1, List.length_append, hi2, encOf, ↓reduceIte] at hb ⊢; omega))
      intro r hr
      rw [hr, hb1, hi2]; simp [encOf]
    · rename_i htg
      have htf : tagged = false := by simpa using htg
      subst htf
      step as ⟨x, hx⟩
      have hd : sids.val.drop i.val = x :: sids.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlt, hx]
      rw [hd] at hb ⊢
      simp only [List.map_cons, List.flatMap_cons, List.length_append, encOf, Bool.false_eq_true,
        ↓reduceIte] at hb ⊢
      step with packets.Sid.Insts.Mysql_commonProtoMySerialize.serialize_spec x buf (by omega) as ⟨b1, hb1⟩
      step as ⟨i2, hi2⟩
      apply WP.spec_mono (ih i2 b1 (by simp [Slice.length] at hi ⊢; omega)
        (by simp only [alloc.vec.Vec.length, hb1, List.length_append, hi2, encOf, Bool.false_eq_true,
          ↓reduceIte] at hb ⊢; omega))
      intro r hr
      rw [hr, hb1, hi2]; simp [encOf]

theorem leBytes_succ_top (c : Nat) : ∀ (k n : Nat), n < 2 ^ (8 * k) →
    leBytes (k + 1) (n + 2 ^ (8 * k) * c) = leBytes k n ++ [byte c] := by
  intro k
  induction k with
  | zero => intro n hn; simp at hn; subst hn; simp [leBytes]
  | succ k ih =>
    intro n hn
    have hp : 2 ^ (8 * (k + 1)) * c = 256 * (2 ^ (8 * k) * c) := by ring
    have e1 : (n + 2 ^ (8 * (k + 1)) * c) / 256 = n / 256 + 2 ^ (8 * k) * c := by
      rw [hp]; generalize 2 ^ (8 * k) * c = P; omega
    have e2 : byte (n + 2 ^ (8 * (k + 1)) * c) = byte n := by
      apply UScalar.eq_of_val_eq
      rw [PBUtil.byte_val, PBUtil.byte_val, hp]; generalize 2 ^ (8 * k) * c = P; omega
    rw [show k + 1 + 1 = (k + 1) + 1 from rfl, leBytes, e2, e1,
      ih (n / 256) (by rw [show 8 * (k + 1) = 8 * k + 8 by ring, pow_add] at hn; omega)]
    simp [leBytes]

theorem n_sids_header_spec (tagged : Bool) (n : U64) (hn : n.val < 2 ^ 48) :
    packets.n_sids_header tagged n ⦃ r => leBytes 8 r.val = nSidsHeader tagged n.val ⦄ := by
  unfold packets.n_sids_header
  cases tagged
  · simp only [Bool.false_eq_true, ↓reduceIte]
    step*
    have hi : i.val = 0 := by rw [i_post]; simp
    have hi1 : i1.val = 0 := by rw [i1_post, hi]; simp
    simp only [nSidsHeader, Bool.false_eq_true, ↓reduceIte, UScalar.val_or, hi1, Nat.or_zero]
  · simp only [↓reduceIte]
    step*
    have hs : U64.size = 2 ^ 64 := by simp [U64.size_def, U64.numBits_def]
    have hi : i.val = n.val * 256 := by
      rw [i_post, Nat.shiftLeft_eq, hs]; apply Nat.mod_eq_of_lt; omega
    have hi1 : i1.val = 1 := by rw [i1_post]; simp
    have hi2 : i2.val = 2 ^ 56 := by rw [i2_post, hi1, hs]; rfl
    have hor : i.val ||| i2.val = n.val * 256 + 2 ^ 56 * 1 := by
      rw [hi, hi2, Nat.lor_comm, show (2:Nat) ^ 56 = 2 ^ 56 * 1 by rfl, ← Nat.two_pow_add_eq_or_of_lt (by omega)]; ring
    simp only [UScalar.val_or, hor, nSidsHeader, ↓reduceIte]
    rw [show 8 = 7 + 1 from rfl, show (2:Nat) ^ 56 = 2 ^ (8 * 7) from rfl, leBytes_succ_top 1 7 _ (by omega)]
    rw [show 7 = 6 + 1 from rfl, leBytes, Nat.mul_div_cancel _ (by norm_num)]
    have hb : byte (n.val * 256) = byte 0 := by
      apply UScalar.eq_of_val_eq
      simp [PBUtil.byte_val]
    rw [hb]

theorem const_flags_ser (x : misc.raw._const.Const packets.BinlogDumpFlags misc.raw.int.LeU16)
    (buf : alloc.vec.Vec U8) (h : buf.length + 2 ≤ Usize.max) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize packets.BinlogDumpFlags.Insts.CoreMarkerCopy
      (core.convert.IntoFrom U16.Insts.CoreConvertFromBinlogDumpFlags)
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 x buf
      ⦃ b => b.val = buf.val ++ leBytes 2 x.1.val ⦄ := by
  rw [misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq _ _ _ _ x.1 rfl]
  exact misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec _ _ h

theorem u32bytes_ser (rb : misc.raw.bytes.RawBytes misc.raw.bytes.U32Bytes Unit) (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 + min (cowList rb.1).length (2 ^ 32 - 1) ≤ Usize.max) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb buf
      ⦃ b => b.val = buf.val ++ leBytes 4 (min (cowList rb.1).length (2 ^ 32 - 1)) ++
        (cowList rb.1).take (2 ^ 32 - 1) ⦄ := by
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  apply WP.spec_mono (misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf
    (by simp only [Slice.length, hs]; omega))
  intro b hb
  rw [hb]
  simp [Slice.length, hs]

theorem rawint_u64_ser (x : misc.raw.int.RawInt misc.raw.int.LeU64 U64) (buf : alloc.vec.Vec U8)
    (h : buf.length + 8 ≤ Usize.max) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64 x buf
      ⦃ b => b.val = buf.val ++ leBytes 8 x.1.val ⦄ := by
  rw [misc.raw.int.RawInt.serialize_eq]
  exact misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec _ _ h

theorem length_le_flatMap_pos {α β : Type} (f : α → List β) (hf : ∀ x, 1 ≤ (f x).length) :
    ∀ l : List α, l.length ≤ (l.flatMap f).length := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.length_cons, List.flatMap_cons, List.length_append]; have := hf a; omega

theorem encOf_pos (t : Bool) (x : SidV) : 1 ≤ (encOf t x).length := by
  cases t <;> simp [encOf, sidEnc, sidTaggedEnc, intervalsEnc, PBUtil.length_leBytes] <;> omega

theorem sidRead_some_len {bs : List U8} {sv : SidV} {r : List U8} (h : sidRead bs = .done (some sv) r) :
    r.length + 16 ≤ bs.length := by
  unfold sidRead at h
  split at h
  · simp at h
  · rename_i h16
    split at h
    · rename_i is rest hi
      simp only [ReadOut.done.injEq] at h
      rw [← h.2]
      have := (Replication.intervalsRead_suffix hi).length_le
      simp at this; omega
    all_goals simp at h

theorem sidTaggedRead_some_len {bs : List U8} {sv : SidV} {r : List U8}
    (h : sidTaggedRead bs = .done (some sv) r) : r.length + 16 ≤ bs.length := by
  unfold sidTaggedRead at h
  split at h
  · simp at h
  · rename_i h16
    dsimp only at h
    split at h
    · simp at h
    · rename_i tl r' hv
      have h1 := (Replication.varlenUintDecode_suffix hv).length_le
      simp only [List.length_drop] at h1
      split at h
      · split at h
        · rename_i is rest hi
          simp only [ReadOut.done.injEq] at h
          rw [← h.2]
          have := (Replication.intervalsRead_suffix hi).length_le
          omega
        all_goals simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · split at h <;> simp at h

theorem untagged_loop (h64 : Target64) (n : Nat) : ∀ (buf : io.ParseBuf) (nn : U64)
    (acc : alloc.vec.Vec packets.Sid), nn.val = n → 16 * acc.val.length + buf.length ≤ Usize.max →
    (∀ o r, sidsRead false n buf.val = .done o r → packets.deserialize_untagged_sids buf nn acc ⦃ res _ =>
      (okPart res).map (fun v => v.val.map SidV.of) = o.map (fun l => acc.val.map SidV.of ++ l) ⦄) ∧
    (∀ e, sidsRead false n buf.val = .panic e → packets.deserialize_untagged_sids buf nn acc = fail e) := by
  induction n with
  | zero =>
    intro buf nn acc hn _
    have hz : ¬ nn > 0#u64 := by scalar_tac
    refine ⟨fun o r h => ?_, fun e h => ?_⟩
    · simp only [sidsRead, ReadOut.done.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      unfold packets.deserialize_untagged_sids
      simp only [hz, ↓reduceIte]
      apply (WP.spec_ok _).mpr
      simp [okPart]
    · simp [sidsRead] at h
  | succ n ih =>
    intro buf nn acc hn hb
    have hp : nn > 0#u64 := by scalar_tac
    have hsz : packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none :=
      packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
    have hparse : ∀ b : io.ParseBuf, io.ParseBuf.parse packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple b () =
        packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () b :=
      fun b => io.ParseBuf.parse_of_size_none _ _ _ (by simp [hsz])
    unfold packets.deserialize_untagged_sids
    simp only [hp, ↓reduceIte, hparse]
    cases hs : sidRead buf.val with
    | done o rest =>
      cases o with
      | some sv =>
        have hl := sidRead_some_len hs
        obtain ⟨⟨r1, b1⟩, he, hr1, hr2⟩ := spec_eq_ok
          (packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf _ _ hs)
        rw [he]
        cases r1 with
        | Err _ => simp [okPart] at hr1
        | Ok x =>
        simp only [okPart, Option.map_some, Option.some.injEq] at hr1
        have hpush : acc.val.length < Usize.max := by simp [Slice.length] at hb; omega
        obtain ⟨acc1, hacc1, hacc1v⟩ := spec_eq_ok (alloc.vec.Vec.push_spec acc x hpush)
        obtain ⟨nn1, hnn1, hnn1v⟩ := spec_eq_ok (show (nn - 1#u64) ⦃ z => z.val = nn.val - 1 ⦄ by step*)
        have hb1 : 16 * acc1.val.length + b1.length ≤ Usize.max := by
          simp only [Slice.length] at hb ⊢; rw [hacc1v, hr2]; simp; omega
        obtain ⟨ihd, ihp⟩ := ih b1 nn1 acc1 (by omega) hb1
        refine ⟨fun o r h => ?_, fun e h => ?_⟩
        · simp only [sidsRead, Bool.false_eq_true, ↓reduceIte, hs] at h
          simp only [hnn1]
          show WP.spec (Std.bind (ok (core.result.Result.Ok x, b1)) _) _
          simp only [bind_ok]
          show WP.spec (Std.bind (acc.push x) _) _
          rw [hacc1]
          simp only [bind_ok]
          rw [← hr2] at h
          split at h
          · rename_i ss rest' hss
            simp only [ReadOut.done.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            apply WP.spec_mono (ihd _ _ hss)
            rintro ⟨res, _⟩ hres
            simp only [WP.uncurry'_pair] at hres ⊢
            rw [hres, hacc1v]; simp [hr1]
          · rename_i rest' hss
            simp only [ReadOut.done.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            apply WP.spec_mono (ihd _ _ hss)
            rintro ⟨res, _⟩ hres
            simp only [WP.uncurry'_pair] at hres ⊢
            rw [hres]; simp
          · simp at h
          · simp at h
        · simp only [sidsRead, Bool.false_eq_true, ↓reduceIte, hs] at h
          simp only [hnn1]
          show (Std.bind (ok (core.result.Result.Ok x, b1)) _) = _
          simp only [bind_ok]
          show (Std.bind (acc.push x) _) = _
          rw [hacc1]
          simp only [bind_ok]
          rw [← hr2] at h
          split at h
          · simp at h
          · simp at h
          · rename_i e' hss
            simp only [ReadOut.panic.injEq] at h
            subst h
            exact ihp _ hss
          · simp at h
      | none =>
        obtain ⟨⟨r1, b1⟩, he, hr1, hr2⟩ := spec_eq_ok
          (packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf _ _ hs)
        rw [he]
        cases r1 with
        | Ok _ => simp [okPart] at hr1
        | Err err =>
        refine ⟨fun o r h => ?_, fun e h => ?_⟩
        · simp only [sidsRead, Bool.false_eq_true, ↓reduceIte, hs, ReadOut.done.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          show WP.spec (Std.bind (ok (core.result.Result.Err err, b1)) _) _
          simp only [bind_ok]
          apply (WP.spec_ok _).mpr
          simp [okPart]
        · simp [sidsRead, hs] at h
    | panic err =>
      have hf := packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_overflow h64 buf err hs
      refine ⟨fun o r h => ?_, fun e h => ?_⟩
      · simp [sidsRead, hs] at h
      · simp only [sidsRead, Bool.false_eq_true, ↓reduceIte, hs, ReadOut.panic.injEq] at h
        subst h
        rw [hf]; simp
    | unknown =>
      refine ⟨fun o r h => ?_, fun e h => ?_⟩
      · simp [sidsRead, hs] at h
      · simp [sidsRead, hs] at h

theorem tagged_loop (h64 : Target64) (n : Nat) : ∀ (buf : io.ParseBuf) (nn : U64)
    (acc : alloc.vec.Vec packets.Sid), nn.val = n → 16 * acc.val.length + buf.length ≤ Usize.max →
    (∀ o r, sidsRead true n buf.val = .done o r → packets.deserialize_tagged_sids buf nn acc ⦃ res _ =>
      (okPart res).map (fun v => v.val.map SidV.of) = o.map (fun l => acc.val.map SidV.of ++ l) ⦄) ∧
    (∀ e, sidsRead true n buf.val = .panic e → packets.deserialize_tagged_sids buf nn acc = fail e) := by
  induction n with
  | zero =>
    intro buf nn acc hn _
    have hz : ¬ nn > 0#u64 := by scalar_tac
    refine ⟨fun o r h => ?_, fun e h => ?_⟩
    · simp only [sidsRead, ReadOut.done.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      unfold packets.deserialize_tagged_sids
      simp only [hz, ↓reduceIte]
      apply (WP.spec_ok _).mpr
      simp [okPart]
    · simp [sidsRead] at h
  | succ n ih =>
    intro buf nn acc hn hb
    have hp : nn > 0#u64 := by scalar_tac
    unfold packets.deserialize_tagged_sids
    simp only [hp, ↓reduceIte]
    cases hs : sidTaggedRead buf.val with
    | done o rest =>
      cases o with
      | some sv =>
        have hl := sidTaggedRead_some_len hs
        obtain ⟨⟨r1, b1⟩, he, hr1, hr2⟩ := spec_eq_ok
          (packets.Sid.deserialize_tagged_spec h64 buf _ _ hs)
        rw [he]
        cases r1 with
        | Err _ => simp [okPart] at hr1
        | Ok x =>
        simp only [okPart, Option.map_some, Option.some.injEq] at hr1
        have hpush : acc.val.length < Usize.max := by simp [Slice.length] at hb; omega
        obtain ⟨acc1, hacc1, hacc1v⟩ := spec_eq_ok (alloc.vec.Vec.push_spec acc x hpush)
        obtain ⟨nn1, hnn1, hnn1v⟩ := spec_eq_ok (show (nn - 1#u64) ⦃ z => z.val = nn.val - 1 ⦄ by step*)
        have hb1 : 16 * acc1.val.length + b1.length ≤ Usize.max := by
          simp only [Slice.length] at hb ⊢; rw [hacc1v, hr2]; simp; omega
        obtain ⟨ihd, ihp⟩ := ih b1 nn1 acc1 (by omega) hb1
        refine ⟨fun o r h => ?_, fun e h => ?_⟩
        · simp only [sidsRead, ↓reduceIte, hs] at h
          simp only [hnn1]
          show WP.spec (Std.bind (ok (core.result.Result.Ok x, b1)) _) _
          simp only [bind_ok]
          show WP.spec (Std.bind (acc.push x) _) _
          rw [hacc1]
          simp only [bind_ok]
          rw [← hr2] at h
          split at h
          · rename_i ss rest' hss
            simp only [ReadOut.done.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            apply WP.spec_mono (ihd _ _ hss)
            rintro ⟨res, _⟩ hres
            simp only [WP.uncurry'_pair] at hres ⊢
            rw [hres, hacc1v]; simp [hr1]
          · rename_i rest' hss
            simp only [ReadOut.done.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            apply WP.spec_mono (ihd _ _ hss)
            rintro ⟨res, _⟩ hres
            simp only [WP.uncurry'_pair] at hres ⊢
            rw [hres]; simp
          · simp at h
          · simp at h
        · simp only [sidsRead, ↓reduceIte, hs] at h
          simp only [hnn1]
          show (Std.bind (ok (core.result.Result.Ok x, b1)) _) = _
          simp only [bind_ok]
          show (Std.bind (acc.push x) _) = _
          rw [hacc1]
          simp only [bind_ok]
          rw [← hr2] at h
          split at h
          · simp at h
          · simp at h
          · rename_i e' hss
            simp only [ReadOut.panic.injEq] at h
            subst h
            exact ihp _ hss
          · simp at h
      | none =>
        obtain ⟨⟨r1, b1⟩, he, hr1, hr2⟩ := spec_eq_ok
          (packets.Sid.deserialize_tagged_spec h64 buf _ _ hs)
        rw [he]
        cases r1 with
        | Ok _ => simp [okPart] at hr1
        | Err err =>
        refine ⟨fun o r h => ?_, fun e h => ?_⟩
        · simp only [sidsRead, ↓reduceIte, hs, ReadOut.done.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          show WP.spec (Std.bind (ok (core.result.Result.Err err, b1)) _) _
          simp only [bind_ok]
          apply (WP.spec_ok _).mpr
          simp [okPart]
        · simp [sidsRead, hs] at h
    | panic err =>
      have hf := packets.Sid.deserialize_tagged_panics h64 buf err hs
      refine ⟨fun o r h => ?_, fun e h => ?_⟩
      · simp [sidsRead, hs] at h
      · simp only [sidsRead, ↓reduceIte, hs, ReadOut.panic.injEq] at h
        subst h
        rw [hf]; simp
    | unknown =>
      refine ⟨fun o r h => ?_, fun e h => ?_⟩
      · simp [sidsRead, hs] at h
      · simp [sidsRead, hs] at h

theorem parse_unchecked_leu32_spec (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw.int.RawInt.deserialize_spec misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 4)) ∧ rest.val = buf.val.drop 4)
    (misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec buf h)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ hr
  simpa [Option.map_map] using hr

theorem flags_try_from_spec (p : U16) :
    packets.BinlogDumpFlags.Insts.CoreConvertTryFromU16UnknownBinlogDumpFlags.try_from p ⦃ r =>
      (okPart r).map (fun f : packets.BinlogDumpFlags => f.val) =
        if p.val &&& binlogDumpFlagsAll = p.val then some p.val else none ⦄ := by
  unfold packets.BinlogDumpFlags.Insts.CoreConvertTryFromU16UnknownBinlogDumpFlags.try_from
    packets.BinlogDumpFlags.from_bits packets.BinlogDumpFlags.from_bits_truncate packets.BinlogDumpFlags.all
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  have hv : i3.val = p.val &&& binlogDumpFlagsAll := by
    have h7 : i2 = 7#u16 := by apply UScalar.eq_of_val_eq; simp_all [UScalar.val_or]
    subst h7; rw [hi3]; simp [UScalar.val_and]; rfl
  split_ifs with h1 h2 h2
  · simp
  · exfalso; apply h2; rw [← hv, h1]
  · exfalso; apply h1; apply UScalar.eq_of_val_eq; rw [hv, h2]
  · simp

theorem parse_unchecked_flags_spec (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16
      packets.BinlogDumpFlags.Insts.CoreConvertTryFromU16UnknownBinlogDumpFlags
      packets.UnknownBinlogDumpFlags.Insts.CoreErrorError) buf () ⦃ r rest =>
      (okPart r).map (fun c => c.1.val) =
        (if leNat (buf.val.take 2) &&& binlogDumpFlagsAll = leNat (buf.val.take 2)
         then some (leNat (buf.val.take 2)) else none) ∧ rest.val = buf.val.drop 2 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16
    packets.BinlogDumpFlags.Insts.CoreConvertTryFromU16UnknownBinlogDumpFlags
    packets.UnknownBinlogDumpFlags.Insts.CoreErrorError buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 2)) ∧ rest.val = buf.val.drop 2)
    (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec buf h)
    (fun p o => o.map (fun c : packets.BinlogDumpFlags => c.val) =
        if p.val &&& binlogDumpFlagsAll = p.val then some p.val else none)
    flags_try_from_spec
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨o, ⟨ho, hrest⟩, hm⟩
  refine ⟨?_, hrest⟩
  cases o with
  | none => simp at ho
  | some p =>
    simp at ho hm
    rw [← ho]
    simpa [Option.map_map, Function.comp_def] using hm

theorem parse_unchecked_hdr_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple
        30#u8 packets.InvalidComBinlogDumpGtidHeader.Insts.CoreErrorError
        packets.InvalidComBinlogDumpGtidHeader.Insts.CoreDefaultDefault) buf () ⦃ r rest =>
      ((okPart r).isSome ↔ leNat (buf.val.take 1) = 30) ∧ rest.val = buf.val.drop 1 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  exact misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec 30#u8
    packets.InvalidComBinlogDumpGtidHeader.Insts.CoreErrorError
    packets.InvalidComBinlogDumpGtidHeader.Insts.CoreDefaultDefault
    ((WP.spec_ok _).mpr trivial) buf h

theorem parse_u32bytes_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
      misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple) buf () ⦃ r rest =>
      ((okPart r).map (fun rb => cowList rb.1), rest.val) = checkedLenPrefixed 4 buf.val ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq,
      misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq])]
  exact misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec _ () buf
    (fun o rest => (o, rest.val) = checkedLenPrefixed 4 buf.val)
    (misc.raw.bytes.U32Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf)

theorem branch_ok_eq {T E : Type} (v : T) :
    CoreOpsTry.branch (core.result.Result.Ok v : core.result.Result T E) =
      ok (core.ops.control_flow.ControlFlow.Continue v) := rfl

theorem branch_err_eq {T E : Type} (e : E) :
    CoreOpsTry.branch (core.result.Result.Err e : core.result.Result T E) =
      ok (core.ops.control_flow.ControlFlow.Break (core.result.Result.Err e)) := rfl

theorem from_residual_eq {T E : Type} (e : E) :
    CoreOpsTry_traitFromResidualResult.from_residual T (core.convert.FromSame E)
      (core.result.Result.Err e : core.result.Result Never E) = ok (core.result.Result.Err e) := by
  simp [CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]

theorem mask_shift (x : Nat) : (x &&& 72057594037927680) >>> 8 = x / 2 ^ 8 % 2 ^ 48 := by
  have hm : (72057594037927680 : Nat) = 2 ^ 8 * (2 ^ 48 - 1) := by norm_num
  apply Nat.eq_of_testBit_eq; intro j
  rw [hm, Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  rw [Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 48 <;> simp [hj, Nat.add_comm]

theorem mask_low (x : Nat) : x &&& 72057594037927935 = x % 2 ^ 56 := by
  rw [show (72057594037927935 : Nat) = 2 ^ 56 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

end GtidUtil

open GtidUtil

/-- `?` on an `Ok`: continue with the value. -/
local macro "gtid_ok_br" : tactic => `(tactic| (rw [branch_ok_eq]; apply spec_bind_ok; dsimp only))
/-- `?` on an `Err`: return it. -/
local macro "gtid_err_br" : tactic =>
  `(tactic| (rw [branch_err_eq]; apply spec_bind_ok; dsimp only; rw [from_residual_eq]; apply spec_bind_ok; apply (WP.spec_ok _).mpr))

/-- `ComBinlogDumpGtid::new(server_id)`: no flags, the server id, an empty file name, position
    0, no SIDs. -/
@[step]
theorem packets.ComBinlogDumpGtid.new_spec (server_id : U32) :
    packets.ComBinlogDumpGtid.new server_id ⦃ g =>
      GtidDump.of g = ⟨0, server_id.val, [], 0, []⟩ ⦄ := by
  unfold packets.ComBinlogDumpGtid.new
  step*
  simp_all [GtidDump.of]

/-- `server_id`: the field. -/
theorem packets.ComBinlogDumpGtid.impl.server_id_eq (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.impl.server_id self = ok self.server_id.1 := by
  rfl

/-- `flags`: the field. -/
theorem packets.ComBinlogDumpGtid.impl.flags_eq (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.impl.flags self = ok self.flags.1 := by
  rfl

/-- `filename_raw`: the file name's effective bytes (at most the first `u32::MAX`). -/
theorem packets.ComBinlogDumpGtid.filename_raw_spec (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.filename_raw self ⦃ s =>
      s.val = (cowList self.filename.1).take (2 ^ 32 - 1) ⦄ := by
  exact u32bytes_as_bytes_spec _

/-- `filename`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComBinlogDumpGtid.impl.filename_spec (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.impl.filename self ⦃ c =>
      LossyUtf8Valid ((cowList self.filename.1).take (2 ^ 32 - 1)) c ⦄ := by
  exact u32bytes_as_str_spec _

/-- `pos`: the field. -/
theorem packets.ComBinlogDumpGtid.impl.pos_eq (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.impl.pos self = ok self.pos.1 := by
  rfl

/-- `sids`: the SIDs. -/
theorem packets.ComBinlogDumpGtid.sids_spec (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.sids self ⦃ s => s.val = cowList self.sid_block.1 ⦄ := by
  unfold packets.ComBinlogDumpGtid.sids
  exact misc.raw.seq.Seq.Insts.CoreOpsDerefDerefSlice.deref_spec _ _

/-- `with_filename`: sets the file name (`filename.into()`); nothing else changes. -/
@[step]
theorem packets.ComBinlogDumpGtid.with_filename_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComBinlogDumpGtid) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComBinlogDumpGtid.with_filename into self x ⦃ g =>
      GtidDump.of g = { GtidDump.of self with filename := cowList c } ⦄ := by
  unfold packets.ComBinlogDumpGtid.with_filename
  step*
  simp_all [GtidDump.of]

/-- `with_server_id`: sets the server id; nothing else changes. -/
@[step]
theorem packets.ComBinlogDumpGtid.with_server_id_spec (self : packets.ComBinlogDumpGtid) (server_id : U32) :
    packets.ComBinlogDumpGtid.with_server_id self server_id ⦃ g =>
      GtidDump.of g = { GtidDump.of self with serverId := server_id.val } ⦄ := by
  unfold packets.ComBinlogDumpGtid.with_server_id
  obtain ⟨hd, fl, ⟨sv, ps⟩, fn, ps2, sb⟩ := self
  simp [GtidDump.of]

/-- `with_flags(flags)`: sets the flags, with `BINLOG_THROUGH_GTID` set exactly when there are
    SIDs; nothing else changes. -/
@[step]
theorem packets.ComBinlogDumpGtid.with_flags_spec (self : packets.ComBinlogDumpGtid)
    (flags : packets.BinlogDumpFlags) :
    packets.ComBinlogDumpGtid.with_flags self flags ⦃ g =>
      GtidDump.of g = { GtidDump.of self with
        flags := if cowList self.sid_block.1 = [] then andNot 16 flags.val BINLOG_THROUGH_GTID
                 else flags.val ||| BINLOG_THROUGH_GTID } ⦄ := by
  unfold packets.ComBinlogDumpGtid.with_flags
  obtain ⟨hd, ⟨fv, pf⟩, sv, fn, pv, sb⟩ := self
  step*
  · simp_all [GtidDump.of, through_gtid_val]
  · simp_all [GtidDump.of, through_gtid_val]

/-- `with_pos`: sets the position; nothing else changes. -/
@[step]
theorem packets.ComBinlogDumpGtid.with_pos_spec (self : packets.ComBinlogDumpGtid) (pos : U64) :
    packets.ComBinlogDumpGtid.with_pos self pos ⦃ g =>
      GtidDump.of g = { GtidDump.of self with pos := pos.val } ⦄ := by
  unfold packets.ComBinlogDumpGtid.with_pos
  obtain ⟨hd, fl, sv, fn, ⟨pv, pp⟩, sb⟩ := self
  simp [GtidDump.of]

/-- `with_sid(sid)`: appends the SID and sets `BINLOG_THROUGH_GTID`; nothing else changes.
    (Preconditions: room for one more SID, and tags that fit in a `usize`, as every real
    string does: a borrowed block is cloned first.) -/
theorem packets.ComBinlogDumpGtid.with_sid_spec (self : packets.ComBinlogDumpGtid) (sid : packets.Sid)
    (h : (cowList self.sid_block.1).length < Usize.max)
    (htags : ∀ s ∈ (GtidDump.of self).sids, ∀ t, s.tag = some t → t.length ≤ Usize.max) :
    packets.ComBinlogDumpGtid.with_sid self sid ⦃ g =>
      GtidDump.of g = { GtidDump.of self with
        flags := (GtidDump.of self).flags ||| BINLOG_THROUGH_GTID,
        sids := (GtidDump.of self).sids ++ [SidV.of sid] } ⦄ := by
  unfold packets.ComBinlogDumpGtid.with_sid misc.raw.seq.Seq.push
  obtain ⟨hd, ⟨fv, pf⟩, sv, fn, pv, ⟨c, pd⟩⟩ := self
  simp only [GtidDump.of, List.mem_map] at htags h
  step with flags_insert_spec as ⟨f1, hf1⟩
  cases c with
  | Borrowed sl =>
    have hcl : ∀ x ∈ sl.val, packets.Sid.Insts.CoreCloneClone.clone x = ok x := by
      intro x hx
      apply sid_clone_eq
      intro t ht
      exact htags (SidV.of x) ⟨x, by simpa [cowList] using hx, rfl⟩ (strCowBytes t) (by simp [SidV.of, ht])
    step with alloc.slice.Slice.to_vec_spec packets.Sid.Insts.CoreCloneClone sl hcl as ⟨v, hv⟩
    have hvl : v.val = sl.val := by rw [hv]; rfl
    step with alloc.vec.Vec.push_spec v sid (by simp [cowList] at h; rw [hvl]; exact h) as ⟨v1, hv1⟩
    apply spec_bind_ok
    apply (WP.spec_ok _).mpr
    simp_all [GtidDump.of, through_gtid_val, cowList]
  | Owned v =>
    step with alloc.vec.Vec.push_spec v sid (by simp [cowList] at h; exact h) as ⟨v1, hv1⟩
    apply spec_bind_ok
    apply (WP.spec_ok _).mpr
    simp_all [GtidDump.of, through_gtid_val, cowList]

/-- `with_sids(sids)`: replaces the SIDs (`sids.into()`), with `BINLOG_THROUGH_GTID` set exactly
    when there are SIDs; nothing else changes. -/
@[step]
theorem packets.ComBinlogDumpGtid.with_sids_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice packets.Sid) (alloc.vec.Vec packets.Sid)))
    (self : packets.ComBinlogDumpGtid) (x : T)
    (c : alloc.borrow.Cow (Slice packets.Sid) (alloc.vec.Vec packets.Sid)) (h : into.into x = ok c) :
    packets.ComBinlogDumpGtid.with_sids into self x ⦃ g =>
      GtidDump.of g = { GtidDump.of self with
        flags := if cowList c = [] then andNot 16 (GtidDump.of self).flags BINLOG_THROUGH_GTID
                 else (GtidDump.of self).flags ||| BINLOG_THROUGH_GTID,
        sids := (cowList c).map SidV.of } ⦄ := by
  unfold packets.ComBinlogDumpGtid.with_sids
  rw [misc.raw.seq.Seq.new_eq _ _ _ _ c h]
  apply spec_bind_ok
  obtain ⟨hd, ⟨fv, pf⟩, sv, fn, pv, sb⟩ := self
  apply WP.spec_bind (seq_is_empty_spec _ ((c, ()) : misc.raw.seq.Seq packets.Sid misc.raw.int.LeU64))
  intro b hb
  split
  · step*
    simp_all [GtidDump.of, through_gtid_val]
  · step*
    simp_all [GtidDump.of, through_gtid_val]

/-- `MySerialize for ComBinlogDumpGtid`: appends `gtidDumpEnc`: the file name with a 4-byte
    length, the position, `data_size` and the SID block (tagged format iff some SID has a tag;
    `data_size` and the block are sent even without `BINLOG_THROUGH_GTID`). Precondition: the
    SID block is shorter than `2^32` bytes; otherwise **crate behaviour**: `data_size` is
    computed with saturating (and truncating `as u32`) arithmetic and no longer matches the
    block. -/
theorem packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComBinlogDumpGtid) (buf : alloc.vec.Vec U8)
    (hblk : (sidBlock (GtidDump.of self).sids).length < 2 ^ 32)
    (h : buf.length + (gtidDumpEnc (GtidDump.of self)).length ≤ Usize.max) :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ gtidDumpEnc (GtidDump.of self) ⦄ := by
  unfold packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMySerialize.serialize
  set ss := (cowList self.sid_block.1).map SidV.of with hss
  set t := gtidTagged ss with ht
  have hblk' : (sidBlock ss).length = 8 + (ss.flatMap (encOf t)).length := by
    simp only [sidBlock, ← ht, List.length_append, nSidsHeader, encOf]
    cases t <;> simp [PBUtil.length_leBytes]
  have hnl : ss.length ≤ (ss.flatMap (encOf t)).length := length_le_flatMap_pos _ (encOf_pos t) ss
  simp only [GtidDump.of, ← hss] at hblk h
  simp only [gtidDumpEnc, List.length_cons, List.length_append, PBUtil.length_leBytes, List.length_take,
    alloc.vec.Vec.length] at h
  have hfn : min (cowList self.filename.1).length (2 ^ 32 - 1) ≤ (cowList self.filename.1).length := by omega
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨b1, h1⟩
  step with const_flags_ser as ⟨b2, h2⟩
  · simp only [alloc.vec.Vec.length, h1, List.length_append]; simp; omega
  step with rawint_u32_serialize as ⟨b3, h3⟩
  · simp only [alloc.vec.Vec.length, h2, h1, List.length_append]; simp [PBUtil.length_leBytes]; omega
  step with u32bytes_ser as ⟨b4, h4⟩
  · simp only [alloc.vec.Vec.length, h3, h2, h1, List.length_append]; simp [PBUtil.length_leBytes]; omega
  step with rawint_u64_ser as ⟨b5, h5⟩
  · simp only [alloc.vec.Vec.length, h4, h3, h2, h1, List.length_append]; simp [PBUtil.length_leBytes]; omega
  step with misc.raw.seq.Seq.Insts.CoreOpsDerefDerefSlice.deref_spec as ⟨sl, hsl⟩
  step with any_sid_tagged_spec sl sl.val.length 0#usize (by simp) as ⟨tg, htg⟩
  have htg' : tg = t := by
    rw [htg, ht, hsl, hss]; simp [gtidTagged, SidV.of, List.any_map, Function.comp_def]
  subst htg'
  have hssl : (sl.val.drop (0#usize).val).map SidV.of = ss := by simp [hsl, hss]
  step with sid_block_len_from_spec sl t sl.val.length 0#usize 8#u32 (by simp)
    (by rw [hssl, show (8#u32).val = 8 from rfl]; omega) as ⟨bl, hbl⟩
  simp only [hsl] at hbl
  step with IntAndMisc.put_u32_le_spec as ⟨b6, h6⟩
  · simp only [alloc.vec.Vec.length, h5, h4, h3, h2, h1, List.length_append]; simp [PBUtil.length_leBytes]; omega
  step with seq_len_spec as ⟨nl, hnl'⟩
  step as ⟨n64, hn64⟩
  have hn64v : n64.val = ss.length := by rw [hn64]; simp [hnl', hss]
  step with n_sids_header_spec t n64 (by rw [hn64v]; omega) as ⟨hdr, hhdr⟩
  step with IntAndMisc.put_u64_le_spec as ⟨b7, h7⟩
  · simp only [alloc.vec.Vec.length, h6, h5, h4, h3, h2, h1, List.length_append]; simp [PBUtil.length_leBytes]; omega
  apply WP.spec_mono (serialize_sids_from_spec sl t sl.val.length 0#usize b7 (by simp)
    (by rw [hssl]; simp only [alloc.vec.Vec.length, h7, h6, h5, h4, h3, h2, h1, List.length_append,
        PBUtil.length_leBytes, List.length_cons, List.length_nil, List.length_take]; omega))
  intro b hb
  simp only [hsl] at hb
  rw [hb, h7, h6, h5, h4, h3, h2, h1, hhdr, hbl]
  have hsb : sidBlock ss = nSidsHeader t ss.length ++ ss.flatMap (encOf t) := by
    simp only [sidBlock, ← ht, encOf]
  simp only [gtidDumpEnc, GtidDump.of, ← hss, hsb, hn64v, List.length_append]
  have hhl : (nSidsHeader t ss.length).length = 8 := by
    cases t <;> simp [nSidsHeader, PBUtil.length_leBytes]
  have h30 : (30#u8 : U8) = byte 30 := rfl
  simp only [hhl, ← ht, List.drop_zero, ← hss, h30, show ((0#usize : Usize).val) = 0 from rfl]
  simp

/-- `MyDeserialize for ComBinlogDumpGtid`: `SIZE` is `None`. -/
theorem packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  simp [packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for ComBinlogDumpGtid`: exactly `gtidDumpRead` whenever that reader returns,
    in both formats. `gtidDumpRead` never gives `unknown` (`Defs.gtidDumpRead_ne_unknown`), so
    with `deserialize_panics` this covers every input.
    **Allocation caveat (GTID).** The SID count comes from the input (up to `2^56`) and is passed
    to `Vec::with_capacity` before any SID is read, which the model treats as free: in real Rust
    a 31-byte packet announcing `2^56` SIDs makes the reader try to allocate `2^56` SIDs and
    abort the process (out of memory, observed), where the model returns an error. The same
    holds for each SID's interval count (`Sid::deserialize_overflow`). -/
theorem packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (h64 : Target64) (buf : io.ParseBuf) (r0 : Option GtidDump) (rest0 : List U8)
    (h : gtidDumpRead buf.val = .done r0 rest0) :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map GtidDump.of = r0 ∧ rest.val = rest0 ⦄ := by
  unfold packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  unfold gtidDumpRead at h
  step with parse_usize_spec as ⟨r, buf1, h1⟩
  split_ifs at h1 with hl
  swap
  · obtain ⟨h1a, h1b⟩ := h1
    have hc : buf.val.length < 7 := by simp only [Slice.length] at hl; omega
    simp only [hc, ↓reduceIte, ReadOut.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [h1b]
    cases r with
    | Ok _ => simp at h1a
    | Err e =>
      rw [branch_err_eq]
      apply spec_bind_ok
      dsimp only
      rw [from_residual_eq]
      apply spec_bind_ok
      exact (WP.spec_ok _).mpr ⟨by simp [okPart], rfl⟩
  obtain ⟨h1a, h1b⟩ := h1
  have hl' : 7 ≤ buf.val.length := hl
  simp only [show ¬ buf.val.length < 7 by omega, ↓reduceIte] at h
  cases r with
  | Err e => simp at h1a
  | Ok pb =>
  simp only [okPart, Option.map_some, Option.some.injEq] at h1a
  rw [show CoreOpsTry.branch (core.result.Result.Ok pb : core.result.Result io.ParseBuf core.io.error.Error) =
    ok (core.ops.control_flow.ControlFlow.Continue pb) from rfl]
  apply spec_bind_ok
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, rest, hbuf⟩ :
      ∃ a0 a1 a2 a3 a4 a5 a6 rest, (↑buf : List U8) = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: rest := by
    match hb : (↑buf : List U8), hl' with
    | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: rest, _ => exact ⟨a0, a1, a2, a3, a4, a5, a6, rest, rfl⟩
  rw [hbuf] at h1a h1b h
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.getD_cons_zero] at h1a h1b h
  step with parse_unchecked_hdr_spec as ⟨r1, sbuf, h2a, h2b⟩
  rw [h1a] at h2a h2b
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, leNat] at h2a h2b
  cases r1 with
  | Err e =>
    have ha : ¬ (a0.val = 30) := by intro hh; simp [okPart, hh] at h2a
    simp only [ha, ne_eq, not_false_eq_true, true_or, ↓reduceIte, ReadOut.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    gtid_err_br
    exact ⟨by simp [okPart], h1b⟩
  | Ok hd =>
  have ha : a0.val = 30 := by simpa [okPart] using h2a
  gtid_ok_br
  step with parse_unchecked_flags_spec as ⟨r2, sbuf2, h3a, h3b⟩
  simp only [h2b, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero] at h3a h3b
  cases r2 with
  | Err e =>
    have hf : leNat [a1, a2] &&& binlogDumpFlagsAll ≠ leNat [a1, a2] := by
      intro hh; simp [hh, okPart] at h3a
    simp only [hf, ne_eq, not_false_eq_true, or_true, ↓reduceIte, ReadOut.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    gtid_err_br
    exact ⟨by simp [okPart], h1b⟩
  | Ok flv =>
  have hf : leNat [a1, a2] &&& binlogDumpFlagsAll = leNat [a1, a2] := by
    by_contra hh; simp [hh, okPart] at h3a
  simp only [hf, ↓reduceIte, okPart, Option.map_some, Option.some.injEq] at h3a
  simp only [ha, hf, ne_eq, not_true_eq_false, or_self, ↓reduceIte] at h
  gtid_ok_br
  step with parse_unchecked_leu32_spec as ⟨r3, sbuf3, h4a, h4b⟩
  · simp [Slice.length, h3b]
  cases r3 with
  | Err e => simp [okPart] at h4a
  | Ok sidv =>
  simp only [h3b, List.take_succ_cons, List.take_zero, okPart, Option.map_some, Option.some.injEq] at h4a
  gtid_ok_br
  step with parse_u32bytes_spec as ⟨r4, buf2, h5⟩
  rw [h1b] at h5
  rcases hc : checkedLenPrefixed 4 rest with ⟨_ | fname, r⟩
  · rw [hc] at h5 h
    simp only [ReadOut.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Prod.mk.injEq] at h5
    cases r4 with
    | Ok _ => simp [okPart] at h5
    | Err e =>
      gtid_err_br
      exact ⟨by simp [okPart], h5.2⟩
  rw [hc] at h5 h
  simp only [Prod.mk.injEq] at h5 h
  cases r4 with
  | Err e => simp [okPart] at h5
  | Ok rb =>
  simp only [okPart, Option.map_some, Option.some.injEq] at h5
  obtain ⟨hrb, hb2⟩ := h5
  gtid_ok_br
  step with misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec as ⟨r5, buf3, h6⟩
  simp only [Slice.length, hb2] at h6
  by_cases h8 : 8 ≤ r.length
  swap
  · simp only [readLE, h8, ↓reduceIte, ReadOut.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [h8, ↓reduceIte] at h6
    cases r5 with
    | Ok _ => simp [okPart] at h6
    | Err e =>
      gtid_err_br
      exact ⟨by simp [okPart], by rw [h6.2, hb2]⟩
  simp only [readLE, h8, ↓reduceIte] at h
  simp only [h8, ↓reduceIte] at h6
  cases r5 with
  | Err e => simp [okPart] at h6
  | Ok posv =>
  simp only [okPart, Option.map_some, Option.some.injEq] at h6
  obtain ⟨hpos, hb3⟩ := h6
  gtid_ok_br
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec as ⟨r6, buf4, h7⟩
  simp only [Slice.length, hb3] at h7
  by_cases h4 : 4 ≤ (r.drop 8).length
  swap
  · simp only [h4, ↓reduceIte, ReadOut.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [h4, ↓reduceIte] at h7
    cases r6 with
    | Ok _ => simp [okPart] at h7
    | Err e =>
      gtid_err_br
      exact ⟨by simp [okPart], by rw [h7.2, hb3]⟩
  simp only [h4, ↓reduceIte] at h
  simp only [h4, ↓reduceIte] at h7
  cases r6 with
  | Err e => simp [okPart] at h7
  | Ok lenv =>
  simp only [okPart, Option.map_some, Option.some.injEq] at h7
  obtain ⟨hlen, hb4⟩ := h7
  gtid_ok_br
  obtain ⟨i, pd⟩ := lenv
  simp only at hlen
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = leNat (List.take 4 (List.drop 8 r)) := by rw [hi1, ← hlen]; simp
  step with parse_usize_spec as ⟨r7, buf5, h9⟩
  simp only [Slice.length, hb4, hi1v] at h9
  generalize hL : leNat (List.take 4 (List.drop 8 r)) = L at h h9 hi1v
  generalize hR : List.drop 4 (List.drop 8 r) = R at h h9 hb4
  by_cases hLR : R.length < L
  · simp only [hLR, ↓reduceIte, ReadOut.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [show ¬ L ≤ R.length by omega, ↓reduceIte] at h9
    cases r7 with
    | Ok _ => simp [okPart] at h9
    | Err e =>
      gtid_err_br
      exact ⟨by simp [okPart], by rw [h9.2, hb4]⟩
  simp only [hLR, ↓reduceIte] at h
  simp only [show L ≤ R.length by omega, ↓reduceIte] at h9
  cases r7 with
  | Err e => simp [okPart] at h9
  | Ok pb1 =>
  simp only [okPart, Option.map_some, Option.some.injEq] at h9
  obtain ⟨hpb1, hb5⟩ := h9
  gtid_ok_br
  step with misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec as ⟨r8, sid_buf, h10⟩
  simp only [Slice.length, hpb1] at h10
  by_cases hb8 : 8 ≤ (R.take L).length
  swap
  · simp only [hb8, ↓reduceIte, ReadOut.done.injEq] at h h10
    obtain ⟨rfl, rfl⟩ := h
    cases r8 with
    | Ok _ => simp [okPart] at h10
    | Err e =>
      gtid_err_br
      exact ⟨by simp [okPart], hb5⟩
  simp only [hb8, ↓reduceIte] at h h10
  cases r8 with
  | Err e => simp [okPart] at h10
  | Ok rawv =>
  simp only [okPart, Option.map_some, Option.some.injEq] at h10
  obtain ⟨hraw, hsb⟩ := h10
  gtid_ok_br
  obtain ⟨raw, pd2⟩ := rawv
  simp only at hraw
  step as ⟨i3, hi3⟩
  step as ⟨fb, hfb⟩
  have hs : U64.size = 2 ^ 64 := by simp [U64.size_def, U64.numBits_def]
  have hfbv : fb.val = raw.val / 2 ^ 56 := by
    rw [hfb]; simp only [UScalar.cast_val_eq]
    rw [hi3, Nat.shiftRight_eq_div_pow]
    have : raw.val < 2 ^ 64 := by scalar_tac
    apply Nat.mod_eq_of_lt
    show raw.val / 2 ^ 56 < 2 ^ 8
    omega
  rw [← hraw, ← hsb] at h
  have hraw64 : raw.val < 2 ^ 64 := by scalar_tac
  by_cases htg : raw.val / 2 ^ 56 = 1
  · have hfb1 : fb = 1#u8 := UScalar.eq_of_val_eq (by rw [hfbv, htg]; rfl)
    simp only [htg, decide_true, ↓reduceIte] at h
    split
    swap
    · rename_i hne; exact absurd hfb1 hne
    step as ⟨i4, hi4⟩
    step as ⟨ns, hns⟩
    have hnsv : ns.val = raw.val / 2 ^ 8 % 2 ^ 48 := by
      rw [hns, hi4, UScalar.val_and]; exact mask_shift _
    step as ⟨i5, hi5⟩
    subst hfb1
    split
    · obtain ⟨hd9, -⟩ := tagged_loop h64 (raw.val / 2 ^ 8 % 2 ^ 48) sid_buf ns
        (alloc.vec.Vec.with_capacity packets.Sid i5) hnsv (by simp [alloc.vec.Vec.with_capacity])
      cases hsr : sidsRead true (raw.val / 2 ^ 8 % 2 ^ 48) sid_buf.val with
      | done o rr =>
        rw [hsr] at h
        step with hd9 o rr hsr as ⟨r9, b9, h9⟩
        cases o with
        | some ss =>
          simp only [ReadOut.done.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases r9 with
          | Err _ => simp [okPart] at h9
          | Ok v =>
          gtid_ok_br
          rw [seq_sid_new_vec]
          apply spec_bind_ok
          apply (WP.spec_ok _).mpr
          simp only [okPart, Option.map_some, Option.some.injEq] at h9
          refine ⟨?_, hb5⟩
          simp only [okPart, Option.map_some, GtidDump.of, h3a, h4a, hrb, hpos]
          simp [cowList, h9, alloc.vec.Vec.with_capacity]
        | none =>
          simp only [ReadOut.done.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases r9 with
          | Ok _ => simp [okPart] at h9
          | Err e =>
            gtid_err_br
            exact ⟨by simp [okPart], hb5⟩
      | panic e => rw [hsr] at h; simp at h
      | unknown => rw [hsr] at h; simp at h
    · rename_i hne; exact absurd rfl hne
  · have hfb1 : fb ≠ 1#u8 := fun hh => htg (by rw [← hfbv, hh]; rfl)
    simp only [htg, decide_false, ↓reduceIte] at h
    split
    · rename_i hh; exact absurd hh hfb1
    have hnsv : (raw &&& 72057594037927935#u64).val = raw.val % 2 ^ 56 := by
      rw [UScalar.val_and]; exact mask_low _
    step as ⟨i5, hi5⟩
    split
    · rename_i hh; exact absurd rfl hfb1
    obtain ⟨hd9, -⟩ := untagged_loop h64 (raw.val % 2 ^ 56) sid_buf (raw &&& 72057594037927935#u64)
      (alloc.vec.Vec.with_capacity packets.Sid i5) hnsv (by simp [alloc.vec.Vec.with_capacity])
    cases hsr : sidsRead false (raw.val % 2 ^ 56) sid_buf.val with
    | done o rr =>
      rw [hsr] at h
      step with hd9 o rr hsr as ⟨r9, b9, h9⟩
      cases o with
      | some ss =>
        simp only [ReadOut.done.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases r9 with
        | Err _ => simp [okPart] at h9
        | Ok v =>
        gtid_ok_br
        rw [seq_sid_new_vec]
        apply spec_bind_ok
        apply (WP.spec_ok _).mpr
        simp only [okPart, Option.map_some, Option.some.injEq] at h9
        refine ⟨?_, hb5⟩
        simp only [okPart, Option.map_some, GtidDump.of, h3a, h4a, hrb, hpos]
        simp [cowList, h9, alloc.vec.Vec.with_capacity]
      | none =>
        simp only [ReadOut.done.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases r9 with
        | Ok _ => simp [okPart] at h9
        | Err e =>
          gtid_err_br
          exact ⟨by simp [okPart], hb5⟩
    | panic e => rw [hsr] at h; simp at h
    | unknown => rw [hsr] at h; simp at h

/-- **Crash path.** `MyDeserialize for ComBinlogDumpGtid` panics where `gtidDumpRead` does: a SID
    whose interval count `n` has `16 * n` above `usize::MAX` (see `Sid::deserialize_overflow`:
    real Rust crashes earlier, in `Vec::with_capacity`). -/
theorem packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics
    (h64 : Target64) (buf : io.ParseBuf) (e : Error) (h : gtidDumpRead buf.val = .panic e) :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf = fail e := by
  unfold gtidDumpRead at h
  by_cases hl : buf.val.length < 7
  · simp [hl] at h
  simp only [hl, ↓reduceIte] at h
  obtain ⟨⟨r1, buf1⟩, he1, h1⟩ := spec_eq_ok (parse_usize_spec buf 7#usize)
  simp only [WP.uncurry'_pair] at h1
  have h7 : ((7#usize : Usize).val) = 7 := rfl
  simp only [h7, Slice.length, show 7 ≤ buf.val.length by omega, ↓reduceIte] at h1
  obtain ⟨h1a, h1b⟩ := h1
  cases r1 with
  | Err _ => simp [okPart] at h1a
  | Ok pb =>
  simp only [okPart, Option.map_some, Option.some.injEq] at h1a
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, rest, hbuf⟩ :
      ∃ a0 a1 a2 a3 a4 a5 a6 rest, (↑buf : List U8) = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: rest := by
    match hb : (↑buf : List U8), (by omega : 7 ≤ buf.val.length) with
    | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: rest, _ => exact ⟨a0, a1, a2, a3, a4, a5, a6, rest, rfl⟩
  rw [hbuf] at h1a h1b h
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.getD_cons_zero] at h1a h1b h
  obtain ⟨⟨r2, sbuf⟩, he2, h2a, h2b⟩ := spec_eq_ok (parse_unchecked_hdr_spec pb (by simp [Slice.length, h1a]))
  rw [h1a] at h2a h2b
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, leNat] at h2a h2b
  cases r2 with
  | Err _ =>
    have ha : ¬ (a0.val = 30) := by intro hh; simp [okPart, hh] at h2a
    simp [ha] at h
  | Ok hd =>
  have ha : a0.val = 30 := by simpa [okPart] using h2a
  obtain ⟨⟨r3, sbuf2⟩, he3, h3a, h3b⟩ := spec_eq_ok (parse_unchecked_flags_spec sbuf (by simp [Slice.length, h2b]))
  simp only [h2b, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero] at h3a h3b
  cases r3 with
  | Err _ =>
    have hf : leNat [a1, a2] &&& binlogDumpFlagsAll ≠ leNat [a1, a2] := by
      intro hh; simp [hh, okPart] at h3a
    simp [hf] at h
  | Ok flv =>
  have hf : leNat [a1, a2] &&& binlogDumpFlagsAll = leNat [a1, a2] := by
    by_contra hh; simp [hh, okPart] at h3a
  simp only [ha, hf, ne_eq, not_true_eq_false, or_self, ↓reduceIte] at h
  obtain ⟨⟨r4, sbuf3⟩, he4, h4a, -⟩ := spec_eq_ok (parse_unchecked_leu32_spec sbuf2 (by simp [Slice.length, h3b]))
  cases r4 with
  | Err _ => simp [okPart] at h4a
  | Ok sidv =>
  obtain ⟨⟨r5, buf2⟩, he5, h5⟩ := spec_eq_ok (parse_u32bytes_spec buf1)
  simp only [WP.uncurry'_pair] at h5
  rw [h1b] at h5
  rcases hc : checkedLenPrefixed 4 rest with ⟨_ | fname, r⟩
  · rw [hc] at h; simp at h
  rw [hc] at h5 h
  simp only [Prod.mk.injEq] at h5
  cases r5 with
  | Err e => simp [okPart] at h5
  | Ok rb =>
  obtain ⟨-, hb2⟩ := h5
  obtain ⟨⟨r6, buf3⟩, he6, h6⟩ := spec_eq_ok
    (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec buf2)
  simp only [WP.uncurry'_pair] at h6
  simp only [Slice.length, hb2] at h6
  by_cases h8 : 8 ≤ r.length
  swap
  · simp [readLE, h8] at h
  simp only [readLE, h8, ↓reduceIte] at h h6
  cases r6 with
  | Err e => simp [okPart] at h6
  | Ok posv =>
  obtain ⟨-, hb3⟩ := h6
  obtain ⟨⟨r7, buf4⟩, he7, h7'⟩ := spec_eq_ok
    (misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf3)
  simp only [WP.uncurry'_pair] at h7'
  simp only [Slice.length, hb3] at h7'
  by_cases h4 : 4 ≤ (r.drop 8).length
  swap
  · simp only [h4, ↓reduceIte] at h; simp at h
  simp only [h4, ↓reduceIte] at h h7'
  cases r7 with
  | Err e => simp [okPart] at h7'
  | Ok lenv =>
  simp only [okPart, Option.map_some, Option.some.injEq] at h7'
  obtain ⟨hlen, hb4⟩ := h7'
  obtain ⟨i, pd⟩ := lenv
  simp only at hlen
  have hi1v : (UScalar.cast .Usize i).val = leNat (List.take 4 (List.drop 8 r)) := by rw [← hlen]; simp
  obtain ⟨⟨r8, buf5⟩, he8, h9⟩ := spec_eq_ok (parse_usize_spec buf4 (UScalar.cast .Usize i))
  simp only [WP.uncurry'_pair] at h9
  simp only [Slice.length, hb4, hi1v] at h9
  generalize hL : leNat (List.take 4 (List.drop 8 r)) = L at h h9
  generalize hR : List.drop 4 (List.drop 8 r) = R at h h9
  by_cases hLR : R.length < L
  · simp [hLR] at h
  simp only [hLR, ↓reduceIte] at h
  simp only [show L ≤ R.length by omega, ↓reduceIte] at h9
  cases r8 with
  | Err e => simp [okPart] at h9
  | Ok pb1 =>
  simp only [okPart, Option.map_some, Option.some.injEq] at h9
  obtain ⟨hpb1, -⟩ := h9
  obtain ⟨⟨r9, sid_buf⟩, he9, h10⟩ := spec_eq_ok
    (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec pb1)
  simp only [WP.uncurry'_pair] at h10
  simp only [Slice.length, hpb1] at h10
  by_cases hb8 : 8 ≤ (R.take L).length
  swap
  · simp only [hb8, ↓reduceIte] at h; simp at h
  simp only [hb8, ↓reduceIte] at h h10
  cases r9 with
  | Err e => simp [okPart] at h10
  | Ok rawv =>
  simp only [okPart, Option.map_some, Option.some.injEq] at h10
  obtain ⟨hraw, hsb⟩ := h10
  obtain ⟨raw, pd2⟩ := rawv
  simp only at hraw
  rw [← hraw, ← hsb] at h
  have hraw64 : raw.val < 2 ^ 64 := by scalar_tac
  obtain ⟨i3, he10, hi3⟩ := spec_eq_ok (show (raw >>> 56#i32) ⦃ z => z.val = raw.val >>> 56 ⦄ by step*)
  have hfbv : (UScalar.cast .U8 i3).val = raw.val / 2 ^ 56 := by
    simp only [UScalar.cast_val_eq]
    rw [hi3, Nat.shiftRight_eq_div_pow]
    apply Nat.mod_eq_of_lt
    show raw.val / 2 ^ 56 < 2 ^ 8
    omega
  unfold packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  delta misc.raw.int.RawInt misc.raw._const.Const misc.raw.seq.Seq misc.raw.bytes.RawBytes misc.raw.int.ConstU8 at *
  by_cases htg : raw.val / 2 ^ 56 = 1
  · have hfb1 : UScalar.cast .U8 i3 = 1#u8 := UScalar.eq_of_val_eq (by rw [hfbv, htg]; rfl)
    simp only [htg, decide_true, ↓reduceIte] at h
    obtain ⟨i4, he11, hi4⟩ := spec_eq_ok
      (show ((raw &&& 72057594037927680#u64) >>> 8#i32) ⦃ z => z.val = (raw &&& 72057594037927680#u64).val >>> 8 ⦄ by
        step*)
    have hnsv : i4.val = raw.val / 2 ^ 8 % 2 ^ 48 := by
      rw [hi4, UScalar.val_and]; exact mask_shift _
    rcases hsr : sidsRead true (raw.val / 2 ^ 8 % 2 ^ 48) sid_buf.val with ⟨o, rr⟩ | e' | _
    · rw [hsr] at h; rcases o with _ | ss <;> simp at h
    · rw [hsr] at h
      simp only [ReadOut.panic.injEq] at h
      subst h
      have hp := (tagged_loop h64 (raw.val / 2 ^ 8 % 2 ^ 48) sid_buf i4
        (alloc.vec.Vec.with_capacity packets.Sid (UScalar.cast .Usize i4)) hnsv
        (by simp [alloc.vec.Vec.with_capacity])).2 e' hsr
      simp [he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, he11, hfb1, hp, CoreOpsTry.branch, lift]
      split
      · rfl
      · rename_i hne; exact absurd rfl hne
    · rw [hsr] at h; simp at h
  · have hfb1 : UScalar.cast .U8 i3 ≠ 1#u8 := fun hh => htg (by rw [← hfbv, hh]; rfl)
    simp only [htg, decide_false, ↓reduceIte] at h
    have hnsv : (raw &&& 72057594037927935#u64).val = raw.val % 2 ^ 56 := by
      rw [UScalar.val_and]; exact mask_low _
    rcases hsr : sidsRead false (raw.val % 2 ^ 56) sid_buf.val with ⟨o, rr⟩ | e' | _
    · rw [hsr] at h; rcases o with _ | ss <;> simp at h
    · rw [hsr] at h
      simp only [ReadOut.panic.injEq] at h
      subst h
      have hp := (untagged_loop h64 (raw.val % 2 ^ 56) sid_buf (raw &&& 72057594037927935#u64)
        (alloc.vec.Vec.with_capacity packets.Sid (UScalar.cast .Usize (raw &&& 72057594037927935#u64))) hnsv
        (by simp [alloc.vec.Vec.with_capacity])).2 e' hsr
      simp [he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, hfb1, hp, CoreOpsTry.branch, lift]
      split
      · rename_i hh; exact absurd hh hfb1
      · rfl
    · rw [hsr] at h; simp at h

/-- Round trip (untagged format): a request without tags, with known flags, a file name shorter
    than `2^32` bytes and a SID block shorter than `2^32` bytes, is read back from
    `gtidDumpEnc`. (With tags, see `roundtrip_tagged`.) -/
theorem packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (h64 : Target64) (g : packets.ComBinlogDumpGtid)
    (hnotag : gtidTagged (GtidDump.of g).sids = false)
    (hf : (GtidDump.of g).flags &&& binlogDumpFlagsAll = (GtidDump.of g).flags)
    (hfn : (GtidDump.of g).filename.length < 2 ^ 32)
    (hblk : (sidBlock (GtidDump.of g).sids).length < 2 ^ 32)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = gtidDumpEnc (GtidDump.of g) ++ tail) :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map GtidDump.of = some (GtidDump.of g) ∧ rest.val = tail ⦄ := by
  have hd := Replication.gtidDumpRead_gtidDumpEnc (GtidDump.of g) hnotag hf
    (by simp [GtidDump.of]; scalar_tac) hfn (by simp [GtidDump.of]; scalar_tac) hblk (by
      intro s hs
      simp only [GtidDump.of, List.mem_map] at hs
      obtain ⟨x, _, rfl⟩ := hs
      refine ⟨by simp [SidV.of], ?_⟩
      intro i hi
      simp only [SidV.of, List.mem_map] at hi
      obtain ⟨y, _, rfl⟩ := hi
      constructor <;> scalar_tac) tail
  rw [← h] at hd
  exact packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf _ _ hd

/-- Round trip, with or without tags: a request whose tags are all valid (`tagBytesValid`), with
    known flags, a file name shorter than `2^32` bytes and a SID block shorter than `2^32` bytes,
    is read back from `gtidDumpEnc`. -/
theorem packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip_tagged
    (h64 : Target64) (g : packets.ComBinlogDumpGtid)
    (htags : ∀ s ∈ (GtidDump.of g).sids, ∀ t, s.tag = some t → tagBytesValid t = true)
    (hf : (GtidDump.of g).flags &&& binlogDumpFlagsAll = (GtidDump.of g).flags)
    (hfn : (GtidDump.of g).filename.length < 2 ^ 32)
    (hblk : (sidBlock (GtidDump.of g).sids).length < 2 ^ 32)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = gtidDumpEnc (GtidDump.of g) ++ tail) :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map GtidDump.of = some (GtidDump.of g) ∧ rest.val = tail ⦄ := by
  have hd := Replication.gtidDumpRead_gtidDumpEnc_tagged (GtidDump.of g) hf
    (by simp [GtidDump.of]; scalar_tac) hfn (by simp [GtidDump.of]; scalar_tac) hblk (by
      intro s hs
      refine ⟨?_, htags s hs, ?_⟩
      · simp only [GtidDump.of, List.mem_map] at hs
        obtain ⟨x, _, rfl⟩ := hs
        simp [SidV.of]
      · simp only [GtidDump.of, List.mem_map] at hs
        obtain ⟨x, _, rfl⟩ := hs
        intro i hi
        simp only [SidV.of, List.mem_map] at hi
        obtain ⟨y, _, rfl⟩ := hi
        constructor <;> scalar_tac) tail
  rw [← h] at hd
  exact packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf _ _ hd

end mysql_common
