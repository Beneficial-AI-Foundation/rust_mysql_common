import Defs
import Proofs.Packets.GnoInterval
import Proofs.Util.RawBytesSeq
import Proofs.Misc.Raw.Array
import Proofs.Misc.Raw.Seq.Seq
import Proofs.Misc.Raw.Seq.LeU64
import Proofs.Misc.ReadVarlenUint
import Proofs.Util.ConvBytesTime
import Proofs.Packets.Tag
import Proofs.Misc.WriteVarlenUint

/-! Statements for `struct Sid and its impls` (spec file: `Specs/Packets/StmtBinlog.lean`).
Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

namespace SidUtil

/-- The `MyDeserialize` instance of `GnoInterval`. -/
abbrev gnoDe := packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple

/-- The `MyDeserialize` instance of the intervals of a `Sid` (`Seq<GnoInterval, LeU64>`). -/
noncomputable abbrev intervalsDe := misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize
  packets.GnoInterval.Insts.CoreCloneClone gnoDe misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple

/-- An interval as (start, end). -/
def gnoPair (g : packets.GnoInterval) : Nat × Nat := (g.start.1.val, g.«end».1.val)

theorem gnoChunks_take (n : Nat) : ∀ (l : List U8) (m : Nat), 16 * n ≤ m →
    gnoChunks n (l.take m) = gnoChunks n l := by
  induction n with
  | zero => intro l m _; simp [gnoChunks]
  | succ n ih =>
    intro l m hm
    have h8 : min 8 m = 8 := by omega
    have h8' : min 8 (m - 8) = 8 := by omega
    simp [gnoChunks, List.take_take, List.drop_take, h8, h8', ih _ (m - 16) (by omega)]

theorem gno_parse_spec (b : io.ParseBuf) (h : 16 ≤ b.length) :
    io.ParseBuf.parse gnoDe b () ⦃ r rest =>
      (okPart r).map gnoPair = some (leNat (b.val.take 8), leNat ((b.val.drop 8).take 8)) ∧
      rest.val = b.val.drop 16 ⦄ := by
  have := IntAndMisc.parse_fixed gnoDe 16#usize
    (by simp [packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq]) b ()
    (fun o => o.map gnoPair = some (leNat (b.val.take 8), leNat ((b.val.drop 8).take 8))) (by
      intro sub hsub hl
      apply WP.spec_mono (packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec sub
        (by simp [Slice.length, hsub] at hl ⊢; omega))
      rintro ⟨r, rest⟩ ⟨h1, -⟩
      simp only [WP.uncurry']
      rw [hsub] at h1
      have e : gnoPair = (fun g : packets.GnoInterval => (g.start.1.val, g.«end».1.val)) := rfl
      rw [e, h1]
      simp [List.take_take, List.drop_take])
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ h1
  have hb : 16 ≤ (b.val : List U8).length := h
  simpa [hb] using h1

theorem gno_loop (k : Nat) : ∀ (it : core.ops.range.Range Usize) (buf : io.ParseBuf)
    (seq : alloc.vec.Vec packets.GnoInterval),
    it.end.val = it.start.val + k → 16 * k ≤ buf.length → seq.length + k ≤ Usize.max →
    misc.raw.seq.parse_items_loop gnoDe it buf seq ⦃ r _ =>
      (okPart r).map (fun c => (cowList c).map gnoPair) = some (seq.val.map gnoPair ++ gnoChunks k buf.val) ⦄ := by
  induction k with
  | zero =>
    intro it buf seq hlen _ _
    rw [parse_items_loop_unfold]
    unfold misc.raw.seq.parse_items_loop.body
    step as ⟨ p, ho, he ⟩
    obtain ⟨o, it1⟩ := p
    simp only at ho he ⊢
    simp only [show ¬ (it.start.val < it.end.val) by omega, ↓reduceIte] at ho
    obtain ⟨ho1, ho2⟩ := ho
    subst ho1
    simp_all [okPart, cowList, gnoChunks]
  | succ k ih =>
    intro it buf seq hlen hbuf hcap
    rw [parse_items_loop_unfold]
    unfold misc.raw.seq.parse_items_loop.body
    step as ⟨ p, ho, he ⟩
    obtain ⟨o, it1⟩ := p
    simp only at ho he ⊢
    simp only [show it.start.val < it.end.val by omega, ↓reduceIte] at ho
    obtain ⟨ho1, ho2⟩ := ho
    subst ho1
    step with gno_parse_spec buf (by omega) as ⟨ p, hr1, hr2 ⟩
    obtain ⟨r, buf1⟩ := p
    simp only at hr1 hr2 ⊢
    cases r with
    | Err e => simp [okPart] at hr1
    | Ok v =>
      simp only [okPart, Option.map_some, Option.some.injEq] at hr1
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      step with alloc.vec.Vec.push_spec seq v (by scalar_tac) as ⟨ seq1, hseq1 ⟩
      have := ih it1 buf1 seq1 (by rw [he, ho2]; omega)
        (by simp [Slice.length, hr2] at hbuf ⊢; omega) (by simp [hseq1] at *; scalar_tac)
      apply WP.spec_mono this
      rintro ⟨r, rest⟩ hp
      simp only [WP.uncurry'] at hp ⊢
      rw [hp, hseq1, hr2]
      simp [gnoChunks, hr1]

theorem usize_max_64 (h64 : Target64) : Usize.max = 2 ^ 64 - 1 := by
  have h1 := Usize.max_def
  rw [Usize.numBits_def, UScalarTy.Usize_numBits_eq] at h1
  simp only [Target64] at h64
  rw [h1, h64]

theorem gno_items (n : Usize) (pb : io.ParseBuf) (hpb : 16 * n.val ≤ pb.length) :
    misc.raw.seq.parse_items packets.GnoInterval.Insts.CoreCloneClone gnoDe n pb
      (alloc.vec.Vec.with_capacity packets.GnoInterval n) ⦃ r _ =>
      (okPart r).map (fun c => (cowList c).map gnoPair) = some (gnoChunks n.val pb.val) ⦄ := by
  unfold misc.raw.seq.parse_items
  have := gno_loop n.val { start := 0#usize, «end» := n } pb (alloc.vec.Vec.with_capacity packets.GnoInterval n)
    (by simp) hpb (by simp [alloc.vec.Vec.with_capacity]; scalar_tac)
  step with this as ⟨ r, rest, h1 ⟩
  simpa [alloc.vec.Vec.with_capacity] using h1

/-- The interval reader (`Seq<GnoInterval, LeU64>`) against `intervalsRead`, when it returns. -/
theorem intervals_deser_done (h64 : Target64) (buf : io.ParseBuf) (o : Option (List (Nat × Nat)))
    (rest0 : List U8) (h : intervalsRead buf.val = .done o rest0) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize
      packets.GnoInterval.Insts.CoreCloneClone gnoDe () buf ⦃ r rest =>
      (okPart r).map (fun c => (cowList c).map gnoPair) = o ∧ rest.val = rest0 ⦄ := by
  unfold misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize
  unfold intervalsRead at h
  step with misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec buf as ⟨ r, buf1, hr ⟩
  by_cases h8 : buf.val.length < 8
  · simp only [h8, ↓reduceIte, ReadOut.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have h8' : ¬ 8 ≤ buf.length := by simp [Slice.length]; omega
    simp only [h8', ↓reduceIte] at hr
    obtain ⟨hr1, rfl⟩ := hr
    cases r with
    | Ok _ => simp [okPart] at hr1
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart]
  · simp only [h8, ↓reduceIte] at h
    have h8' : 8 ≤ buf.length := by simp [Slice.length]; omega
    simp only [h8', ↓reduceIte] at hr
    obtain ⟨hr1, hr2⟩ := hr
    cases r with
    | Err e => simp [okPart] at hr1
    | Ok val =>
      simp only [okPart, Option.map_some, Option.some.injEq] at hr1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref]
      obtain ⟨v, u⟩ := val
      simp only at hr1
      simp only [bind_ok, lift, packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq]
      have hlen : (UScalar.cast UScalarTy.Usize v).val = leNat (List.take 8 buf.val) := by
        rw [PBUtil.cast_usize_64 h64, hr1]
      have hmax := usize_max_64 h64
      by_cases hov : Usize.max < 16 * leNat (List.take 8 buf.val)
      · simp [hov] at h
      · simp only [hov, ↓reduceIte] at h
        step as ⟨ i1, hi1 ⟩
        step with parse_parsebuf_spec buf1 i1 as ⟨ r1, buf2, hp ⟩
        have hd : (List.drop 8 buf.val).length = buf.val.length - 8 := List.length_drop ..
        by_cases hsh : (List.drop 8 buf.val).length < 16 * leNat (List.take 8 buf.val)
        · simp only [hsh, ↓reduceIte, ReadOut.done.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have : ¬ i1.val ≤ buf1.length := by simp [Slice.length, hr2, hi1, hlen] at hsh ⊢; omega
          simp only [this, ↓reduceIte] at hp
          obtain ⟨hp1, rfl⟩ := hp
          cases r1 with
          | Ok _ => simp [okPart] at hp1
          | Err e => simp [okPart, hr2, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · simp only [hsh, ↓reduceIte, ReadOut.done.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hle : i1.val ≤ buf1.length := by simp [Slice.length, hr2, hi1, hlen] at hsh ⊢; omega
          simp only [hle, ↓reduceIte] at hp
          obtain ⟨hp1, hp2⟩ := hp
          cases r1 with
          | Err e => simp [okPart] at hp1
          | Ok pb =>
            simp only [okPart, Option.map_some, Option.some.injEq] at hp1
            simp only [bind_ok]
            step with gno_items (UScalar.cast UScalarTy.Usize v) pb (by simp [Slice.length, hp1, hr2, hi1, hlen] at hsh ⊢; omega) as ⟨ r2, rest2, h2 ⟩
            refine ⟨?_, by rw [hp2, hr2, hi1, hlen]⟩
            rw [h2, hp1, hr2, hi1, hlen, gnoChunks_take _ _ _ (le_refl _)]

/-- The interval reader panics where `intervalsRead` does. -/
theorem intervals_deser_panic (h64 : Target64) (buf : io.ParseBuf) (e : Error)
    (h : intervalsRead buf.val = .panic e) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize
      packets.GnoInterval.Insts.CoreCloneClone gnoDe () buf = fail e := by
  unfold misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize
  unfold intervalsRead at h
  obtain ⟨⟨r, buf1⟩, he, hr⟩ := PBUtil.spec_eq_ok
    (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec buf)
  rw [he]
  by_cases h8 : buf.val.length < 8
  · simp [h8] at h
  · simp only [h8, ↓reduceIte] at h
    have h8' : 8 ≤ buf.length := by simp [Slice.length]; omega
    simp only [h8', ↓reduceIte] at hr
    obtain ⟨hr1, -⟩ := hr
    have hmax := usize_max_64 h64
    by_cases hov : Usize.max < 16 * leNat (List.take 8 buf.val)
    · simp only [hov, ↓reduceIte, ReadOut.panic.injEq] at h
      subst h
      cases r with
      | Err e => simp [okPart] at hr1
      | Ok val =>
        simp only [okPart, Option.map_some, Option.some.injEq] at hr1
        obtain ⟨v, u⟩ := val
        simp only at hr1
        have hlen : (UScalar.cast UScalarTy.Usize v).val = leNat (List.take 8 buf.val) := by
          rw [PBUtil.cast_usize_64 h64, hr1]
        have hm : 16#usize * UScalar.cast UScalarTy.Usize v = fail .integerOverflow :=
          CBTUtil.umul_overflow _ _ (by
            have h1 := Usize.max_def
            rw [Usize.numBits_def] at h1
            simp only [hlen]; scalar_tac)
        simp [core.result.Result.Insts.CoreOpsTry.branch, misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref,
          lift, packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq, hm]
    · simp only [hov, ↓reduceIte] at h
      split_ifs at h

/-- `parse::<Seq<GnoInterval, LeU64>>` against `intervalsRead`, when it returns. -/
theorem intervals_parse_done (h64 : Target64) (buf : io.ParseBuf) (o : Option (List (Nat × Nat)))
    (rest0 : List U8) (h : intervalsRead buf.val = .done o rest0) :
    io.ParseBuf.parse intervalsDe buf () ⦃ r rest =>
      (okPart r).map (fun s => (cowList s.1).map gnoPair) = o ∧ rest.val = rest0 ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq])]
  have := misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec
    packets.GnoInterval.Insts.CoreCloneClone gnoDe misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple () buf
    (fun o' rest => o'.map (List.map gnoPair) = o ∧ rest.val = rest0) (by
      apply WP.spec_mono (intervals_deser_done h64 buf o rest0 h)
      rintro ⟨r, rest⟩ hr
      simp only [WP.uncurry', Option.map_map] at hr ⊢
      exact hr)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ hr
  simp only [WP.uncurry', Option.map_map] at hr ⊢
  exact hr

/-- `parse::<Seq<GnoInterval, LeU64>>` panics where `intervalsRead` does. -/
theorem intervals_parse_panic (h64 : Target64) (buf : io.ParseBuf) (e : Error)
    (h : intervalsRead buf.val = .panic e) :
    io.ParseBuf.parse intervalsDe buf () = fail e := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq])]
  show misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.deserialize _ _ _ () buf = _
  unfold misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.deserialize
  exact PBUtil.bind_fail_left (intervals_deser_panic h64 buf e h)

/-- `parse::<[u8; 16]>`. -/
theorem uuid_parse_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple 16#usize) buf () ⦃ r rest =>
      if 16 ≤ buf.val.length then (okPart r).map (·.val) = some (buf.val.take 16) ∧ rest.val = buf.val.drop 16
      else okPart r = none ∧ rest = buf ⦄ := by
  have := IntAndMisc.parse_fixed (ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple 16#usize) 16#usize
    (by simp [ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq]) buf ()
    (fun o => o.map (·.val) = some (buf.val.take 16)) (by
      intro sub hsub hl
      apply WP.spec_mono (ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec 16#usize sub
        (by simp [Slice.length, hsub] at hl ⊢; omega))
      rintro ⟨r, rest⟩ ⟨h1, -⟩
      simp only [WP.uncurry']
      rw [h1, hsub]
      simp)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa [Slice.length] using h1

theorem gnoChunks_enc (is : List (Nat × Nat)) (h : ∀ i ∈ is, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64)
    (tail : List U8) : gnoChunks is.length (is.flatMap gnoEnc ++ tail) = is := by
  induction is with
  | nil => simp [gnoChunks]
  | cons i is ih =>
    obtain ⟨h1, h2⟩ := h i (by simp)
    have hl : (gnoEnc i).length = 16 := by simp [gnoEnc, PBUtil.length_leBytes]
    simp only [List.length_cons, gnoChunks, List.flatMap_cons, List.append_assoc]
    rw [List.drop_left' hl, ih (fun j hj => h j (by simp [hj]))]
    simp only [gnoEnc, List.append_assoc]
    rw [PKUtil.leNat_take_leBytes 8 _ _ (by simpa using h1),
      List.drop_left' (PBUtil.length_leBytes 8 _), PKUtil.leNat_take_leBytes 8 _ _ (by simpa using h2)]

/-- `intervalsRead` reads back `intervalsEnc` (bounds in range, and the count small enough for
    `16 * count` not to overflow). -/
theorem intervalsRead_enc (is : List (Nat × Nat)) (h : ∀ i ∈ is, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64)
    (hn : 16 * is.length ≤ Usize.max) (tail : List U8) :
    intervalsRead (intervalsEnc is ++ tail) = .done (some is) tail := by
  have hl64 : is.length < 2 ^ 64 := by
    have := lt_two_pow_64_of_le_max hn; omega
  have hfl : (is.flatMap gnoEnc).length = 16 * is.length := by
    rw [length_flatMap_const _ _ 16 (fun x _ => by simp [gnoEnc, PBUtil.length_leBytes])]
  unfold intervalsRead intervalsEnc
  simp only [List.append_assoc]
  rw [PKUtil.leNat_take_leBytes 8 _ _ (by simpa using hl64), List.drop_left' (PBUtil.length_leBytes 8 _)]
  simp only [show ¬ Usize.max < 16 * is.length by omega, List.length_append, hfl,
    show ¬ 16 * is.length + tail.length < 16 * is.length by omega]
  rw [gnoChunks_enc is h tail, ← hfl, List.drop_left]
  simp [PBUtil.length_leBytes]

/-- `sidRead` reads back `sidEnc` (16-byte UUID, bounds in range, `16 * count` not overflowing). -/
theorem sidRead_enc (sv : SidV) (hu : sv.uuid.length = 16)
    (h : ∀ i ∈ sv.intervals, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64)
    (hn : 16 * sv.intervals.length ≤ Usize.max) (tail : List U8) :
    sidRead (sidEnc sv ++ tail) = .done (some { sv with tag := none }) tail := by
  unfold sidRead sidEnc
  simp only [List.append_assoc]
  rw [List.drop_left' hu, intervalsRead_enc _ h hn, List.take_left' hu]
  simp [hu]

theorem tag_zero (tl : Usize) (buf : io.ParseBuf) (h0 : tl.val = 0) :
    packets.Sid.deserialize_tag tl buf ⦃ r rest => r = .Ok none ∧ rest = buf ⦄ := by
  unfold packets.Sid.deserialize_tag
  have : ¬ tl > 0#usize := by scalar_tac
  simp [this]

theorem tag_short (tl : Usize) (buf : io.ParseBuf) (h0 : 0 < tl.val) (hlt : buf.length < tl.val) :
    packets.Sid.deserialize_tag tl buf ⦃ r rest => okPart r = none ∧ rest = buf ⦄ := by
  unfold packets.Sid.deserialize_tag
  have : tl > 0#usize := by scalar_tac
  simp only [this, ↓reduceIte]
  step with io.ParseBuf.len_spec as ⟨ i, hi ⟩
  have : i < tl := by scalar_tac
  simp only [this, ↓reduceIte]
  step*
  simp [okPart]

theorem tag_invalid (tl : Usize) (buf : io.ParseBuf) (h0 : 0 < tl.val) (hle : tl.val ≤ buf.length)
    (hnv : ¬ (Trusted.bytesOf (buf.val.take tl.val)).IsValidUTF8) :
    packets.Sid.deserialize_tag tl buf ⦃ r rest => okPart r = none ∧ rest = buf ⦄ := by
  unfold packets.Sid.deserialize_tag
  have : tl > 0#usize := by scalar_tac
  simp only [this, ↓reduceIte]
  step with io.ParseBuf.len_spec as ⟨ i, hi ⟩
  have : ¬ i < tl := by scalar_tac
  simp only [this, ↓reduceIte]
  step as ⟨ tb, htb, htbl ⟩
  have htb' : tb.val = buf.val.take tl.val := by rw [htb]; simp [List.slice]
  simp [misc.trusted.sid_tag_from_utf8, htb', hnv, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart]

theorem tagRestByte_iff (c : U8) :
    tagRestByte c = true ↔ (97 ≤ c.val ∧ c.val ≤ 122) ∨ c.val = 95 ∨ (48 ≤ c.val ∧ c.val ≤ 57) := by
  simp [tagRestByte, tagFirstByte, or_assoc]

theorem tagFirstByte_iff (c : U8) :
    tagFirstByte c = true ↔ (97 ≤ c.val ∧ c.val ≤ 122) ∨ c.val = 95 := by
  simp [tagFirstByte]

/-- `tag_bytes_valid_from b i`: the bytes of `b` from `i` on are all `tagRestByte`. -/
theorem tag_bytes_valid_from_spec (b : Slice U8) (k : Nat) : ∀ (i : Usize), b.length = i.val + k →
    packets.tag_bytes_valid_from b i ⦃ r => r = (b.val.drop i.val).all tagRestByte ⦄ := by
  induction k with
  | zero =>
    intro i h
    rw [packets.tag_bytes_valid_from]
    have : ¬ i < Slice.len b := by scalar_tac
    simp only [this, ↓reduceIte, WP.spec_ok]
    have : b.val.length ≤ i.val := by simp [Slice.length] at h; omega
    simp [List.drop_eq_nil_of_le this]
  | succ k ih =>
    intro i h
    rw [packets.tag_bytes_valid_from]
    have hlt : i < Slice.len b := by scalar_tac
    simp only [hlt, ↓reduceIte]
    step as ⟨ c, hc ⟩
    have hil : i.val < b.val.length := by simp [Slice.length] at h; omega
    have hd : b.val.drop i.val = c :: b.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hil, hc]
    rw [hd]
    split_ifs
    all_goals first
      | (exfalso; scalar_tac)
      | (have hr : tagRestByte c = false := by
            rw [← Bool.not_eq_true, tagRestByte_iff]; scalar_tac
         simp [hr])
      | (have hr : tagRestByte c = true := by rw [tagRestByte_iff]; scalar_tac
         step as ⟨ i2, hi2 ⟩
         apply WP.spec_mono (ih i2 (by scalar_tac))
         intro r hr2
         rw [hr2, hi2]
         simp [hr])

/-- `tag_bytes_valid b` is `tagBytesValid` of its bytes. -/
theorem tag_bytes_valid_spec (b : Slice U8) :
    packets.tag_bytes_valid b ⦃ r => r = tagBytesValid b.val ⦄ := by
  unfold packets.tag_bytes_valid
  simp only [core.slice.Slice.is_empty, bind_ok]
  rcases hb : b.val with _ | ⟨c, cs⟩
  · have : b.length = 0 := by simp [Slice.length, hb]
    simp [this, tagBytesValid]
  · have hl : b.length = cs.length + 1 := by simp [Slice.length, hb]
    have : ¬ (b.length = 0) := by omega
    simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte, packets.Tag.MAX_LEN]
    by_cases h32 : 32 < cs.length + 1
    · have : Slice.len b > 32#usize := by scalar_tac
      simp only [this, ↓reduceIte, WP.spec_ok]
      simp [tagBytesValid]; omega
    · have : ¬ Slice.len b > 32#usize := by scalar_tac
      simp only [this, ↓reduceIte]
      step as ⟨ c0, hc0 ⟩
      have hc : c0 = c := by simp [hc0, hb]
      subst hc
      have hcs : cs.length < 32 := by omega
      split_ifs
      all_goals first
        | (exfalso; scalar_tac)
        | (have hr : tagFirstByte c0 = false := by
              rw [← Bool.not_eq_true, tagFirstByte_iff]; scalar_tac
           simp [tagBytesValid, hr])
        | (have hr : tagFirstByte c0 = true := by rw [tagFirstByte_iff]; scalar_tac
           apply WP.spec_mono (tag_bytes_valid_from_spec b cs.length 1#usize (by simp [hl]; omega))
           intro r hr2
           rw [hr2, hb]
           simp [tagBytesValid, hr, hcs])

/-- `deserialize_tag` of a present, valid-UTF-8 tag (`tl` bytes, `0 < tl`): the tag consumed;
    `Some` of a tag with those bytes if they are a valid tag (`tagBytesValid`), else an error. -/
theorem tag_utf8 (tl : Usize) (buf : io.ParseBuf) (h0 : 0 < tl.val) (hle : tl.val ≤ buf.length)
    (hv : (Trusted.bytesOf (buf.val.take tl.val)).IsValidUTF8) :
    packets.Sid.deserialize_tag tl buf ⦃ r rest =>
      (okPart r).map (Option.map strCowBytes) =
        (if tagBytesValid (buf.val.take tl.val) then some (some (buf.val.take tl.val)) else none) ∧
      rest.val = buf.val.drop tl.val ⦄ := by
  unfold packets.Sid.deserialize_tag
  have : tl > 0#usize := by scalar_tac
  simp only [this, ↓reduceIte]
  step with io.ParseBuf.len_spec as ⟨ i, hi ⟩
  have : ¬ i < tl := by scalar_tac
  simp only [this, ↓reduceIte]
  step as ⟨ tb, htb, htbl ⟩
  have htb' : tb.val = buf.val.take tl.val := by rw [htb]; simp [List.slice]
  simp only [misc.trusted.sid_tag_from_utf8, htb', hv, ↓reduceIte, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  step with io.ParseBuf.skip_spec as ⟨ b1, hb1 ⟩
  step with tag_bytes_valid_spec tb as ⟨ bv, hbv ⟩
  rw [htb'] at hbv
  subst hbv
  split
  · rename_i htv
    obtain ⟨x, hx1, hx2⟩ : ∃ x, String.fromUTF8? (Trusted.bytesOf tb.val) = some x ∧ utf8 x = tb.val := by
      rw [htb']
      refine ⟨String.fromUTF8 _ hv, by simp [String.fromUTF8?, hv], CBTUtil.utf8_ofByteArray _ hv⟩
    simp only [Str.Insts.AllocBorrowToOwnedString.to_owned, hx1, bind_ok, WP.spec_ok]
    simp [okPart, hb1, strCowBytes, hx2, htb']
  · rename_i htv
    simp [misc.trusted.sid_tag_invalid_error, okPart, hb1]

theorem seq_new_vec (v : alloc.vec.Vec packets.GnoInterval) :
    misc.raw.seq.Seq.new misc.raw.int.LeU64 packets.GnoInterval.Insts.CoreCloneClone
      (core.convert.IntoFrom (alloc.borrow.CowASliceVec.Insts.CoreConvertFromVec
        packets.GnoInterval.Insts.CoreCloneClone)) v = ok (.Owned v, ()) :=
  misc.raw.seq.Seq.new_eq _ _ _ _ _ rfl

end SidUtil

/-- `Sid::new(uuid)`: the UUID, no tag, no intervals. -/
theorem packets.Sid.new_spec (uuid : Array U8 16#usize) :
    packets.Sid.new uuid ⦃ s => SidV.of s = ⟨uuid.val, none, []⟩ ⦄ := by
  unfold packets.Sid.new misc.raw.seq.Seq.Insts.CoreDefaultDefault.default
  rw [SidUtil.seq_new_vec]
  apply spec_bind_ok
  apply (WP.spec_ok _).mpr
  simp [SidV.of, cowList, alloc.vec.Vec.new]

/-- `uuid`: the field. -/
theorem packets.Sid.impl.uuid_eq (self : packets.Sid) :
    packets.Sid.impl.uuid self = ok self.uuid := by
  rfl

/-- `tag`: the field. -/
theorem packets.Sid.impl.tag_eq (self : packets.Sid) :
    packets.Sid.impl.tag self = ok self.tag := by
  unfold packets.Sid.impl.tag
  cases self.tag <;> rfl

/-- `intervals`: the intervals. -/
theorem packets.Sid.impl.intervals_spec (self : packets.Sid) :
    packets.Sid.impl.intervals self ⦃ s => s.val = cowList self.intervals.1 ⦄ := by
  unfold packets.Sid.impl.intervals
  step with misc.raw.seq.Seq.Insts.CoreOpsDerefDerefSlice.deref_spec as ⟨ s, hs ⟩
  simp [core.slice.index.Slice.index,
    hs]

/-- `with_interval(g)`: appends the interval (unchecked); nothing else changes. (Precondition:
    room for one more interval.) -/
theorem packets.Sid.with_interval_spec (self : packets.Sid) (g : packets.GnoInterval)
    (h : (cowList self.intervals.1).length < Usize.max) :
    packets.Sid.with_interval self g ⦃ s =>
      SidV.of s = { SidV.of self with
        intervals := (SidV.of self).intervals ++ [(g.start.1.val, g.«end».1.val)] } ⦄ := by
  unfold packets.Sid.with_interval misc.raw.cow_into_vec
  obtain ⟨uuid, tag, ⟨c, u⟩⟩ := self
  simp only at h ⊢
  have hcl : ∀ x : packets.GnoInterval, packets.GnoInterval.Insts.CoreCloneClone.clone x = ok x := fun _ => rfl
  cases c with
  | Borrowed sl =>
    step with alloc.slice.Slice.to_vec_spec packets.GnoInterval.Insts.CoreCloneClone sl (fun x _ => hcl x) as ⟨ v, hv ⟩
    step with alloc.vec.Vec.push_spec v g (by simp [hv, cowList] at h; exact h) as ⟨ v1, hv1 ⟩
    rw [SidUtil.seq_new_vec]
    apply spec_bind_ok
    apply (WP.spec_ok _).mpr
    dsimp only [SidV.of, cowList]
    rw [hv1, hv]
    simp
    rfl
  | Owned v =>
    apply spec_bind_ok
    step with alloc.vec.Vec.push_spec v g (by simp [cowList] at h ⊢; scalar_tac) as ⟨ v1, hv1 ⟩
    rw [SidUtil.seq_new_vec]
    apply spec_bind_ok
    apply (WP.spec_ok _).mpr
    dsimp only [SidV.of, cowList]
    rw [hv1]
    simp

/-- `with_intervals(v)`: replaces the intervals (unchecked); nothing else changes. -/
theorem packets.Sid.with_intervals_spec (self : packets.Sid) (v : alloc.vec.Vec packets.GnoInterval) :
    packets.Sid.with_intervals self v ⦃ s =>
      SidV.of s = { SidV.of self with intervals := v.val.map (fun g => (g.start.1.val, g.«end».1.val)) } ⦄ := by
  unfold packets.Sid.with_intervals
  rw [SidUtil.seq_new_vec]
  apply spec_bind_ok
  apply (WP.spec_ok _).mpr
  simp [SidV.of, cowList]

/-- `with_tag(t)`: sets the tag. -/
theorem packets.Sid.with_tag_eq (self : packets.Sid) (t : packets.Tag) :
    packets.Sid.with_tag self t = ok { self with tag := some t } := by
  rfl

/-- `MySerialize for Sid`: appends the untagged format `sidEnc` (UUID, interval count,
    intervals). **The tag is not written** (the tagged format is written only by
    `ComBinlogDumpGtid`). -/
theorem packets.Sid.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.Sid)
    (buf : alloc.vec.Vec U8) (h : buf.length + (sidEnc (SidV.of self)).length ≤ Usize.max) :
    packets.Sid.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ sidEnc (SidV.of self) ⦄ := by
  unfold packets.Sid.Insts.Mysql_commonProtoMySerialize.serialize
  have hfl : ((cowList self.intervals.1).map SidUtil.gnoPair).flatMap gnoEnc =
      (cowList self.intervals.1).flatMap (fun g => gnoEnc (SidUtil.gnoPair g)) := by
    rw [List.flatMap_map]
  have hlen16 : ((cowList self.intervals.1).flatMap (fun g => gnoEnc (SidUtil.gnoPair g))).length =
      16 * (cowList self.intervals.1).length := by
    rw [length_flatMap_const _ _ 16 (fun x _ => by simp [gnoEnc, PBUtil.length_leBytes])]
  have hS : SidV.of self = ⟨self.uuid.val, self.tag.map strCowBytes,
      (cowList self.intervals.1).map SidUtil.gnoPair⟩ := rfl
  rw [hS] at h ⊢
  simp only [sidEnc, intervalsEnc, List.length_append, List.length_map, hfl, hlen16] at h ⊢
  have hu : self.uuid.val.length = 16 := by simp
  rw [hu] at h
  step with ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨ b1, h1 ⟩
  apply misc.raw.seq.Seq.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro sl hsl
  have hmax := Usize.max_def
  have hlt : (cowList self.intervals.1).length < 2 ^ 64 - 1 := by
    have := lt_two_pow_64_of_le_max (show 16 * (cowList self.intervals.1).length ≤ Usize.max by
      simp [PBUtil.length_leBytes] at h; omega)
    omega
  apply WP.spec_mono (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize_spec
    packets.GnoInterval.Insts.Mysql_commonProtoMySerialize (fun g => gnoEnc (SidUtil.gnoPair g)) sl
    (fun x _ b hb => by
      apply packets.GnoInterval.Insts.Mysql_commonProtoMySerialize.serialize_spec
      simpa [gnoEnc, PBUtil.length_leBytes] using hb) b1 (by
      rw [hsl, List.take_of_length_le (by omega), hlen16]
      have hb1 : b1.length = buf.length + 16 := by simp [h1]
      have hbl : buf.length = buf.val.length := rfl
      simp [PBUtil.length_leBytes] at h; omega))
  intro b hb
  rw [hb, h1, hsl]
  have hsl' : sl.length = (cowList self.intervals.1).length := by simp [Slice.length, hsl]
  rw [hsl', Nat.min_eq_left (by omega), List.take_of_length_le (by omega)]
  simp

/-- `MyDeserialize for Sid`: `SIZE` is `None`. -/
theorem packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  unfold packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for Sid`: the untagged format (`sidRead`; the tag is `None`), exactly,
    whenever that reader returns. -/
theorem packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64)
    (buf : io.ParseBuf) (r0 : Option SidV) (rest0 : List U8) (h : sidRead buf.val = .done r0 rest0) :
    packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map SidV.of = r0 ∧ rest.val = rest0 ⦄ := by
  unfold packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with SidUtil.uuid_parse_spec buf as ⟨ r, buf1, hr ⟩
  unfold sidRead at h
  by_cases h16 : buf.val.length < 16
  · simp only [h16, ↓reduceIte, ReadOut.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [show ¬ 16 ≤ buf.val.length by omega, ↓reduceIte] at hr
    obtain ⟨hr1, rfl⟩ := hr
    cases r with
    | Ok _ => simp [okPart] at hr1
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart]
  · simp only [h16, ↓reduceIte] at h
    simp only [show 16 ≤ buf.val.length by omega, ↓reduceIte] at hr
    obtain ⟨hr1, hr2⟩ := hr
    cases r with
    | Err e => simp [okPart] at hr1
    | Ok val =>
      simp only [okPart, Option.map_some, Option.some.injEq] at hr1
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      rcases hi : intervalsRead (buf.val.drop 16) with ⟨o, rest⟩ | e | _
      · rw [hi] at h
        step with SidUtil.intervals_parse_done h64 buf1 o rest (by rw [hr2]; exact hi) as ⟨ r1, buf2, h1, h2 ⟩
        cases r1 with
        | Ok sq =>
          simp only [okPart, Option.map_some] at h1
          subst h1
          simp only at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [bind_ok]
          apply (WP.spec_ok _).mpr
          refine ⟨?_, h2⟩
          simp only [okPart, Option.map_some, SidV.of, hr1, Option.map_none]
          rfl
        | Err e =>
          simp only [okPart, Option.map_none] at h1
          subst h1
          simp only [ReadOut.done.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [okPart, h2, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · rw [hi] at h; simp at h
      · rw [hi] at h; simp at h

/-- **Crash path.** In the model, `MyDeserialize for Sid` panics where `sidRead` does: an
    interval count `n` from the input with `16 * n` above `usize::MAX` (`n ≥ 2^60`, unchecked
    multiplication). **Real Rust crashes earlier and more often**: `Vec::with_capacity(n)` runs
    first, before the count is checked against the input, so a large count aborts the process
    (out of memory), and `n ≥ 2^59` panics (capacity overflow), on a ~24-byte input; the model
    treats the allocation as free (allocation caveat) and returns an error for `n < 2^60`. The
    model's `16 * n` overflow is never reached in real Rust. -/
theorem packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_overflow (h64 : Target64)
    (buf : io.ParseBuf) (e : Error) (h : sidRead buf.val = .panic e) :
    packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf = fail e := by
  unfold packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  unfold sidRead at h
  by_cases h16 : buf.val.length < 16
  · simp [h16] at h
  · simp only [h16, ↓reduceIte] at h
    obtain ⟨⟨r, buf1⟩, he, hr⟩ := PBUtil.spec_eq_ok (SidUtil.uuid_parse_spec buf)
    rw [he]
    simp only [show 16 ≤ buf.val.length by omega, ↓reduceIte] at hr
    obtain ⟨hr1, hr2⟩ := hr
    cases r with
    | Err e => simp [okPart] at hr1
    | Ok val =>
      rcases hi : intervalsRead (buf.val.drop 16) with ⟨o, rest⟩ | e' | _
      · rw [hi] at h; rcases o with _ | is <;> simp at h
      · rw [hi] at h
        simp only [ReadOut.panic.injEq] at h
        subst h
        have hp := SidUtil.intervals_parse_panic h64 buf1 e' (by rw [hr2]; exact hi)
        simp [core.result.Result.Insts.CoreOpsTry.branch, hp]
      · rw [hi] at h; simp at h

/-- Round trip: the untagged format is read back, without the tag. -/
theorem packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h64 : Target64)
    (s : packets.Sid) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = sidEnc (SidV.of s) ++ tail) :
    packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map SidV.of = some { SidV.of s with tag := none } ∧ rest.val = tail ⦄ := by
  have hbl : buf.val.length ≤ Usize.max := by scalar_tac
  have hfl : ((SidV.of s).intervals.flatMap gnoEnc).length = 16 * (SidV.of s).intervals.length := by
    rw [length_flatMap_const _ _ 16 (fun x _ => by simp [gnoEnc, PBUtil.length_leBytes])]
  have hn : 16 * (SidV.of s).intervals.length ≤ Usize.max := by
    rw [h] at hbl
    simp only [sidEnc, intervalsEnc, List.length_append, hfl] at hbl
    omega
  have hr := SidUtil.sidRead_enc (SidV.of s) (by simp [SidV.of])
    (fun i hi => by
      simp only [SidV.of, List.mem_map] at hi
      obtain ⟨g, _, rfl⟩ := hi
      exact ⟨by scalar_tac, by scalar_tac⟩) hn tail
  rw [← h] at hr
  apply WP.spec_mono (packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec h64 buf _ _ hr)
  rintro ⟨r, rest⟩ hr'
  exact hr'

end mysql_common

namespace mysql_common

/-- `Sid::deserialize_tagged` (the tagged format, read by `ComBinlogDumpGtid`): exactly
    `sidTaggedRead` whenever that reader returns. -/
theorem packets.Sid.deserialize_tagged_spec (h64 : Target64) (buf : io.ParseBuf) (r0 : Option SidV)
    (rest0 : List U8) (h : sidTaggedRead buf.val = .done r0 rest0) :
    packets.Sid.deserialize_tagged buf ⦃ r rest => (okPart r).map SidV.of = r0 ∧ rest.val = rest0 ⦄ := by
  unfold packets.Sid.deserialize_tagged
  step with SidUtil.uuid_parse_spec buf as ⟨ r, buf1, hr ⟩
  unfold sidTaggedRead at h
  by_cases h16 : buf.val.length < 16
  · simp only [h16, ↓reduceIte, ReadOut.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [show ¬ 16 ≤ buf.val.length by omega, ↓reduceIte] at hr
    obtain ⟨hr1, rfl⟩ := hr
    cases r with
    | Ok _ => simp [okPart] at hr1
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart]
  · simp only [h16, ↓reduceIte] at h
    simp only [show 16 ≤ buf.val.length by omega, ↓reduceIte] at hr
    obtain ⟨hr1, hr2⟩ := hr
    cases r with
    | Err e => simp [okPart] at hr1
    | Ok val =>
      simp only [okPart, Option.map_some, Option.some.injEq] at hr1
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      step with misc.read_varlen_uint_spec buf1 as ⟨ r1, buf2, hv1, hv2 ⟩
      rw [hr2] at hv1
      rcases hd : varlenUintDecode (buf.val.drop 16) with _ | ⟨tl, rr⟩
      · rw [hd] at h hv1
        simp only [ReadOut.done.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases r1 with
        | Ok _ => simp [okPart] at hv1
        | Err e =>
          have := hv2 rfl
          subst this
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart, hr2]
      · rw [hd] at h hv1
        cases r1 with
        | Err e => simp [okPart] at hv1
        | Ok n =>
          simp only [okPart, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv1
          obtain ⟨hn, hb2⟩ := hv1
          simp only [lift, bind_ok]
          have htl : (UScalar.cast UScalarTy.Usize n).val = tl := by rw [PBUtil.cast_usize_64 h64, hn]
          by_cases h0 : tl = 0
          · simp only [h0, ↓reduceIte] at h
            step with SidUtil.tag_zero (UScalar.cast UScalarTy.Usize n) buf2 (by rw [htl, h0]) as ⟨ r2, buf3, hr2a, hr2b ⟩
            subst hr2a hr2b
            simp only
            rcases hi : intervalsRead rr with ⟨o, rest⟩ | e | _
            · rw [hi] at h
              step with SidUtil.intervals_parse_done h64 buf3 o rest (by rw [hb2]; exact hi) as ⟨ r3, buf4, h3, h4 ⟩
              cases r3 with
              | Ok sq =>
                simp only [okPart, Option.map_some] at h3
                subst h3
                simp only at h
                obtain ⟨rfl, rfl⟩ := h
                simp only [bind_ok]
                apply (WP.spec_ok _).mpr
                refine ⟨?_, h4⟩
                simp only [okPart, Option.map_some, SidV.of, hr1, Option.map_none]
                rfl
              | Err e =>
                simp only [okPart, Option.map_none] at h3
                subst h3
                simp only [ReadOut.done.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                simp [okPart, h4, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            · rw [hi] at h; simp at h
            · rw [hi] at h; simp at h
          · simp only [h0, ↓reduceIte] at h
            have hl2 : buf2.length = rr.length := by simp [Slice.length, hb2]
            by_cases hs : rr.length < tl
            · simp only [hs, ↓reduceIte, ReadOut.done.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              step with SidUtil.tag_short (UScalar.cast UScalarTy.Usize n) buf2 (by rw [htl]; omega) (by rw [htl]; omega) as ⟨ r2, buf3, hr2a, hr2b ⟩
              subst hr2b
              cases r2 with
              | Ok _ => simp [okPart] at hr2a
              | Err e => simp [okPart, hb2, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            · simp only [hs, ↓reduceIte] at h
              by_cases hu : (Trusted.bytesOf (rr.take tl)).IsValidUTF8
              · simp only [hu, not_true_eq_false, ↓reduceIte] at h
                step with SidUtil.tag_utf8 (UScalar.cast UScalarTy.Usize n) buf2 (by rw [htl]; omega) (by rw [htl]; omega) (by rw [htl, hb2]; exact hu) as ⟨ r2, buf3, hr2a, hr2b ⟩
                rw [htl, hb2] at hr2a hr2b
                by_cases htv : tagBytesValid (rr.take tl)
                · simp only [htv, ↓reduceIte] at h hr2a
                  cases r2 with
                  | Err _ => simp [okPart] at hr2a
                  | Ok t =>
                    simp only [okPart, Option.map_some, Option.some.injEq] at hr2a
                    simp only
                    rcases hi : intervalsRead (rr.drop tl) with ⟨o, rest⟩ | e | _
                    · rw [hi] at h
                      step with SidUtil.intervals_parse_done h64 buf3 o rest (by rw [hr2b]; exact hi) as ⟨ r3, buf4, h3, h4 ⟩
                      cases r3 with
                      | Ok sq =>
                        simp only [okPart, Option.map_some] at h3
                        subst h3
                        simp only at h
                        obtain ⟨rfl, rfl⟩ := h
                        simp only [bind_ok]
                        apply (WP.spec_ok _).mpr
                        refine ⟨?_, h4⟩
                        simp only [okPart, Option.map_some, SidV.of, hr1, hr2a]
                        rfl
                      | Err e =>
                        simp only [okPart, Option.map_none] at h3
                        subst h3
                        simp only [ReadOut.done.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        simp [okPart, h4, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                    · rw [hi] at h; simp at h
                    · rw [hi] at h; simp at h
                · simp only [htv, Bool.false_eq_true, ↓reduceIte, ReadOut.done.injEq] at h hr2a
                  obtain ⟨rfl, rfl⟩ := h
                  cases r2 with
                  | Ok _ => simp [okPart] at hr2a
                  | Err e =>
                    simp [okPart, hr2b, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              · simp only [hu, not_false_eq_true, ↓reduceIte, ReadOut.done.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                step with SidUtil.tag_invalid (UScalar.cast UScalarTy.Usize n) buf2 (by rw [htl]; omega) (by rw [htl]; omega) (by rw [htl, hb2]; exact hu) as ⟨ r2, buf3, hr2a, hr2b ⟩
                subst hr2b
                cases r2 with
                | Ok _ => simp [okPart] at hr2a
                | Err e => simp [okPart, hb2, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `Sid::deserialize_tagged` panics where `sidTaggedRead` does (an interval count overflow after
    an empty or a valid tag). -/
theorem packets.Sid.deserialize_tagged_panics (h64 : Target64) (buf : io.ParseBuf) (e : Error)
    (h : sidTaggedRead buf.val = .panic e) :
    packets.Sid.deserialize_tagged buf = fail e := by
  unfold packets.Sid.deserialize_tagged
  unfold sidTaggedRead at h
  by_cases h16 : buf.val.length < 16
  · simp [h16] at h
  · simp only [h16, ↓reduceIte] at h
    obtain ⟨⟨r, buf1⟩, he, hr⟩ := PBUtil.spec_eq_ok (SidUtil.uuid_parse_spec buf)
    rw [he]
    simp only [show 16 ≤ buf.val.length by omega, ↓reduceIte] at hr
    obtain ⟨hr1, hr2⟩ := hr
    cases r with
    | Err e => simp [okPart] at hr1
    | Ok val =>
      obtain ⟨⟨r1, buf2⟩, he1, hv1, hv2⟩ := PBUtil.spec_eq_ok (misc.read_varlen_uint_spec buf1)
      rw [hr2] at hv1
      rcases hd : varlenUintDecode (buf.val.drop 16) with _ | ⟨tl, rr⟩
      · rw [hd] at h; simp at h
      · rw [hd] at h hv1
        cases r1 with
        | Err e => simp [okPart] at hv1
        | Ok n =>
          simp only [okPart, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv1
          obtain ⟨hn, hb2⟩ := hv1
          have htl : (UScalar.cast UScalarTy.Usize n).val = tl := by rw [PBUtil.cast_usize_64 h64, hn]
          by_cases h0 : tl = 0
          · simp only [h0, ↓reduceIte] at h
            obtain ⟨⟨r2, buf3⟩, he2, hr2a, hr2b⟩ := PBUtil.spec_eq_ok
              (SidUtil.tag_zero (UScalar.cast UScalarTy.Usize n) buf2 (by rw [htl, h0]))
            subst hr2a hr2b
            rcases hi : intervalsRead rr with ⟨o, rest⟩ | e' | _
            · rw [hi] at h; rcases o with _ | is <;> simp at h
            · rw [hi] at h
              simp only [ReadOut.panic.injEq] at h
              subst h
              have hp := SidUtil.intervals_parse_panic h64 buf3 e' (by rw [hb2]; exact hi)
              simp [core.result.Result.Insts.CoreOpsTry.branch, he1, lift, he2, hp]
            · rw [hi] at h; simp at h
          · simp only [h0, ↓reduceIte] at h
            by_cases hs : rr.length < tl
            · simp [hs] at h
            by_cases hu : (Trusted.bytesOf (rr.take tl)).IsValidUTF8
            swap
            · simp [hs, hu] at h
            by_cases htv : tagBytesValid (rr.take tl)
            swap
            · simp [hs, hu, htv] at h
            simp only [hs, hu, htv, not_true_eq_false, ↓reduceIte] at h
            have hl2 : buf2.length = rr.length := by simp [Slice.length, hb2]
            obtain ⟨⟨r2, buf3⟩, he2, hr2a, hr2b⟩ := PBUtil.spec_eq_ok
              (SidUtil.tag_utf8 (UScalar.cast UScalarTy.Usize n) buf2 (by rw [htl]; omega)
                (by rw [htl]; omega) (by rw [htl, hb2]; exact hu))
            rw [htl, hb2] at hr2a hr2b
            simp only [htv, ↓reduceIte] at hr2a
            cases r2 with
            | Err _ => simp [okPart] at hr2a
            | Ok t =>
              rcases hi : intervalsRead (rr.drop tl) with ⟨o, rest⟩ | e' | _
              · rw [hi] at h; rcases o with _ | is <;> simp at h
              · rw [hi] at h
                simp only [ReadOut.panic.injEq] at h
                subst h
                have hp := SidUtil.intervals_parse_panic h64 buf3 e' (by rw [hr2b]; exact hi)
                simp [core.result.Result.Insts.CoreOpsTry.branch, he1, lift, he2, hp]
              · rw [hi] at h; simp at h

theorem SidUtil.extend_from_slice_spec (v : alloc.vec.Vec U8) (s : Slice U8)
    (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ r => r.val = v.val ++ s.val ⦄ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [dite_eq_left h]
  have := List.clone_spec (clone := core.clone.CloneU8.clone) (l := s.val) (by intros; rfl)
  obtain ⟨l, hl, hp⟩ := PBUtil.spec_eq_ok this
  simp [hl, hp.1]

theorem SidUtil.tag_str_spec (self : packets.Sid)
    (hfit : ((self.tag.map strCowBytes).getD []).length ≤ Usize.max) :
    packets.Sid.tag_str self ⦃ s => s.val = (self.tag.map strCowBytes).getD [] ⦄ := by
  unfold packets.Sid.tag_str
  cases ht : self.tag with
  | none => simp only [toStr]; exact (WP.spec_ok _).mpr (by rw [Slice.from_val]; simp)
  | some t =>
    rw [ht] at hfit
    exact packets.Tag.as_str_spec t (by simpa using hfit)

/-- `Sid::serialize_tagged`: appends the tagged format `sidTaggedEnc` (UUID, the tag length as a
    varlen integer, the tag bytes, the intervals). -/
theorem packets.Sid.serialize_tagged_spec (self : packets.Sid) (buf : alloc.vec.Vec U8)
    (h : buf.length + (sidTaggedEnc (SidV.of self)).length ≤ Usize.max) :
    packets.Sid.serialize_tagged self buf ⦃ buf' => buf'.val = buf.val ++ sidTaggedEnc (SidV.of self) ⦄ := by
  unfold packets.Sid.serialize_tagged
  have hfl : ((cowList self.intervals.1).map SidUtil.gnoPair).flatMap gnoEnc =
      (cowList self.intervals.1).flatMap (fun g => gnoEnc (SidUtil.gnoPair g)) := by
    rw [List.flatMap_map]
  have hlen16 : ((cowList self.intervals.1).flatMap (fun g => gnoEnc (SidUtil.gnoPair g))).length =
      16 * (cowList self.intervals.1).length := by
    rw [length_flatMap_const _ _ 16 (fun x _ => by simp [gnoEnc, PBUtil.length_leBytes])]
  have hS : SidV.of self = ⟨self.uuid.val, self.tag.map strCowBytes,
      (cowList self.intervals.1).map SidUtil.gnoPair⟩ := rfl
  rw [hS] at h ⊢
  generalize ht : (self.tag.map strCowBytes).getD [] = tb at h ⊢
  simp only [sidTaggedEnc, intervalsEnc, List.length_append, List.length_map, hfl, hlen16, ht,
    IntAndMisc.varlenUint_length', PBUtil.length_leBytes] at h ⊢
  have hu : self.uuid.val.length = 16 := by simp
  rw [hu] at h
  have hbl : buf.length = buf.val.length := rfl
  step with ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨ b1, h1 ⟩
  step with SidUtil.tag_str_spec self (by rw [ht]; omega) as ⟨ ts, hts ⟩
  rw [ht] at hts
  simp only [core.str.Str.len, bind_ok, lift]
  have hil : (Slice.len ts).val = tb.length := by
    have := Slice.len_val ts; rw [← hts]; exact this
  have hcast : (UScalar.cast UScalarTy.U64 (Slice.len ts)).val = tb.length := by
    rw [UScalar.cast_val_eq, hil]
    exact Nat.mod_eq_of_lt (by have := lt_two_pow_64_of_le_max (show tb.length ≤ Usize.max by omega); simpa using this)
  have hb1 : b1.length = buf.val.length + 16 := by simp [h1]
  step with misc.write_varlen_uint_spec b1 _ (by rw [hcast]; omega) as ⟨ b2, h2 ⟩
  simp only [core.str.Str.as_bytes]
  apply spec_bind_ok
  have hb2 : b2.length = buf.val.length + 16 + varlenUintSize tb.length := by
    simp [h2, h1, hcast, IntAndMisc.varlenUint_length']; omega
  have hb2' : b2.length = b2.val.length := rfl
  step with SidUtil.extend_from_slice_spec b2 ts (by simp [Slice.length, hts]; omega) as ⟨ b3, h3 ⟩
  apply misc.raw.seq.Seq.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro sl hsl
  have hlt : (cowList self.intervals.1).length < 2 ^ 64 - 1 := by
    have := lt_two_pow_64_of_le_max (show 16 * (cowList self.intervals.1).length ≤ Usize.max by omega)
    omega
  apply WP.spec_mono (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize_spec
    packets.GnoInterval.Insts.Mysql_commonProtoMySerialize (fun g => gnoEnc (SidUtil.gnoPair g)) sl
    (fun x _ b hb => by
      apply packets.GnoInterval.Insts.Mysql_commonProtoMySerialize.serialize_spec
      simpa [gnoEnc, PBUtil.length_leBytes] using hb) b3 (by
      rw [hsl, List.take_of_length_le (by omega), hlen16]
      have hb3 : b3.length = b2.length + tb.length := by simp [h3, hts]
      omega))
  intro b hb
  rw [hb, h3, h2, h1, hsl, hcast, hts]
  have hsl' : sl.length = (cowList self.intervals.1).length := by simp [Slice.length, hsl]
  rw [hsl', Nat.min_eq_left (by omega), List.take_of_length_le (by omega)]
  simp

end mysql_common
