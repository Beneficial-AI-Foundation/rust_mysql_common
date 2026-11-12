import Defs
import Proofs.Io.ParseBuf
import Proofs.Io.BufMutExt

/-! Helper lemmas for the `IntAndMisc` proofs. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace IntAndMisc

/-! ## Hoare triples -/

theorem spec_bind_inv {α β : Type} {m : Result α} {k : α → Result β} {P : Post β}
    (h : spec (Std.bind m k) P) : spec m (fun x => spec (k x) P) := by
  cases m
  · simp_all
  · simp_all
  · simp_all

/-- A failing first step makes the whole computation fail. -/
theorem not_spec_bind {α β : Type} {m : Result α} {k : α → Result β} {P : Post β}
    (h : ¬ spec m (fun _ => True)) : ¬ spec (Std.bind m k) P := by
  intro h'
  exact h (spec_mono (spec_bind_inv h') (fun _ _ => trivial))

theorem leBytes_bv' (k : Nat) : ∀ (w : Nat) (_ : w = 8 * k) (b : BitVec w),
    b.toLEBytes.map (@UScalar.mk UScalarTy.U8) = leBytes k b.toNat := by
  induction k with
  | zero => intro w hw b; subst hw; simp [BitVec.toLEBytes, leBytes]
  | succ k ih =>
    intro w hw b
    rw [BitVec.toLEBytes]
    simp only [show w > 0 by omega, ↓reduceIte, List.map_cons, leBytes]
    rw [ih (w - 8) (by omega)]
    congr 1
    · simp only [byte]; congr 1; apply BitVec.eq_of_toNat_eq; simp
    · congr 1; simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hb := b.isLt
      apply Nat.mod_eq_of_lt
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
      rw [show w - 8 + 8 = w by omega]; exact hb

theorem leBytes_bv {w : Nat} (k : Nat) (hw : w = 8 * k) (b : BitVec w) :
    b.toLEBytes.map (@UScalar.mk UScalarTy.U8) = leBytes k b.toNat := leBytes_bv' k w hw b

@[step]
theorem put_slice_spec (buf : alloc.vec.Vec U8) (s : Slice U8) (h : buf.length + s.length ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_slice buf s ⦃ b' => b'.val = buf.val ++ s.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_slice alloc.vec.Vec.extend_from_slice
  simp only [h, ↓reduceDIte]
  apply spec_bind (List.clone_spec (by intro x _; rfl))
  intro l hl
  simp [hl.1]

theorem bv_toNat_signed {w : Nat} (b : BitVec w) : b.toNat = (b.toInt % (2 ^ w : Int)).toNat := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := b.isLt
  have h2 : ((b.toNat : Int)) < (2 ^ w : Int) := by exact_mod_cast this
  split
  · rw [Int.emod_eq_of_lt (by omega) h2]; simp
  · push_cast; rw [Int.sub_emod_right,Int.emod_eq_of_lt (by omega) h2]; simp

theorem ival_bv {ty : IScalarTy} (x : IScalar ty) : x.bv.toNat = (x.val % (2 ^ ty.numBits : Int)).toNat := by
  rw [bv_toNat_signed]; rfl

@[step]
theorem put_u16_le_spec (buf : alloc.vec.Vec U8) (x : U16) (h : buf.length + 2 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u16_le buf x ⦃ b' => b'.val = buf.val ++ leBytes 2 x.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u16_le
  step*
  simp [*, leBytes_bv 2 rfl]

@[step]
theorem put_u32_le_spec (buf : alloc.vec.Vec U8) (x : U32) (h : buf.length + 4 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u32_le buf x ⦃ b' => b'.val = buf.val ++ leBytes 4 x.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u32_le
  step*
  simp [*, leBytes_bv 4 rfl]

@[step]
theorem put_u64_le_spec (buf : alloc.vec.Vec U8) (x : U64) (h : buf.length + 8 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u64_le buf x ⦃ b' => b'.val = buf.val ++ leBytes 8 x.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u64_le
  step*
  simp [*, leBytes_bv 8 rfl]

@[step]
theorem put_i16_le_spec (buf : alloc.vec.Vec U8) (x : I16) (h : buf.length + 2 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_i16_le buf x ⦃ b' => b'.val = buf.val ++ leBytesI 2 x.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_i16_le
  step*
  simp [*, leBytes_bv 2 rfl, leBytesI, ival_bv]

@[step]
theorem put_i32_le_spec (buf : alloc.vec.Vec U8) (x : I32) (h : buf.length + 4 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_i32_le buf x ⦃ b' => b'.val = buf.val ++ leBytesI 4 x.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_i32_le
  step*
  simp [*, leBytes_bv 4 rfl, leBytesI, ival_bv]

@[step]
theorem put_i64_le_spec (buf : alloc.vec.Vec U8) (x : I64) (h : buf.length + 8 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_i64_le buf x ⦃ b' => b'.val = buf.val ++ leBytesI 8 x.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_i64_le
  step*
  simp [*, leBytes_bv 8 rfl, leBytesI, ival_bv]

@[step]
theorem put_u8_spec (buf : alloc.vec.Vec U8) (x : U8) (h : buf.length + 1 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u8 buf x ⦃ b' => b'.val = buf.val ++ [x] ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u8
  step*

@[step]
theorem put_i8_spec (buf : alloc.vec.Vec U8) (x : I8) (h : buf.length + 1 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_i8 buf x ⦃ b' => b'.val = buf.val ++ leBytesI 1 x.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_i8
  step*
  simp [b'_post, s_post, i_post, leBytesI, leBytes, IScalar.hcast, byte]
  apply BitVec.eq_of_toNat_eq
  rw [ival_bv]; simp; omega

/-! ## Byte lists -/

theorem leNat_leBytes' (k : Nat) : ∀ n : Nat, leNat (leBytes k n) = n % 2 ^ (8 * k) := by
  induction k with
  | zero => intro n; simp [leBytes, leNat, Nat.mod_one]
  | succ k ih =>
    intro n
    simp only [leBytes, leNat, ih, byte]
    simp only [UScalar.val]
    rw [show 8 * (k + 1) = 8 + 8 * k by ring, Nat.pow_add, Nat.mod_mul]
    norm_num
    ring_nf
    simp [BitVec.toNat_ofNat]

@[simp] theorem length_leBytes' (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

@[simp] theorem length_leBytesI (k : Nat) (x : Int) : (leBytesI k x).length = k := by
  simp [leBytesI]

theorem leBytes_mod (k : Nat) : ∀ n : Nat, leBytes k (n % 2 ^ (8 * k)) = leBytes k n := by
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    simp only [leBytes]
    congr 1
    · simp only [byte]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      rw [show 8 * (k + 1) = 8 + 8 * k by ring, Nat.pow_add, Nat.mod_mul_right_mod]
    · rw [show 8 * (k + 1) = 8 + 8 * k by ring, Nat.pow_add, Nat.mod_mul_right_div_self, ih]

theorem leNat_lt : ∀ bs : List U8, leNat bs < 2 ^ (8 * bs.length)
  | [] => by simp [leNat]
  | b :: bs => by
    have := leNat_lt bs
    have hb := b.hBounds
    simp only [leNat, List.length_cons]
    rw [show 8 * (bs.length + 1) = 8 + 8 * bs.length by ring, Nat.pow_add]
    simp only [UScalarTy.numBits] at hb
    nlinarith

theorem leBytes_take_drop (k n : Nat) (tail : List U8) :
    (leBytes k n ++ tail).take k = leBytes k n ∧ (leBytes k n ++ tail).drop k = tail := by
  constructor
  · rw [List.take_append_of_le_length (by simp)]; simp
  · rw [List.drop_append_of_le_length (by simp)]; simp

theorem leBytesI_take_drop (k : Nat) (x : Int) (tail : List U8) :
    (leBytesI k x ++ tail).take k = leBytesI k x ∧ (leBytesI k x ++ tail).drop k = tail :=
  leBytes_take_drop k _ tail

theorem leNat_leBytesI (k : Nat) (x : Int) : leNat (leBytesI k x) = (x % (2 ^ (8 * k) : Int)).toNat := by
  unfold leBytesI
  rw [leNat_leBytes']
  apply Nat.mod_eq_of_lt
  have h1 : (0 : Int) < 2 ^ (8 * k) := by positivity
  have h2 := Int.emod_lt_of_pos x h1
  have h3 := Int.emod_nonneg x (ne_of_gt h1)
  have : ((x % (2 ^ (8 * k) : Int)).toNat : Int) < ((2 ^ (8 * k) : Nat) : Int) := by
    rw [Int.toNat_of_nonneg h3]; push_cast; exact h2
  exact_mod_cast this

theorem toSigned_emod (w : Nat) (hw : 0 < w) (x : Int) (h1 : -2 ^ (w - 1) ≤ x) (h2 : x < 2 ^ (w - 1)) :
    toSigned w (x % (2 ^ w : Int)).toNat = x := by
  have hM : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : (0 : Int) < 2 ^ (w - 1) := by positivity
  have hc : ∀ n : Nat, (n < 2 ^ (w - 1) ↔ (n : Int) < 2 ^ (w - 1)) := by
    intro n; constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  unfold toSigned
  generalize hn : (x % (2 ^ w : Int)).toNat = n
  have hn' : (n : Int) = x % (2 ^ w : Int) := by
    rw [← hn, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
  have hcn := hc n
  rw [hM] at hn' ⊢
  generalize (2 : Int) ^ (w - 1) = M at *
  have key : (n : Int) = if 0 ≤ x then x else x + 2 * M := by
    split
    · rw [hn', Int.emod_eq_of_lt (by omega) (by omega)]
    · rw [hn', ← Int.add_mul_emod_self_left x (2 * M) 1]
      rw [Int.emod_eq_of_lt (by omega) (by omega)]; ring
  split <;> rename_i hh
  · have := hcn.1 hh
    split at key <;> omega
  · have : ¬ (n : Int) < M := fun h => hh (hcn.2 h)
    split at key <;> omega

/-! ## `RawInt` -/

@[step]
theorem rawint_new_spec {T P : Type} (inst : misc.raw.int.IntRepr T P) (x : P) :
    misc.raw.int.RawInt.new inst x ⦃ r => r = (x, ()) ⦄ := by
  unfold misc.raw.int.RawInt.new
  exact (spec_ok _).2 rfl

@[step]
theorem rawint_deref_spec {T P : Type} (inst : misc.raw.int.IntRepr T P) (self : misc.raw.int.RawInt T P) :
    misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref inst self ⦃ r => r = self.1 ⦄ := by
  unfold misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref
  exact (spec_ok _).2 rfl

@[step]
theorem rawflags_new_spec {T B : Type} (U : Type) (fl : bitflags.traits.Flags T B) (value : B) :
    misc.raw.flags.RawFlags.new U fl value ⦃ r => r = (value, ()) ⦄ := by
  unfold misc.raw.flags.RawFlags.new
  exact (spec_ok _).2 rfl

@[step]
theorem rawconst_new_spec {T P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P) (t : P) :
    misc.raw._const.RawConst.new U inst t ⦃ r => r = (t, ()) ⦄ := by
  unfold misc.raw._const.RawConst.new
  exact (spec_ok _).2 rfl

@[step]
theorem const_new_spec {T : Type} (U : Type) (t : T) :
    misc.raw._const.Const.new U t ⦃ r => r = (t, ()) ⦄ := by
  unfold misc.raw._const.Const.new
  exact (spec_ok _).2 rfl

theorem rawint_new_bind {T P β : Type} (inst : misc.raw.int.IntRepr T P) (x : P)
    (f : misc.raw.int.RawInt T P → Result β) :
    Std.bind (misc.raw.int.RawInt.new inst x) f = f (x, ()) :=
  Std.bind_ok (α := misc.raw.int.RawInt T P) (x, ()) f

theorem rawint_deserialize_spec {T P : Type} (inst : misc.raw.int.IntRepr T P)
    (buf : io.ParseBuf) (Q : Option P → io.ParseBuf → Prop)
    (h : inst.deserialize buf ⦃ r rest => Q (okPart r) rest ⦄) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize inst () buf ⦃ r rest => Q ((okPart r).map (·.1)) rest ⦄ := by
  unfold misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with h as ⟨ r, rest, hq ⟩
  cases r
  · step*
    subst ri_post
    exact hq
  · step*
    simpa [okPart] using hq

/-- `parse::<RawInt<T>>` for a fixed-size `T` (`SIZE = Some n`). -/
theorem parse_rawint {T P : Type} (inst : misc.raw.int.IntRepr T P) (n : Usize)
    (hs : inst.SIZE = ok (some n)) (buf : io.ParseBuf) (Q : Option P → Prop)
    (hd : ∀ sub : io.ParseBuf, sub.val = buf.val.take n.val → n.val ≤ buf.length →
      inst.deserialize sub ⦃ r _ => Q (okPart r) ⦄) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple inst) buf () ⦃ r rest =>
      if n.val ≤ buf.length then Q ((okPart r).map (·.1)) ∧ rest.val = buf.val.drop n.val
      else okPart r = none ∧ rest = buf ⦄ := by
  have hs' : (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple inst).SIZE = ok (some n) := by
    simpa [misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE] using hs
  by_cases hl : n.val ≤ buf.length
  · have := io.ParseBuf.parse_of_size _ buf () n hs' hl (fun o => Q (o.map (·.1))) (by
      intro sub hsub
      have h1 := rawint_deserialize_spec inst sub (fun o _ => Q o) (hd sub hsub hl)
      exact h1)
    apply spec_mono this
    rintro ⟨r, rest⟩ h
    simpa [hl] using h
  · have := io.ParseBuf.parse_of_size_short _ buf () n hs' (by omega)
    apply spec_mono this
    rintro ⟨r, rest⟩ h
    simpa [hl] using h

/-- `parse::<T>` for a fixed-size `T` (`SIZE = Some n`). -/
theorem parse_fixed {T Ctx : Type} (inst : proto.MyDeserialize T Ctx) (n : Usize)
    (hs : inst.SIZE = ok (some n)) (buf : io.ParseBuf) (ctx : Ctx) (Q : Option T → Prop)
    (hd : ∀ sub : io.ParseBuf, sub.val = buf.val.take n.val → n.val ≤ buf.length →
      inst.deserialize ctx sub ⦃ r _ => Q (okPart r) ⦄) :
    io.ParseBuf.parse inst buf ctx ⦃ r rest =>
      if n.val ≤ buf.length then Q (okPart r) ∧ rest.val = buf.val.drop n.val
      else okPart r = none ∧ rest = buf ⦄ := by
  by_cases hl : n.val ≤ buf.length
  · have := io.ParseBuf.parse_of_size inst buf ctx n hs hl Q (fun sub hsub => hd sub hsub hl)
    apply spec_mono this
    rintro ⟨r, rest⟩ h
    simpa [hl] using h
  · have := io.ParseBuf.parse_of_size_short inst buf ctx n hs (by omega)
    apply spec_mono this
    rintro ⟨r, rest⟩ h
    simpa [hl] using h

/-! ## Errors -/

@[step]
theorem io_error_from_spec {E : Type} (inst : core.error.Error E) (kind : core.io.error.ErrorKind) (err : E) :
    misc.io_error_from inst kind err ⦃ _ => True ⦄ := by
  simp [misc.io_error_from]

@[step]
theorem unexpected_buf_eof_spec : misc.unexpected_buf_eof ⦃ _ => True ⦄ := by
  simp [misc.unexpected_buf_eof, misc.io_error_msg]

end IntAndMisc
