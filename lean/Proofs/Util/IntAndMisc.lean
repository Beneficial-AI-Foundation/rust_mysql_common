import Defs
import Proofs.Io.ParseBuf
import Proofs.Util.ParseBuf

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

attribute [simp] PBUtil.length_leBytes

theorem take_leBytes (k : Nat) : ∀ (m n : Nat), k ≤ m → (leBytes m n).take k = leBytes k n := by
  induction k with
  | zero => intro m n _; simp [leBytes]
  | succ k ih =>
    intro m n hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp [leBytes, ih m' (n / 256) (by omega)]


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
  rw [PBUtil.leNat_leBytes]
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

theorem toNat_emod_emod (x : Int) (k : Nat) (hk : k ≤ 8) :
    (x % (2 ^ 64 : Int)).toNat % 2 ^ (8 * k) = (x % (2 ^ (8 * k) : Int)).toNat := by
  have hd : ((2 : Int) ^ (8 * k)) ∣ 2 ^ 64 := pow_dvd_pow 2 (by omega)
  rw [← Int.emod_emod_of_dvd x hd]
  rw [Int.toNat_emod (Int.emod_nonneg _ (by positivity)) (by positivity)]
  congr 1

theorem leBytes_int64 (k : Nat) (hk : k ≤ 8) (x : Int) :
    leBytes k (x % (2 ^ 64 : Int)).toNat = leBytesI k x := by
  rw [leBytesI, ← leBytes_mod k, toNat_emod_emod x k hk]

@[step]
theorem put_uint_le_spec (buf : alloc.vec.Vec U8) (x : U64) (k : Usize) (hk : k.val ≤ 8)
    (h : buf.length + k.val ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_uint_le buf x k ⦃ b' => b'.val = buf.val ++ leBytes k.val x.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_uint_le
  step*
  rw [b'_post, s_post]
  simp [List.slice, slice_post, leBytes_bv 8 rfl, take_leBytes _ _ _ hk]

@[step]
theorem put_int_le_spec (buf : alloc.vec.Vec U8) (x : I64) (k : Usize) (hk : k.val ≤ 8)
    (h : buf.length + k.val ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_int_le buf x k ⦃ b' => b'.val = buf.val ++ leBytesI k.val x.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_int_le
  step*
  rw [b'_post, s_post, ← leBytes_int64 _ hk]
  simp [List.slice, slice_post, leBytes_bv 8 rfl, take_leBytes _ _ _ hk, ival_bv]

/-! ## JSONB varlen -/

theorem jsonbVarLen_lt (n : Nat) (h : n < 128) : jsonbVarLen n = [byte n] := by
  rw [jsonbVarLen]; simp [h]

theorem jsonbVarLen_ge (n : Nat) (h : 128 ≤ n) :
    jsonbVarLen n = byte (n % 128 + 128) :: jsonbVarLen (n / 128) := by
  rw [jsonbVarLen]; simp [show ¬ n < 128 by omega]

theorem jsonbVarLen_props (n : Nat) : ∀ (k : Nat) (t : List U8), (jsonbVarLen n).length ≤ k →
    base128 (jsonbVarLen n) = n ∧
    (((jsonbVarLen n ++ t).take k).findIdx? (fun b => decide (b.val < 128))) =
      some ((jsonbVarLen n).length - 1) ∧
    0 < (jsonbVarLen n).length := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k t hk
    by_cases h : n < 128
    · rw [jsonbVarLen_lt n h] at hk ⊢
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
      simp [base128, PBUtil.byte_val, Nat.mod_eq_of_lt (by omega : n < 256), Nat.mod_eq_of_lt h,
        List.findIdx?_cons, h]
    · rw [jsonbVarLen_ge n (by omega)] at hk ⊢
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
      simp only [List.length_cons] at hk
      obtain ⟨h1, h2, h3⟩ := ih (n / 128) (by omega) k' t (by omega)
      have hb : (byte (n % 128 + 128)).val = n % 128 + 128 := by
        rw [PBUtil.byte_val]; omega
      refine ⟨?_, ?_, by simp⟩
      · simp only [base128, hb, h1]; omega
      · simp only [List.cons_append, List.take_succ_cons, List.findIdx?_cons, hb, h2]
        simp
        omega

theorem jsonbVarLen_length_le (n m : Nat) (h : n < 128 ^ (m + 1)) : (jsonbVarLen n).length ≤ m + 1 := by
  induction m generalizing n with
  | zero => rw [jsonbVarLen_lt n (by simpa using h)]; simp
  | succ m ih =>
    by_cases h' : n < 128
    · rw [jsonbVarLen_lt n h']; simp
    · rw [jsonbVarLen_ge n (by omega)]
      simp only [List.length_cons]
      have := ih (n / 128) (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at h; exact h)
      omega

theorem jsonbVarLenRead_jsonbVarLen' (n : Nat) (t : List U8) (hn : n < 2 ^ 32) :
    jsonbVarLenRead (jsonbVarLen n ++ t) = (some n, t) := by
  have hl := jsonbVarLen_length_le n 4 (by omega)
  obtain ⟨h1, h2, h3⟩ := jsonbVarLen_props n 5 t hl
  unfold jsonbVarLenRead
  rw [h2]
  simp only [Nat.sub_add_cancel h3]
  rw [List.take_append_of_le_length (le_refl _), List.take_length, List.drop_append_of_le_length (le_refl _),
    List.drop_length, List.nil_append, h1]
  simp only [hn, ↓reduceIte]

theorem base128_append (l : List U8) (c : U8) :
    base128 (l ++ [c]) = base128 l + 128 ^ l.length * (c.val % 128) := by
  induction l with
  | nil => simp [base128]
  | cons b l ih => simp only [List.cons_append, base128, ih, List.length_cons, pow_succ]; ring

theorem base128_lt (l : List U8) : base128 l < 128 ^ l.length := by
  induction l with
  | nil => simp [base128]
  | cons b l ih => simp only [base128, List.length_cons, pow_succ]; omega

theorem take_succ_of_drop {α : Type} (bs : List α) (i : Nat) (c : α) (rest : List α)
    (hd : bs.drop i = c :: rest) :
    bs.take (i + 1) = bs.take i ++ [c] ∧ bs.drop (i + 1) = rest ∧ i < bs.length := by
  have hil : i < bs.length := by
    have : (bs.drop i).length > 0 := by rw [hd]; simp
    simp at this; omega
  have hlen : (bs.take i).length = i := by simp; omega
  have hbs : bs = bs.take i ++ c :: rest := by rw [← hd, List.take_append_drop]
  refine ⟨?_, ?_, hil⟩
  · conv_lhs => rw [hbs]
    rw [List.take_append, hlen, List.take_of_length_le (by omega)]
    simp
  · rw [← List.drop_drop, hd]; simp

theorem jsonbVarLenRead_none (bs : List U8) (i : Nat) (hall : ∀ c ∈ bs.take i, 128 ≤ c.val)
    (h : bs.take 5 = bs.take i) : jsonbVarLenRead bs = (none, bs.drop 5) := by
  unfold jsonbVarLenRead
  rw [h]
  have : (bs.take i).findIdx? (fun b => decide (b.val < 128)) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro x hx; have := hall x hx; simp; omega
  rw [this]

theorem jsonbVarLenRead_some (bs : List U8) (i : Nat) (hi : i < 5) (hall : ∀ c ∈ bs.take i, 128 ≤ c.val)
    (c : U8) (rest : List U8) (hd : bs.drop i = c :: rest) (hc : c.val < 128) :
    jsonbVarLenRead bs =
      (if base128 (bs.take i) + 128 ^ i * (c.val % 128) < 2 ^ 32
        then some (base128 (bs.take i) + 128 ^ i * (c.val % 128)) else none, rest) := by
  have hil : i < bs.length := by
    have : (bs.drop i).length > 0 := by rw [hd]; simp
    simp at this; omega
  have hlen : (bs.take i).length = i := by simp; omega
  have hbs : bs = bs.take i ++ c :: rest := by rw [← hd, List.take_append_drop]
  unfold jsonbVarLenRead
  have h5 : bs.take 5 = bs.take i ++ c :: rest.take (4 - i) := by
    conv_lhs => rw [hbs]
    rw [List.take_append, hlen, List.take_of_length_le (by omega)]
    congr 1
    rw [show 5 - i = (4 - i) + 1 by omega]; rfl
  have hn : (bs.take i).findIdx? (fun b => decide (b.val < 128)) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro x hx; have := hall x hx; simp; omega
  rw [h5, List.findIdx?_append, hn, List.findIdx?_cons]
  simp only [hc, decide_true, Option.none_or, ↓reduceIte, Option.map_some, zero_add, hlen]
  have ht : bs.take (i + 1) = bs.take i ++ [c] := by
    conv_lhs => rw [hbs]
    rw [List.take_append, hlen, List.take_of_length_le (by omega)]
    simp
  have hdr : bs.drop (i + 1) = rest := by
    rw [← List.drop_drop, hd]; simp
  rw [ht, hdr, base128_append, hlen]

theorem varlen_or (c len i : Nat) (hi : i < 5) (hlen : len < 128 ^ i) :
    (len ||| (c % 128) <<< (7 * i) % 2 ^ 64) = len + 128 ^ i * (c % 128) := by
  have hp : (128 : Nat) ^ i = 2 ^ (7 * i) := by rw [pow_mul]; norm_num
  have hc : c % 128 < 2 ^ 7 := by omega
  have hsmall : (c % 128) <<< (7 * i) < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    calc c % 128 * 2 ^ (7 * i) < 2 ^ 7 * 2 ^ (7 * i) := by
          apply Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ = 2 ^ (7 + 7 * i) := by rw [pow_add]
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.mod_eq_of_lt hsmall, Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by rw [← hp]; exact hlen),
    Nat.shiftLeft_eq, hp]
  ring

theorem and127 (c : Nat) : c &&& 127 = c % 128 := by
  rw [show (127 : Nat) = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem and128 (c : Nat) (hc : c < 256) : (c &&& 128 = 0 ↔ c < 128) := by
  rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.and_two_pow, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : c < 128
  · have : c / 128 % 2 = 0 := by omega
    simp [this, h]
  · have : c / 128 % 2 = 1 := by omega
    simp [this, h]

/-! ## Serialization-library varlen -/

theorem varlen_tb (n k i : Nat) (hk1 : 1 ≤ k) (hi : i < k) (hi8 : i < 8) :
    ((n * 2 ^ k + (2 ^ (k - 1) - 1)) % 256).testBit i = decide (i < k - 1) := by
  have hb : 2 ^ (k - 1) - 1 < 2 ^ k := by
    have : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have := Nat.one_le_two_pow (n := k - 1)
    omega
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, mul_comm,
    Nat.testBit_two_pow_mul_add n hb]
  simp [hi, hi8]

theorem varlen_trailingOnes (n k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 8) :
    trailingOnes (byte (n * 2 ^ k + (2 ^ (k - 1) - 1))) = k - 1 := by
  unfold trailingOnes
  rw [PBUtil.byte_val]
  have h := fun i => varlen_tb n k i hk1
  generalize (n * 2 ^ k + (2 ^ (k - 1) - 1)) % 256 = m at h
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  all_goals simp [List.range, List.range.loop, List.takeWhile, h]

theorem varlenUintSize_eq (n : Nat) : varlenUintSize n = if n < 128 then 1 else if n < 16384 then 2
    else if n < 2097152 then 3 else if n < 268435456 then 4 else if n < 34359738368 then 5
    else if n < 4398046511104 then 6 else if n < 562949953421312 then 7
    else if n < 72057594037927936 then 8 else 9 := by
  simp only [varlenUintSize, List.range', List.find?]
  norm_num
  split_ifs <;> simp [*]

theorem varlenUintSize_spec (n : Nat) :
    1 ≤ varlenUintSize n ∧ varlenUintSize n ≤ 9 ∧
    (varlenUintSize n ≤ 8 → n < 2 ^ (7 * varlenUintSize n)) ∧
    (varlenUintSize n = 9 → 2 ^ 56 ≤ n) := by
  rw [varlenUintSize_eq]
  split_ifs <;> norm_num <;> omega

theorem trailingOnes_255 : trailingOnes (byte 0xFF) = 8 := by
  unfold trailingOnes; rw [PBUtil.byte_val]
  simp [List.range, List.range.loop, List.takeWhile]
  decide

theorem varlenUintDecode_varlenUint' (n : Nat) (t : List U8) (hn : n < 2 ^ 64) :
    varlenUintDecode (varlenUint n ++ t) = some (n, t) := by
  obtain ⟨h1, h9, hlt, hge⟩ := varlenUintSize_spec n
  unfold varlenUint
  generalize hk : varlenUintSize n = k at *
  simp only
  split_ifs with hk9
  · subst hk9
    simp only [List.cons_append, varlenUintDecode, trailingOnes_255, ↓reduceIte]
    exact PBUtil.readLE_leBytes 8 n t hn
  · have hk8 : k ≤ 8 := by omega
    have hn7 := hlt hk8
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have htr := varlen_trailingOnes n (k' + 1) (by omega) hk8
    simp only [Nat.add_sub_cancel] at htr ⊢
    have hp1 := Nat.one_le_two_pow (n := k')
    have hpk : (2 : Nat) ^ (k' + 1) = 2 * 2 ^ k' := by rw [pow_succ]; ring
    have e2 : 2 ^ k' - 1 < 2 ^ (k' + 1) := by omega
    have hm : n * 2 ^ (k' + 1) + (2 ^ k' - 1) < 2 ^ (8 * (k' + 1)) := by
      have e1 : (2 : Nat) ^ (8 * (k' + 1)) = 2 ^ (7 * (k' + 1)) * 2 ^ (k' + 1) := by
        rw [← pow_add]; congr 1; ring
      have : n * 2 ^ (k' + 1) + 2 ^ (k' + 1) ≤ 2 ^ (7 * (k' + 1)) * 2 ^ (k' + 1) := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hn7
      omega
    generalize hM : n * 2 ^ (k' + 1) + (2 ^ k' - 1) = M at *
    have hlen := PBUtil.length_leBytes (k' + 1) M
    obtain ⟨ht, hd⟩ := leBytes_take_drop (k' + 1) M t
    have hcons : leBytes (k' + 1) M ++ t = byte M :: (leBytes k' (M / 256) ++ t) := rfl
    rw [hcons] at ht hd
    rw [hcons]
    simp only [varlenUintDecode, htr, show k' ≠ 8 by omega, ↓reduceIte]
    rw [← hcons]
    simp only [List.length_append, hlen, Nat.le_add_right, ↓reduceIte]
    rw [← hcons] at ht hd
    rw [ht, hd, PBUtil.leNat_leBytes, Nat.mod_eq_of_lt hm, ← hM]
    congr 2
    rw [Nat.add_div_of_dvd_right (Dvd.intro_left _ rfl), Nat.mul_div_cancel _ (by positivity),
      Nat.div_eq_of_lt e2]
    simp

theorem varlenUint_length' (n : Nat) : (varlenUint n).length = varlenUintSize n := by
  unfold varlenUint
  dsimp only
  split_ifs with h
  · simp [h]
  · simp

theorem trailingOnes_eq (b : U8) (t : Nat) (ht : t ≤ 8) (hall : ∀ j < t, b.val.testBit j = true)
    (hstop : t < 8 → b.val.testBit t = false) : trailingOnes b = t := by
  unfold trailingOnes
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 := by omega
  all_goals simp [List.range, List.range.loop, List.takeWhile, hall, hstop]

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

/-- `parse::<RawInt<T>>` for a fixed-size `T` (`SIZE = Some n`) whose `deserialize` reads a value
determined by the first `n` bytes: the shape of every `parse_rawint_spec` in `Misc/Raw/Int`. -/
theorem parse_rawint_take {T P β : Type} (inst : misc.raw.int.IntRepr T P) (n : Usize) (k : Nat)
    (hs : inst.SIZE = ok (some n)) (hk : n.val = k) (g : P → β) (F : List U8 → β)
    (hd : ∀ sub : io.ParseBuf, k ≤ sub.length → inst.deserialize sub ⦃ r rest =>
      (okPart r).map g = some (F (sub.val.take k)) ∧ rest.val = sub.val.drop k ⦄)
    (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple inst) buf () ⦃ r rest =>
      if k ≤ buf.length then
        (okPart r).map (fun x => g x.1) = some (F (buf.val.take k)) ∧ rest.val = buf.val.drop k
      else okPart r = none ∧ rest = buf ⦄ := by
  subst hk
  have := parse_rawint inst n hs buf (fun o => o.map g = some (F (buf.val.take n.val))) (by
    intro sub hsub hl
    apply spec_mono (hd sub (by simp [Slice.length, hsub]; omega))
    rintro ⟨r, rest⟩ ⟨h1, _⟩
    simpa [hsub, List.take_take] using h1)
  apply spec_mono this
  rintro ⟨r, rest⟩ h1
  simpa [Option.map_map] using h1

/-- Round trip for a fixed-size `RawInt<T>` from its `parse_rawint_spec` (`parse_rawint_take`): on
`enc ++ tail` with `enc` of exactly `n` bytes, `parse` returns `y = F enc` and leaves `tail`. -/
theorem rawint_roundtrip {T P β : Type} (inst : misc.raw.int.IntRepr T P) (n : Nat) (g : P → β)
    (F : List U8 → β) (buf : io.ParseBuf)
    (hp : io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple inst) buf () ⦃ r rest =>
      if n ≤ buf.length then
        (okPart r).map (fun x => g x.1) = some (F (buf.val.take n)) ∧ rest.val = buf.val.drop n
      else okPart r = none ∧ rest = buf ⦄)
    (enc tail : List U8) (hlen : enc.length = n) (h : buf.val = enc ++ tail) (y : β) (hy : F enc = y) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple inst) buf () ⦃ r rest =>
      (okPart r).map (fun x => g x.1) = some y ∧ rest.val = tail ⦄ := by
  apply spec_mono hp
  rintro ⟨r, rest⟩ hr
  have hl : n ≤ buf.length := by simp [Slice.length, h, hlen]
  subst hlen hy
  simpa [hl, h] using hr

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

@[step]
theorem min_usize_spec (x y : Usize) :
    core.cmp.min core.cmp.OrdUsize x y ⦃ r => r.val = min x.val y.val ⦄ := by
  simp [core.cmp.min]

theorem usize_pow_ge : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
  apply Nat.pow_le_pow_right (by norm_num)
  simp only [UScalarTy.numBits]; cases System.Platform.numBits_eq <;> simp [*]

theorem cast_usize_small {ty : UScalarTy} (x : UScalar ty) (h : x.val < 2 ^ 32) :
    (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (lt_of_lt_of_le h usize_pow_ge)

/-! ## Errors -/

@[step]
theorem io_error_from_spec {E : Type} (inst : core.error.Error E) (kind : core.io.error.ErrorKind) (err : E) :
    misc.io_error_from inst kind err ⦃ _ => True ⦄ := by
  simp [misc.io_error_from]

@[step]
theorem io_error_msg_spec (kind : core.io.error.ErrorKind) (msg : Str) :
    misc.io_error_msg kind msg ⦃ _ => True ⦄ := by
  simp [misc.io_error_msg]

@[step]
theorem unexpected_buf_eof_spec : misc.unexpected_buf_eof ⦃ _ => True ⦄ := by
  simp [misc.unexpected_buf_eof, misc.io_error_msg]

end IntAndMisc
