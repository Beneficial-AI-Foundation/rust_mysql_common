import Defs

/-! Helper lemmas for the `ParseBuf` proofs (`Proofs/Io/ParseBuf.lean`,
`Proofs/Misc/Raw/ParseBuf.lean`): byte-order arithmetic and step lemmas for the internal
building blocks of `impl ParseBuf`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.PBUtil

/-! ## Byte-order arithmetic -/

theorem leNat_lt (l : List U8) : leNat l < 2 ^ (8 * l.length) := by
  induction l with
  | nil => simp [leNat]
  | cons b l ih =>
    have hb : b.val < 256 := by have := b.hBounds; simpa using this
    simp only [leNat, List.length_cons]
    rw [show 8 * (l.length + 1) = 8 * l.length + 8 by ring, pow_add]
    have : leNat l + 1 ≤ 2 ^ (8 * l.length) := ih
    nlinarith

theorem fromLEBytes_toNat (l : List U8) :
    (BitVec.fromLEBytes (l.map U8.bv)).toNat = leNat l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb : b.val < 256 := by have := b.hBounds; simpa using this
    have hl := leNat_lt l
    rw [List.map_cons, BitVec.fromLEBytes]
    simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, ih, List.length_cons,
      List.length_map, leNat]
    have hP : 2 ^ (8 * (l.length + 1)) = 2 ^ (8 * l.length) * 256 := by
      rw [show 8 * (l.length + 1) = 8 * l.length + 8 by ring, pow_add]; norm_num
    have hbv : b.bv.toNat = b.val := rfl
    have h1 : leNat l % 2 ^ (8 * (l.length + 1)) = leNat l := Nat.mod_eq_of_lt (by rw [hP]; omega)
    have hpos : 0 < 2 ^ (8 * l.length) := by positivity
    have h2 : b.val % 2 ^ (8 * (l.length + 1)) = b.val := Nat.mod_eq_of_lt (by rw [hP]; nlinarith)
    have h3 : (leNat l <<< 8) % 2 ^ (8 * (l.length + 1)) = leNat l <<< 8 := by
      apply Nat.mod_eq_of_lt; rw [Nat.shiftLeft_eq, hP]; omega
    rw [hbv, h1, h2, h3, Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : b.val < 2 ^ 8), Nat.shiftLeft_eq]
    ring


theorem fromLEBytes_cast_toNat {w : Nat} (l : List U8) (h : 8 * (l.map U8.bv).length = w) :
    ((BitVec.fromLEBytes (l.map U8.bv)).cast h).toNat = leNat l := by
  rw [BitVec.toNat_cast, fromLEBytes_toNat]

theorem fromBEBytes_cast_toNat {w : Nat} (l : List U8) (h : 8 * (l.map U8.bv).length = w) :
    ((BitVec.fromBEBytes (l.map U8.bv)).cast h).toNat = beNat l := by
  rw [BitVec.toNat_cast, BitVec.fromBEBytes, BitVec.toNat_cast, ← List.map_reverse, fromLEBytes_toNat]
  rfl

theorem toInt_eq_toSigned {w : Nat} (x : BitVec w) (hw : 0 < w) : x.toInt = toSigned w x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond, toSigned]
  have : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']; congr 1; omega
  split_ifs <;> first | rfl | omega

theorem leNat_append_zeros (l : List U8) (k : Nat) : leNat (l ++ List.replicate k 0#u8) = leNat l := by
  induction l with
  | nil =>
    simp only [List.nil_append, leNat]
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, leNat, ih]
  | cons b l ih => simp [leNat, ih]

theorem beNat_zeros_append (l : List U8) (k : Nat) : beNat (List.replicate k 0#u8 ++ l) = beNat l := by
  simp [beNat, List.reverse_append, leNat_append_zeros]

theorem setSlice!_replicate {α : Type} (n i : Nat) (z : α) (l : List α) (h : i + l.length ≤ n) :
    (List.replicate n z).setSlice! i l = List.replicate i z ++ l ++ List.replicate (n - i - l.length) z := by
  simp only [List.setSlice!, List.take_replicate, List.length_replicate, List.drop_replicate]
  have h1 : min i n = i := by omega
  have h2 : min l.length (n - i) = l.length := by omega
  rw [h1, h2, List.take_of_length_le (le_refl _)]
  congr 2; omega

theorem padded_be (n i : Nat) (l : List U8) (h : i + l.length = n) :
    beNat ((List.replicate n 0#u8).setSlice! i l) = beNat l := by
  rw [setSlice!_replicate _ _ _ _ (by omega), show n - i - l.length = 0 by omega]
  simp [beNat_zeros_append]

theorem padded_le (n : Nat) (l : List U8) (h : l.length ≤ n) :
    leNat ((List.replicate n 0#u8).setSlice! 0 l) = leNat l := by
  rw [setSlice!_replicate _ _ _ _ (by omega)]
  simp [leNat_append_zeros]

theorem toSigned_of_lt (w n : Nat) (h : n < 2 ^ (w - 1)) : toSigned w n = n := by
  simp [toSigned, h]

theorem toSigned_leNat_small (w : Nat) (l : List U8) (h : 8 * l.length < w) :
    toSigned w (leNat l) = leNat l := by
  apply toSigned_of_lt
  have := leNat_lt l
  have : 2 ^ (8 * l.length) ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem toSigned_beNat_small (w : Nat) (l : List U8) (h : 8 * l.length < w) :
    toSigned w (beNat l) = beNat l :=
  toSigned_leNat_small w l.reverse (by simpa using h)


/-! ## Buffers -/

theorem from_slice_take_val {n : Usize} (a : Std.Array U8 n) (bytes : Slice U8) (buf : List U8) (k : Nat)
    (hb : bytes.val = buf.take k) (hk : k ≤ buf.length) (hn : n.val = k) :
    (a.from_slice bytes).val = buf.take k := by
  rw [Array.from_slice_val _ _ (by simp [hb]; omega), hb]

theorem padded_take_le (n : Nat) (buf : List U8) (k : Nat) (hk : k ≤ n) :
    leNat ((List.replicate n 0#u8).setSlice! 0 (buf.take k)) = leNat (buf.take k) :=
  padded_le _ _ (by simp; omega)

theorem padded_take_be (n i : Nat) (buf : List U8) (k : Nat) (hk : k ≤ buf.length) (hn : i + k = n) :
    beNat ((List.replicate n 0#u8).setSlice! i (buf.take k)) = beNat (buf.take k) :=
  padded_be _ _ _ (by simp; omega)


/-! ## Results and specs -/

theorem val_mk {ty : UScalarTy} (b : BitVec ty.numBits) : (UScalar.mk b : UScalar ty).val = b.toNat := rfl

theorem spec_eq_ok {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) : ∃ v, m = ok v ∧ P v := by
  cases m <;> simp_all

/-- A program fails if its first step succeeds and every continuation allowed by its spec fails. -/
theorem not_spec_bind {α β : Type} {m : Result α} {k : α → Result β} {P : α → Prop} (hm : m ⦃ P ⦄)
    (hk : ∀ x, P x → ¬ (k x) ⦃ _ => True ⦄) : ¬ (Std.bind m k) ⦃ _ => True ⦄ := by
  obtain ⟨v, rfl, hv⟩ := spec_eq_ok hm
  simpa using hk v hv

/-- A program fails if its first step fails. -/
theorem not_spec_bind_left {α β : Type} {m : Result α} {k : α → Result β} {P : β → Prop}
    (hm : ¬ m ⦃ _ => True ⦄) : ¬ (Std.bind m k) ⦃ P ⦄ := by
  cases m <;> simp_all

/-! ## Step lemmas for the building blocks -/

@[step]
theorem len_ok (buf : io.ParseBuf) :
    io.ParseBuf.len buf ⦃ n => n.val = buf.length ⦄ := by
  unfold io.ParseBuf.len; step*

@[step]
theorem eat_ok (buf : io.ParseBuf) (n : Usize) (h : n.val ≤ buf.length) :
    io.ParseBuf.eat buf n ⦃ s rest => s.val = buf.val.take n.val ∧ rest.val = buf.val.drop n.val ⦄ := by
  unfold io.ParseBuf.eat
  step*

theorem eat_fail (buf : io.ParseBuf) (n : Usize) (h : buf.length < n.val) :
    ¬ io.ParseBuf.eat buf n ⦃ _ => True ⦄ := by
  unfold io.ParseBuf.eat core.slice.Slice.split_at
  simp [show ¬ n.val ≤ buf.length by omega]

@[step]
theorem checked_eat_ok (buf : io.ParseBuf) (n : Usize) :
    io.ParseBuf.checked_eat buf n ⦃ o rest =>
      if n.val ≤ buf.length then
        o.map (·.val) = some (buf.val.take n.val) ∧ rest.val = buf.val.drop n.val
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat
  step*
  all_goals split_ifs <;> simp_all

@[step]
theorem checked_eat_buf_ok (buf : io.ParseBuf) (n : Usize) :
    io.ParseBuf.checked_eat_buf buf n ⦃ o rest =>
      if n.val ≤ buf.length then
        o.map (·.val) = some (buf.val.take n.val) ∧ rest.val = buf.val.drop n.val
      else o = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.checked_eat_buf
  step*
  all_goals simp_all

@[step]
theorem deserialize_usize_ok (len : Usize) (buf : io.ParseBuf) :
    io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize len buf ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map (·.val) = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄ := by
  unfold io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize misc.unexpected_buf_eof
    misc.io_error_msg
  step*
  all_goals split_ifs at * <;> simp_all [okPart]

/-! ## Length-encoded integers, `position_of_zero` -/

theorem cast_usize_64 (h64 : Target64) (x : U64) : (UScalar.cast .Usize x).val = x.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [Target64] at h64; simp [h64])

theorem byte_val (n : Nat) : (byte n).val = n % 256 := by
  simp [byte, UScalar.val]

theorem length_leBytes (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem leNat_leBytes (k n : Nat) : leNat (leBytes k n) = n % 2 ^ (8 * k) := by
  induction k generalizing n with
  | zero => simp [leBytes, leNat, Nat.mod_one]
  | succ k ih =>
    simp only [leBytes, leNat, ih, byte_val]
    rw [show 8 * (k + 1) = 8 + 8 * k by ring, pow_add, Nat.mod_mul]
    norm_num

theorem readLE_leBytes (k n : Nat) (t : List U8) (hn : n < 2 ^ (8 * k)) :
    readLE k (leBytes k n ++ t) = some (n, t) := by
  have hl := length_leBytes k n
  simp [readLE, hl, leNat_leBytes,
    Nat.mod_eq_of_lt hn]

theorem checkedLenencInt_lenencInt (n : Nat) (t : List U8) (hn : n < 2 ^ 64) :
    checkedLenencInt (lenencInt n ++ t) = (some n, t) := by
  unfold lenencInt
  split_ifs with h1 h2 h3
  · simp [checkedLenencInt, lenencIntDecode, byte_val, Nat.mod_eq_of_lt (by omega : n < 256)]
    rw [ite_eq_right (by omega), ite_eq_left h1]
  · simp [checkedLenencInt, lenencIntDecode, byte_val, readLE_leBytes 2 n t (by omega)]
  · simp [checkedLenencInt, lenencIntDecode, byte_val, readLE_leBytes 3 n t (by omega)]
  · simp [checkedLenencInt, lenencIntDecode, byte_val, readLE_leBytes 8 n t (by omega)]

@[step]

theorem position_of_zero_ok (s : Slice U8) :
    io.position_of_zero s ⦃ r => match r with
      | some i => i.val < s.length ∧ (∀ b ∈ s.val.take i.val, b.val ≠ 0) ∧ (s.val[i.val]!).val = 0
      | none => ∀ b ∈ s.val, b.val ≠ 0 ⦄ := by
  unfold io.position_of_zero io.position_of_zero_loop
  apply loop.spec_decr_nat (fun i => s.length - i.val)
    (fun i => i.val ≤ s.length ∧ ∀ b ∈ s.val.take i.val, b.val ≠ 0)
  · rintro i ⟨hi, hall⟩
    unfold io.position_of_zero_loop.body
    step*
    · have hlt : i.val < s.length := by scalar_tac
      refine ⟨hlt, hall, ?_⟩
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [Slice.length] using hlt)]
      simp only [Option.getD_some, ← i2_post]
      have h0 : i2 = 0#u8 := by assumption
      rw [h0]; rfl
    · have hlt : i.val < s.length := by scalar_tac
      refine ⟨by omega, ?_, by omega⟩
      rw [i3_post, List.take_add_one, List.getElem?_eq_getElem (by simpa [Slice.length] using hlt)]
      intro b hb
      simp only [List.mem_append, Option.toList_some, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact hall b hb
      · rw [← i2_post]; intro h0; apply ‹¬i2 = 0#u8›; simp [UScalar.eq_equiv, h0]
    · have : i.val = s.length := by scalar_tac
      rw [this, Slice.length, List.take_length] at hall
      exact hall
  · simp

theorem beforeZero_of_all (l : List U8) (h : ∀ b ∈ l, b.val ≠ 0) : beforeZero l = l := by
  unfold beforeZero
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.takeWhile_cons, ite_eq_left (by simpa using h b (by simp))]
    rw [ih (fun x hx => h x (by simp [hx]))]

theorem beforeZero_of_zero (l : List U8) (i : Nat) (hi : i < l.length) (hall : ∀ b ∈ l.take i, b.val ≠ 0)
    (h0 : (l[i]!).val = 0) : beforeZero l = l.take i := by
  unfold beforeZero
  conv => lhs; rw [← List.take_append_drop i l]
  rw [List.takeWhile_append_of_pos (by simpa using hall)]
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h0
  rw [List.drop_eq_getElem_cons hi, List.takeWhile_cons, ite_eq_right (by simp [h0])]
  simp

/-! ## Tactics for the fixed-width readers -/

macro "pb_finish" : tactic => `(tactic| (
  refine ⟨?_, by assumption⟩
  subst_vars
  simp only [← UScalar.bv_toNat, ← IScalar.bv_toInt_eq, core.num.U32.from_le_bytes, core.num.U32.from_be_bytes,
    core.num.U64.from_le_bytes, core.num.U64.from_be_bytes, *]
  try rw [toInt_eq_toSigned _ (by decide)]
  first | rw [fromLEBytes_cast_toNat] | rw [fromBEBytes_cast_toNat]
  try simp only [*, Array.repeat_val, IScalarTy.I8_numBits_eq, IScalarTy.I16_numBits_eq, IScalarTy.I32_numBits_eq,
    IScalarTy.I64_numBits_eq, IScalarTy.I128_numBits_eq]
  first
    | rw [from_slice_take_val _ _ _ _ (by assumption) (by scalar_tac) (by rfl)]
    | rw [padded_take_le _ _ _ (by decide)]
    | rw [padded_take_be _ _ _ _ (by scalar_tac) (by decide)]
  try first
    | rw [toSigned_leNat_small _ _ (by simp; omega)]
    | rw [toSigned_beNat_small _ _ (by simp; omega)]))

end mysql_common.PBUtil
