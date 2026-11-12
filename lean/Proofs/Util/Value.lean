import Defs
import Proofs.Io.ParseBuf
import Proofs.Io.BufMutExt
import Proofs.Misc.LenencStrLen
import Proofs.Misc.Raw.Bytes.LenEnc
import Proofs.Misc.Raw.Bytes.RawBytes
set_option autoImplicit false
set_option linter.auxLemma false
open Aeneas Aeneas.Std Result mysql_common Defs
/-! Helper lemmas for the proofs of the `Value` group (`Proofs/Value/*.lean`). -/

namespace mysql_common.ValueUtil

open mysql_common

theorem leBytes_mod (k n : Nat) : leBytes k (n % 2 ^ (8 * k)) = leBytes k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 ^ (8 * (k+1)) = 256 * 2 ^ (8 * k) := by rw [Nat.mul_succ, Nat.pow_add]; omega
    simp only [leBytes]
    congr 1
    · simp only [byte]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      rw [h2, Nat.mod_mul_right_mod]
    · rw [h2, Nat.mod_mul_right_div_self, ih]

theorem toLEBytes_leBytes : ∀ (w : Nat) (b : BitVec w), w % 8 = 0 →
    (b.toLEBytes.map (@UScalar.mk UScalarTy.U8)) = leBytes (w / 8) b.toNat
  | 0, b, _ => by simp [BitVec.toLEBytes, leBytes]
  | w + 1, b, hw => by
    rw [BitVec.toLEBytes]
    have hk : (w + 1) / 8 = (w + 1 - 8) / 8 + 1 := by omega
    simp only [show w + 1 > 0 by omega, ite_true, List.map_cons, hk, leBytes]
    congr 1
    · simp only [byte]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp
    · rw [toLEBytes_leBytes (w + 1 - 8) _ (by omega)]
      rw [← leBytes_mod _ (b.toNat / 256)]
      congr 1
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
      congr 2 <;> omega

theorem put_slice_spec (buf : alloc.vec.Vec U8) (s : Slice U8)
    (h : buf.length + s.length ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_slice buf s ⦃ b => b.val = buf.val ++ s.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_slice alloc.vec.Vec.extend_from_slice
  rw [dite_eq_left h]
  step with List.clone_spec
  simp_all

theorem put_u8_spec (buf : alloc.vec.Vec U8) (n : U8)
    (h : buf.length + 1 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u8 buf n ⦃ b => b.val = buf.val ++ [n] ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u8
  simp only [lift, Std.bind_ok]
  apply WP.spec_mono (put_slice_spec _ _ (by simpa [Array.to_slice] using h))
  intro b hb; simpa [Array.to_slice] using hb

theorem put_u16_le_spec (buf : alloc.vec.Vec U8) (n : U16)
    (h : buf.length + 2 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u16_le buf n ⦃ b => b.val = buf.val ++ leBytes 2 n.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u16_le
  simp only [lift, Std.bind_ok]
  apply WP.spec_mono (put_slice_spec _ _ (by simpa [Array.to_slice, core.num.U16.to_le_bytes] using h))
  intro b hb
  simp [Array.to_slice, core.num.U16.to_le_bytes] at hb
  rw [hb]
  have := toLEBytes_leBytes 16 n.bv rfl
  simpa using this

theorem put_u32_le_spec (buf : alloc.vec.Vec U8) (n : U32)
    (h : buf.length + 4 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u32_le buf n ⦃ b => b.val = buf.val ++ leBytes 4 n.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u32_le
  simp only [lift, Std.bind_ok]
  apply WP.spec_mono (put_slice_spec _ _ (by simpa [Array.to_slice, core.num.U32.to_le_bytes] using h))
  intro b hb
  simp [Array.to_slice, core.num.U32.to_le_bytes] at hb
  rw [hb]
  have := toLEBytes_leBytes 32 n.bv rfl
  simpa using this

theorem put_u64_le_spec (buf : alloc.vec.Vec U8) (n : U64)
    (h : buf.length + 8 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u64_le buf n ⦃ b => b.val = buf.val ++ leBytes 8 n.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_u64_le
  simp only [lift, Std.bind_ok]
  apply WP.spec_mono (put_slice_spec _ _ (by simpa [Array.to_slice, core.num.U64.to_le_bytes] using h))
  intro b hb
  simp [Array.to_slice, core.num.U64.to_le_bytes] at hb
  rw [hb]
  have := toLEBytes_leBytes 64 n.bv rfl
  simpa using this

theorem toInt_emod_toNat {w : Nat} (b : BitVec w) : (b.toInt % (2 ^ w : Int)).toNat = b.toNat := by
  rw [BitVec.toInt_eq_toNat_bmod, show (2:Int)^w = ((2^w : Nat) : Int) by simp, Int.bmod_emod]
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast b.isLt)]
  simp

theorem put_i64_le_spec (buf : alloc.vec.Vec U8) (n : I64)
    (h : buf.length + 8 ≤ Usize.max) :
    alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_i64_le buf n ⦃ b => b.val = buf.val ++ leBytesI 8 n.val ⦄ := by
  unfold alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_i64_le
  simp only [lift, Std.bind_ok]
  apply WP.spec_mono (put_slice_spec _ _ (by simpa [Array.to_slice, core.num.I64.to_le_bytes] using h))
  intro b hb
  simp [Array.to_slice, core.num.I64.to_le_bytes] at hb
  rw [hb]
  have := toLEBytes_leBytes 64 n.bv rfl
  simp at this
  rw [this, leBytesI, ← IScalar.bv_toInt_eq]
  have := toInt_emod_toNat n.bv
  simp at this
  simp [this]

attribute [step] put_u8_spec put_u16_le_spec put_u32_le_spec put_u64_le_spec put_i64_le_spec

theorem length_leBytes' (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n <;> simp_all [leBytes]

@[simp] theorem byte_val (x : U8) : byte x.val = x := by
  simp [byte]

theorem m6 {β : Type} (x : U8) (f : Unit → β) (g : U8 → β) :
    value.Value.bin_len.match_6 (fun _ => β) x f g = if x = 0#u8 then f () else g x := by
  by_cases hx : x = 0#u8
  · subst hx; rfl
  · rw [value.Value.bin_len.match_6.eq_2 _ _ _ _ hx]; simp [hx]

theorem m4 {β : Type} (x : U16) (f : Unit → β) (g : U16 → β) :
    value.Value.bin_len.match_4 (fun _ => β) x f g = if x = 0#u16 then f () else g x := by
  by_cases hx : x = 0#u16
  · subst hx; rfl
  · rw [value.Value.bin_len.match_4.eq_2 _ _ _ _ hx]; simp [hx]

theorem m8 {β : Type} (x : U32) (f : Unit → β) (g : U32 → β) :
    value.Value.bin_len.match_8 (fun _ => β) x f g = if x = 0#u32 then f () else g x := by
  by_cases hx : x = 0#u32
  · subst hx; rfl
  · rw [value.Value.bin_len.match_8.eq_2 _ _ _ _ hx]; simp [hx]

theorem u8_val_eq_zero (x : U8) : x.val = 0 ↔ x = 0#u8 := by
  constructor
  · intro h; apply UScalar.eq_of_val_eq; simpa using h
  · rintro rfl; rfl
theorem u16_val_eq_zero (x : U16) : x.val = 0 ↔ x = 0#u16 := by
  constructor
  · intro h; apply UScalar.eq_of_val_eq; simpa using h
  · rintro rfl; rfl
theorem u32_val_eq_zero (x : U32) : x.val = 0 ↔ x = 0#u32 := by
  constructor
  · intro h; apply UScalar.eq_of_val_eq; simpa using h
  · rintro rfl; rfl

open alloc.vec.VecU8.Insts.Mysql_commonIoBufMut in
set_option maxHeartbeats 10000000 in
theorem serialize_date_eq (y : U16) (mo d h mi s : U8) (us : U32) (buf : alloc.vec.Vec U8) :
    value.Value.Insts.Mysql_commonProtoMySerialize.serialize (.Date y mo d h mi s us) buf =
    if y = 0#u16 ∧ mo = 0#u8 ∧ d = 0#u8 ∧ h = 0#u8 ∧ mi = 0#u8 ∧ s = 0#u8 ∧ us = 0#u32 then
      put_u8 buf 0#u8
    else if h = 0#u8 ∧ mi = 0#u8 ∧ s = 0#u8 ∧ us = 0#u32 then do
      let b ← put_u8 buf 4#u8; let b ← put_u16_le b y; let b ← put_u8 b mo; put_u8 b d
    else if us = 0#u32 then do
      let b ← put_u8 buf 7#u8; let b ← put_u16_le b y; let b ← put_u8 b mo; let b ← put_u8 b d
      let b ← put_u8 b h; let b ← put_u8 b mi; put_u8 b s
    else (do
      let b ← put_u8 buf 11#u8; let b ← put_u16_le b y; let b ← put_u8 b mo; let b ← put_u8 b d
      let b ← put_u8 b h; let b ← put_u8 b mi; let b ← put_u8 b s; put_u32_le b us) := by
  unfold value.Value.Insts.Mysql_commonProtoMySerialize.serialize
  simp (maxSteps := 10000000) only [m4, m6, m8]
  obtain rfl | hy := eq_or_ne y 0#u16 <;>
  obtain rfl | hmo := eq_or_ne mo 0#u8 <;>
  obtain rfl | hd := eq_or_ne d 0#u8 <;>
  obtain rfl | hh := eq_or_ne h 0#u8 <;>
  obtain rfl | hmi := eq_or_ne mi 0#u8 <;>
  obtain rfl | hs := eq_or_ne s 0#u8 <;>
  obtain rfl | hus := eq_or_ne us 0#u32 <;>
  simp only [ite_true, ite_false, *, and_true, and_false, true_and, false_and]


theorem byte_lits : byte 0 = 0#u8 ∧ byte 1 = 1#u8 ∧ byte 4 = 4#u8 ∧ byte 7 = 7#u8 ∧ byte 8 = 8#u8 ∧ byte 11 = 11#u8 ∧ byte 12 = 12#u8 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem serialize_date_spec (y : U16) (mo d h mi s : U8) (us : U32) (buf : alloc.vec.Vec U8)
    (hb : buf.length + (binEnc (Val.ofValue (.Date y mo d h mi s us))).length ≤ Usize.max) :
    value.Value.Insts.Mysql_commonProtoMySerialize.serialize (.Date y mo d h mi s us) buf ⦃ buf' => buf'.val = buf.val ++ binEnc (Val.ofValue (.Date y mo d h mi s us)) ⦄ := by
  rw [serialize_date_eq]
  simp only [Val.ofValue, binEnc, u8_val_eq_zero, u16_val_eq_zero, u32_val_eq_zero] at hb ⊢
  split_ifs at hb ⊢
  all_goals
    simp only [List.length_cons, List.length_append, length_leBytes', List.length_nil, List.length_singleton] at hb
    step*
  all_goals first
    | (simp only [alloc.vec.Vec.length] at hb ⊢; simp only [*, List.length_append, List.length_cons, List.length_nil, length_leBytes', List.length_singleton] <;> omega)
    | (simp only [*, byte_lits, byte_val, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append])


macro "vec_len_tac" : tactic => `(tactic| (simp only [alloc.vec.Vec.length] at *; simp only [*, List.length_append, List.length_cons, List.length_nil, length_leBytes', List.length_singleton] <;> omega))

open alloc.vec.VecU8.Insts.Mysql_commonIoBufMut in
set_option maxHeartbeats 10000000 in
theorem serialize_time_eq (neg : Bool) (d : U32) (h m s : U8) (us : U32) (buf : alloc.vec.Vec U8) :
    value.Value.Insts.Mysql_commonProtoMySerialize.serialize (.Time neg d h m s us) buf =
    if d = 0#u32 ∧ h = 0#u8 ∧ m = 0#u8 ∧ s = 0#u8 ∧ us = 0#u32 then
      put_u8 buf 0#u8
    else if us = 0#u32 then do
      let b ← put_u8 buf 8#u8
      let b ← put_u8 b (if neg then 1#u8 else 0#u8)
      let b ← put_u32_le b d; let b ← put_u8 b h; let b ← put_u8 b m; put_u8 b s
    else (do
      let b ← put_u8 buf 12#u8
      let b ← put_u8 b (if neg then 1#u8 else 0#u8)
      let b ← put_u32_le b d; let b ← put_u8 b h; let b ← put_u8 b m; let b ← put_u8 b s
      put_u32_le b us) := by
  unfold value.Value.Insts.Mysql_commonProtoMySerialize.serialize
  simp (maxSteps := 10000000) only [m4, m6, m8]
  obtain rfl | hd := eq_or_ne d 0#u32 <;>
  obtain rfl | hh := eq_or_ne h 0#u8 <;>
  obtain rfl | hm := eq_or_ne m 0#u8 <;>
  obtain rfl | hs := eq_or_ne s 0#u8 <;>
  obtain rfl | hus := eq_or_ne us 0#u32 <;>
  cases neg <;>
  simp only [ite_true, ite_false, *, and_true, and_false, true_and, false_and, Bool.false_eq_true]

theorem serialize_time_spec (neg : Bool) (d : U32) (h m s : U8) (us : U32) (buf : alloc.vec.Vec U8)
    (hb : buf.length + (binEnc (Val.ofValue (.Time neg d h m s us))).length ≤ Usize.max) :
    value.Value.Insts.Mysql_commonProtoMySerialize.serialize (.Time neg d h m s us) buf ⦃ buf' => buf'.val = buf.val ++ binEnc (Val.ofValue (.Time neg d h m s us)) ⦄ := by
  rw [serialize_time_eq]
  simp only [Val.ofValue, binEnc, u8_val_eq_zero, u16_val_eq_zero, u32_val_eq_zero] at hb ⊢
  split_ifs at hb ⊢
  all_goals
    simp only [List.length_cons, List.length_append, length_leBytes', List.length_nil, List.length_singleton] at hb
    step*
  all_goals first
    | vec_len_tac
    | (cases neg <;> simp only [*, byte_lits, byte_val, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append, ite_true, ite_false, Bool.false_eq_true])


set_option maxHeartbeats 10000000 in
theorem bin_len_date_eq (y : U16) (mo d h mi s : U8) (us : U32) :
    value.Value.bin_len (.Date y mo d h mi s us) =
    if y = 0#u16 ∧ mo = 0#u8 ∧ d = 0#u8 ∧ h = 0#u8 ∧ mi = 0#u8 ∧ s = 0#u8 ∧ us = 0#u32 then ok 1#u64
    else if h = 0#u8 ∧ mi = 0#u8 ∧ s = 0#u8 ∧ us = 0#u32 then ok 5#u64
    else if us = 0#u32 then ok 8#u64 else ok 12#u64 := by
  unfold value.Value.bin_len
  simp (maxSteps := 10000000) only [m4, m6, m8]
  obtain rfl | hy := eq_or_ne y 0#u16 <;>
  obtain rfl | hmo := eq_or_ne mo 0#u8 <;>
  obtain rfl | hd := eq_or_ne d 0#u8 <;>
  obtain rfl | hh := eq_or_ne h 0#u8 <;>
  obtain rfl | hmi := eq_or_ne mi 0#u8 <;>
  obtain rfl | hs := eq_or_ne s 0#u8 <;>
  obtain rfl | hus := eq_or_ne us 0#u32 <;>
  simp only [ite_true, ite_false, *, and_true, and_false, true_and, false_and]

set_option maxHeartbeats 10000000 in
theorem bin_len_time_eq (neg : Bool) (d : U32) (h m s : U8) (us : U32) :
    value.Value.bin_len (.Time neg d h m s us) =
    if d = 0#u32 ∧ h = 0#u8 ∧ m = 0#u8 ∧ s = 0#u8 ∧ us = 0#u32 then ok 1#u64
    else if us = 0#u32 then ok 9#u64 else ok 13#u64 := by
  unfold value.Value.bin_len
  simp (maxSteps := 10000000) only [m4, m6, m8]
  obtain rfl | hd := eq_or_ne d 0#u32 <;>
  obtain rfl | hh := eq_or_ne h 0#u8 <;>
  obtain rfl | hm := eq_or_ne m 0#u8 <;>
  obtain rfl | hs := eq_or_ne s 0#u8 <;>
  obtain rfl | hus := eq_or_ne us 0#u32 <;>
  simp only [ite_true, ite_false, *, and_true, and_false, true_and, false_and]

@[simp] theorem deref_val (x : alloc.vec.Vec U8) : (alloc.vec.Vec.deref x).val = x.val := by
  simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]

theorem bin_len_spec' (v : value.Value)
    (h : (binEnc (Val.ofValue v)).length < 2 ^ 64) :
    value.Value.bin_len v ⦃ n => n.val = (binEnc (Val.ofValue v)).length ⦄ := by
  cases v with
  | Bytes x =>
    unfold value.Value.bin_len
    dsimp only
    simp only [Val.ofValue, binEnc] at h ⊢
    have := misc.lenenc_str_len_spec x.deref (by rw [deref_val]; exact h)
    rw [deref_val] at this
    exact this
  | Date y mo d hh mi s us =>
    rw [bin_len_date_eq]
    simp only [Val.ofValue, binEnc, u8_val_eq_zero, u16_val_eq_zero, u32_val_eq_zero]
    split_ifs <;> simp [length_leBytes']
  | Time neg d hh m s us =>
    rw [bin_len_time_eq]
    simp only [Val.ofValue, binEnc, u8_val_eq_zero, u16_val_eq_zero, u32_val_eq_zero]
    split_ifs <;> simp [length_leBytes']
  | _ => unfold value.Value.bin_len; simp [Val.ofValue, binEnc, length_leBytes', leBytesI]

theorem serialize_spec' (v : value.Value) (buf : alloc.vec.Vec U8)
    (h : buf.length + (binEnc (Val.ofValue v)).length ≤ Usize.max) :
    value.Value.Insts.Mysql_commonProtoMySerialize.serialize v buf ⦃ buf' => buf'.val = buf.val ++ binEnc (Val.ofValue v) ⦄ := by
  cases v with
  | Date y mo d hh mi s us => exact serialize_date_spec y mo d hh mi s us buf h
  | Time neg d hh m s us => exact serialize_time_spec neg d hh m s us buf h
  | NULL => unfold value.Value.Insts.Mysql_commonProtoMySerialize.serialize; simp [Val.ofValue, binEnc]
  | Bytes x =>
    unfold value.Value.Insts.Mysql_commonProtoMySerialize.serialize
    dsimp only
    simp only [Val.ofValue, binEnc] at h ⊢
    have := io.BufMutExt.put_lenenc_str_spec buf x.deref (by rw [deref_val]; exact h)
    rw [deref_val] at this
    exact this
  | Int x =>
    unfold value.Value.Insts.Mysql_commonProtoMySerialize.serialize
    simp only [Val.ofValue, binEnc] at h ⊢
    exact put_i64_le_spec _ _ (by simpa [leBytesI, length_leBytes'] using h)
  | UInt x =>
    unfold value.Value.Insts.Mysql_commonProtoMySerialize.serialize
    simp only [Val.ofValue, binEnc] at h ⊢
    exact put_u64_le_spec _ _ (by simpa [length_leBytes'] using h)
  | Float x =>
    unfold value.Value.Insts.Mysql_commonProtoMySerialize.serialize
      alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_f32_le core.f32.F32.to_bits
    simp only [Val.ofValue, binEnc, Std.bind_ok] at h ⊢
    exact put_u32_le_spec _ _ (by simpa [length_leBytes'] using h)
  | Double x =>
    unfold value.Value.Insts.Mysql_commonProtoMySerialize.serialize
      alloc.vec.VecU8.Insts.Mysql_commonIoBufMut.put_f64_le core.f64.F64.to_bits
    simp only [Val.ofValue, binEnc, Std.bind_ok] at h ⊢
    exact put_u64_le_spec _ _ (by simpa [length_leBytes'] using h)


theorem mtext {β : Type} (x : U8) (f : Unit → β) (g : U8 → β) :
    value.Value.deserialize_text.match_1 (fun _ => β) x f g = if x = 251#u8 then f () else g x := by
  by_cases hx : x = 251#u8
  · subst hx; rfl
  · rw [value.Value.deserialize_text.match_1.eq_2 _ _ _ _ hx]; simp [hx]

@[simp] theorem eof_ok : ∃ e, misc.unexpected_buf_eof = ok e := ⟨_, rfl⟩

theorem unexpected_buf_eof_spec : misc.unexpected_buf_eof ⦃ _ => True ⦄ := by
  simp [misc.unexpected_buf_eof, misc.io_error_msg]

@[simp] theorem from_residual_err {T : Type} (e : core.io.error.Error) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame core.io.error.Error) (.Err e) = ok (.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame]

theorem cow_into_vec_spec (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    misc.raw.cow_into_vec core.clone.CloneU8 c ⦃ v => v.val = cowList c ⦄ := by
  cases c with
  | Borrowed s =>
    unfold misc.raw.cow_into_vec
    simp only
    apply WP.spec_mono (alloc.slice.Slice.to_vec_spec _ s (by simp))
    intro v hv; simp [cowList, hv, alloc.vec.Vec.val]
  | Owned v => simp [misc.raw.cow_into_vec, cowList]

theorem rawbytes_lenenc_size :
    (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
      misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple).SIZE = ok none := by
  simp only [misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize,
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE,
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple]
  unfold misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE; rfl

theorem deserialize_text_spec' (h64 : Target64) (buf : io.ParseBuf) :
    value.Value.deserialize_text buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = textRead buf.val ⦄ := by
  unfold value.Value.deserialize_text
  step with io.ParseBuf.is_empty_spec as ⟨b, hb⟩
  split
  · have hv : buf.val = [] := hb.mp (by assumption)
    simp [misc.unexpected_buf_eof, misc.io_error_msg, okPart, hv, textRead]
  · have hv : buf.val ≠ [] := fun h => by simp_all
    obtain ⟨x, rest, hx⟩ : ∃ x rest, buf.val = x :: rest := by
      cases h : buf.val with
      | nil => exact absurd h hv
      | cons x rest => exact ⟨x, rest, rfl⟩
    step with Slice.index_usize_spec as ⟨i, hi⟩
    have hix : i = x := by rw [hi]; simp [hx]
    subst hix
    rw [mtext]
    split
    · step with io.ParseBuf.skip_spec as ⟨rest', hr⟩
      subst_vars
      simp [okPart, Val.ofValue, textRead, hx, hr]
    · rw [io.ParseBuf.parse_of_size_none _ _ _ rawbytes_lenenc_size]
      have H := misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec
        misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple () buf
        (fun o rest => (o, rest.val) = checkedLenencStr buf.val)
        (misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf h64)
      apply WP.spec_bind H
      rintro ⟨r, rest'⟩ hr
      have hne : ¬ i.val = 0xFB := by
        intro h; apply (by assumption : ¬ i = 251#u8); apply UScalar.eq_of_val_eq; simpa using h
      simp only [WP.uncurry'_pair] at hr
      rw [hx]
      simp only [textRead, hne, ite_false]
      rw [← hx]
      cases r with
      | Ok rb =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        obtain ⟨c, u⟩ := rb
        step with cow_into_vec_spec as ⟨v, hv⟩
        simp only [okPart, Option.map] at hr ⊢
        rw [← hr]
        simp [Val.ofValue, hv]
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, from_residual_err]
        simp only [okPart, Option.map] at hr ⊢
        rw [← hr]
        simp

theorem byte_val_mod (n : Nat) : (byte n).val = n % 256 := by
  simp [byte, UScalar.val]

theorem lenencStr_head (s t : List U8) :
    ∃ b rest, lenencStr s ++ t = b :: rest ∧ b ≠ 251#u8 := by
  unfold lenencStr lenencInt
  split_ifs with h1 h2 h3
  · refine ⟨_, _, rfl, ?_⟩
    intro h
    have h' : (byte s.length).val = 251 := by rw [h]; rfl
    rw [byte_val_mod] at h'
    omega
  all_goals exact ⟨_, _, rfl, by decide⟩

theorem deserialize_text_bytes_case (buf : io.ParseBuf) (i : U8) (rest : List U8)
    (hx : buf.val = i :: rest) (hi : i ≠ 251#u8)
    (Q : Option value.Value → io.ParseBuf → Prop)
    (hQ : misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf
      ⦃ r rest => ∀ v : alloc.vec.Vec U8, (okPart r).map cowList = some v.val → Q (some (.Bytes v)) rest ⦄)
    (hQn : misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf
      ⦃ r rest => okPart r = none → Q none rest ⦄) :
    value.Value.deserialize_text buf ⦃ r rest => Q (okPart r) rest ⦄ := by
  unfold value.Value.deserialize_text
  step with io.ParseBuf.is_empty_spec as ⟨b, hb⟩
  split
  · simp_all
  step with Slice.index_usize_spec as ⟨j, hj⟩
  have hix : j = i := by rw [hj]; simp [hx]
  subst hix
  rw [mtext]; simp only [hi, ite_false]
  rw [io.ParseBuf.parse_of_size_none _ _ _ rawbytes_lenenc_size]
  have H := misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec
    misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple () buf
    (fun o rest => (∀ v : alloc.vec.Vec U8, o = some v.val → Q (some (.Bytes v)) rest) ∧ (o = none → Q none rest))
    (by
      have := WP.spec_and hQ hQn
      apply WP.spec_mono this
      rintro ⟨r, rest⟩ ⟨h1, h2⟩
      simp only [WP.uncurry'_pair] at *
      refine ⟨h1, fun h => h2 ?_⟩
      cases r <;> simp [okPart] at h ⊢)
  apply WP.spec_bind H
  rintro ⟨r, rest'⟩ hr
  simp only [WP.uncurry'_pair] at hr
  cases r with
  | Ok rb =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    obtain ⟨c, u⟩ := rb
    step with cow_into_vec_spec as ⟨v, hv⟩
    exact hr.1 v (by rw [hv]; rfl)
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch, okPart]
    exact hr.2 (by simp [okPart])

theorem deserialize_text_roundtrip' (s tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = lenencStr s ++ tail) :
    value.Value.deserialize_text buf ⦃ r rest =>
      (okPart r).map Val.ofValue = some (.bytes s) ∧ rest.val = tail ⦄ := by
  obtain ⟨b, rest, hbr, hb⟩ := lenencStr_head s tail
  have := deserialize_text_bytes_case buf b rest (h.trans hbr) hb
    (fun o rest => o.map Val.ofValue = some (.bytes s) ∧ rest.val = tail)
  apply this
  · apply WP.spec_mono (misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip s tail buf h)
    rintro ⟨r, rest⟩ ⟨h1, h2⟩ v hv
    simp_all [Val.ofValue]
  · apply WP.spec_mono (misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip s tail buf h)
    rintro ⟨r, rest⟩ ⟨h1, h2⟩ hn
    simp_all

theorem deserialize_text_null' (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = byte 0xFB :: tail) :
    value.Value.deserialize_text buf ⦃ r rest =>
      (okPart r).map Val.ofValue = some .null ∧ rest.val = tail ⦄ := by
  unfold value.Value.deserialize_text
  step with io.ParseBuf.is_empty_spec as ⟨b, hb⟩
  split
  · simp_all
  step with Slice.index_usize_spec as ⟨j, hj⟩
  have hix : j = 251#u8 := by rw [hj]; simp [h]; rfl
  subst hix
  rw [mtext, if_pos rfl]
  step with io.ParseBuf.skip_spec as ⟨rest', hr⟩
  simp [okPart, Val.ofValue, hr, h]

theorem c32 : ∀ i : Fin 16, i.val ≠ 5 → (32#16).getLsbD i.val = false := by decide
theorem bvaux (b : BitVec 16) : (b &&& 32#16 = 32#16) ↔ b.getLsbD 5 = true := by
  constructor
  · intro h; have := congrArg (fun x => x.getLsbD 5) h; simpa using this
  · intro h; ext i hi
    rw [BitVec.getElem_and]
    by_cases h5 : i = 5
    · subst h5; rw [BitVec.getElem_eq_testBit_toNat] at *; simp_all [BitVec.testBit_toNat]
    · have := c32 ⟨i, hi⟩ h5
      have h2 : (32#16)[i] = false := by rw [← BitVec.getLsbD_eq_getElem]; exact this
      rw [h2]; simp

theorem contains_unsigned (flags : constants.ColumnFlags) :
    constants.ColumnFlags.contains flags constants.ColumnFlags.UNSIGNED_FLAG ⦃ b => b = isUnsigned flags ⦄ := by
  unfold constants.ColumnFlags.contains constants.ColumnFlags.UNSIGNED_FLAG isUnsigned
  simp only [lift, Std.bind_ok, WP.spec_ok]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, UScalar.eq_equiv_bv_eq, UScalar.bv_and]
  have := bvaux flags.bv
  simp only [UScalar.val, BitVec.testBit_toNat]
  exact this

theorem deserialize_tiny_spec (u : Bool) (buf : io.ParseBuf) :
    value.Value.deserialize_tiny u buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = readIntVal 1 u buf.val ⦄ := by
  unfold value.Value.deserialize_tiny
  split
  · step with io.ParseBuf.checked_eat_u8_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
      simp only
      step with UScalar.hcast_inBounds_spec as ⟨i, hi⟩
      simp only [Option.map_some, Option.some.injEq] at ho
      simp [okPart, Val.ofValue, readIntVal, readLE, hl, hi, ho, *]
    · obtain ⟨rfl, rfl⟩ := ho
      simp only
      step with unexpected_buf_eof_spec
      simp [okPart, readIntVal, readLE, hl]
  · step with io.ParseBuf.checked_eat_i8_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
      simp only
      step with IScalar.cast_inBounds_spec as ⟨i, hi⟩
      simp only [Option.map_some, Option.some.injEq] at ho
      simp [okPart, Val.ofValue, readIntVal, readLE, hl, hi, ho, *]
    · obtain ⟨rfl, rfl⟩ := ho
      simp only
      step with unexpected_buf_eof_spec
      simp [okPart, readIntVal, readLE, hl]

theorem deserialize_short_spec (u : Bool) (buf : io.ParseBuf) :
    value.Value.deserialize_short u buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = readIntVal 2 u buf.val ⦄ := by
  unfold value.Value.deserialize_short
  split
  · step with io.ParseBuf.checked_eat_u16_le_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
      simp only
      step with UScalar.hcast_inBounds_spec as ⟨i, hi⟩
      simp only [Option.map_some, Option.some.injEq] at ho
      simp [okPart, Val.ofValue, readIntVal, readLE, hl, hi, ho, *]
    · obtain ⟨rfl, rfl⟩ := ho
      simp only
      step with unexpected_buf_eof_spec
      simp [okPart, readIntVal, readLE, hl]
  · step with io.ParseBuf.checked_eat_i16_le_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
      simp only
      step with IScalar.cast_inBounds_spec as ⟨i, hi⟩
      simp only [Option.map_some, Option.some.injEq] at ho
      simp [okPart, Val.ofValue, readIntVal, readLE, hl, hi, ho, *]
    · obtain ⟨rfl, rfl⟩ := ho
      simp only
      step with unexpected_buf_eof_spec
      simp [okPart, readIntVal, readLE, hl]

theorem deserialize_long_spec (u : Bool) (buf : io.ParseBuf) :
    value.Value.deserialize_long u buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = readIntVal 4 u buf.val ⦄ := by
  unfold value.Value.deserialize_long
  split
  · step with io.ParseBuf.checked_eat_u32_le_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
      simp only
      step with UScalar.hcast_inBounds_spec as ⟨i, hi⟩
      simp only [Option.map_some, Option.some.injEq] at ho
      simp [okPart, Val.ofValue, readIntVal, readLE, hl, hi, ho, *]
    · obtain ⟨rfl, rfl⟩ := ho
      simp only
      step with unexpected_buf_eof_spec
      simp [okPart, readIntVal, readLE, hl]
  · step with io.ParseBuf.checked_eat_i32_le_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
      simp only
      step with IScalar.cast_inBounds_spec as ⟨i, hi⟩
      simp only [Option.map_some, Option.some.injEq] at ho
      simp [okPart, Val.ofValue, readIntVal, readLE, hl, hi, ho, *]
    · obtain ⟨rfl, rfl⟩ := ho
      simp only
      step with unexpected_buf_eof_spec
      simp [okPart, readIntVal, readLE, hl]

theorem deserialize_longlong_spec (u : Bool) (buf : io.ParseBuf) :
    value.Value.deserialize_longlong u buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = binRead .MYSQL_TYPE_LONGLONG u buf.val ⦄ := by
  unfold value.Value.deserialize_longlong
  simp only [binRead, isLenencStrType, Bool.false_eq_true, ite_false]
  split
  · step with io.ParseBuf.checked_eat_u64_le_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
      simp only [Option.map_some, Option.some.injEq] at ho
      simp only
      step with IScalar.hcast_inBounds_spec as ⟨m, hm⟩
      · simp [core.num.I64.MAX, I64.rMax, U64.max, U64.numBits]
      have hm' : m.val = 2 ^ 63 - 1 := by simp [I64.rMax] at hm; omega
      split
      · rename_i hxm
        have hx : x.val ≤ 2 ^ 63 - 1 := by rw [← hm']; exact hxm
        step with UScalar.hcast_inBounds_spec as ⟨i, hi⟩
        simp [okPart, Val.ofValue, readLE, hl, ho.1, ho.2, hi]
        try (rw [← ho.1]; omega)
      · rename_i hxm
        have hx : ¬ x.val ≤ 2 ^ 63 - 1 := by rw [← hm']; exact hxm
        simp [okPart, Val.ofValue, readLE, hl, ho.1, ho.2]
        try (rw [← ho.1]; omega)
    · obtain ⟨rfl, rfl⟩ := ho
      simp only
      step with unexpected_buf_eof_spec
      simp [okPart, readLE, hl]
  · step with io.ParseBuf.checked_eat_i64_le_spec as ⟨o, rest, ho⟩
    split_ifs at ho with hl
    · obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
      simp only [Option.map_some, Option.some.injEq] at ho
      simp [okPart, Val.ofValue, readLE, hl, ho, *]
    · obtain ⟨rfl, rfl⟩ := ho
      simp only
      step with unexpected_buf_eof_spec
      simp [okPart, readLE, hl]

theorem deserialize_datetime_spec (buf : io.ParseBuf) :
    value.Value.deserialize_datetime buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = dateRead buf.val ⦄ := by
  unfold value.Value.deserialize_datetime
  step with io.ParseBuf.checked_eat_u8_spec as ⟨o, buf1, ho⟩
  rcases hb : buf.val with _ | ⟨l, rest⟩
  · have : ¬ 1 ≤ buf.length := by simp [Slice.length, hb]
    rw [if_neg this] at ho
    obtain ⟨rfl, rfl⟩ := ho
    simp only
    step with unexpected_buf_eof_spec
    simp [okPart, dateRead, hb]
  have : 1 ≤ buf.length := by simp [Slice.length, hb]
  rw [if_pos this] at ho
  obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
  simp only [Option.map_some, Option.some.injEq, hb] at ho
  obtain ⟨hx, h1⟩ := ho
  simp [leNat] at hx
  simp only
  step with UScalar.cast_inBounds_spec as ⟨n, hn⟩
  step with io.ParseBuf.checked_eat_buf_spec as ⟨o1, buf2, ho1⟩
  simp only [dateRead]
  have hnl : n.val = l.val := by simp_all
  have hxl : x.val = l.val := by simp_all
  have hlen1 : Slice.length buf1 = rest.length := by simp [Slice.length, h1]
  rw [hnl, hlen1, h1] at ho1
  by_cases hlen : l.val ≤ rest.length
  swap
  · rw [if_neg hlen] at ho1
    obtain ⟨rfl, rfl⟩ := ho1
    simp only
    step with unexpected_buf_eof_spec
    simp [okPart, h1, show rest.length < l.val by omega]
  rw [if_pos hlen] at ho1
  obtain ⟨pb, rfl⟩ : ∃ x, o1 = some x := by cases o1 <;> simp_all
  simp only [Option.map_some, Option.some.injEq] at ho1
  obtain ⟨hpb, hbuf2⟩ := ho1
  simp only [show ¬ rest.length < l.val by omega, ite_false]
  generalize hP : List.take l.val rest = P at hpb ⊢
  have hPl : P.length = l.val := by rw [← hP]; simp; omega
  by_cases h4 : l.val < 4
  · have : ¬ (x ≥ 4#u8) := by scalar_tac
    simp only [this, ite_false, h4, ite_true]
    simp [okPart, Val.ofValue, hbuf2]
  have : x ≥ 4#u8 := by scalar_tac
  simp only [this, ite_true, h4, ite_false]
  simp only [List.drop_one, List.tail_cons, hP] at hpb hbuf2
  rcases P with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, P⟩⟩⟩⟩ <;> simp at hPl <;> try omega
  by_cases h7 : l.val < 7
  · have : ¬ 7 ≤ x.val := by omega
    simp only [this, h7, ite_false, ite_true]
    step* <;> simp_all [Slice.length, leNat, okPart, Val.ofValue]
  rcases P with _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, P⟩⟩⟩ <;> simp at hPl <;> try omega
  have : 7 ≤ x.val := by omega
  simp only [this, h7, ite_false, ite_true]
  by_cases h11 : l.val = 11
  · have : x = 11#u8 := by apply UScalar.eq_of_val_eq; simp; omega
    simp only [this, h11, ite_false, ite_true]
    rcases P with _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, P⟩⟩⟩⟩ <;> simp at hPl <;> try omega
    step* <;> simp_all [Slice.length, leNat, okPart, Val.ofValue]
  · have : x ≠ 11#u8 := by intro h; apply h11; rw [← hxl, h]; rfl
    simp only [this, h11, ite_false, ite_true]
    step* <;> simp_all [Slice.length, leNat, okPart, Val.ofValue]

theorem u8_eq_one_iff (x : U8) : x = 1#u8 ↔ x.val = 1 := by
  constructor
  · rintro rfl; rfl
  · intro h; apply UScalar.eq_of_val_eq; simpa using h

theorem deserialize_time_spec (buf : io.ParseBuf) :
    value.Value.deserialize_time buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = timeRead buf.val ⦄ := by
  unfold value.Value.deserialize_time
  step with io.ParseBuf.checked_eat_u8_spec as ⟨o, buf1, ho⟩
  rcases hb : buf.val with _ | ⟨l, rest⟩
  · have : ¬ 1 ≤ buf.length := by simp [Slice.length, hb]
    rw [if_neg this] at ho
    obtain ⟨rfl, rfl⟩ := ho
    simp only
    step with unexpected_buf_eof_spec
    simp [okPart, timeRead, hb]
  have : 1 ≤ buf.length := by simp [Slice.length, hb]
  rw [if_pos this] at ho
  obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
  simp only [Option.map_some, Option.some.injEq, hb] at ho
  obtain ⟨hx, h1⟩ := ho
  simp [leNat] at hx
  simp only
  step with UScalar.cast_inBounds_spec as ⟨n, hn⟩
  step with io.ParseBuf.checked_eat_buf_spec as ⟨o1, buf2, ho1⟩
  simp only [timeRead]
  have hnl : n.val = l.val := by simp_all
  have hxl : x.val = l.val := by simp_all
  have hlen1 : Slice.length buf1 = rest.length := by simp [Slice.length, h1]
  rw [hnl, hlen1, h1] at ho1
  by_cases hlen : l.val ≤ rest.length
  swap
  · rw [if_neg hlen] at ho1
    obtain ⟨rfl, rfl⟩ := ho1
    simp only
    step with unexpected_buf_eof_spec
    simp [okPart, h1, show rest.length < l.val by omega]
  rw [if_pos hlen] at ho1
  obtain ⟨pb, rfl⟩ : ∃ x, o1 = some x := by cases o1 <;> simp_all
  simp only [Option.map_some, Option.some.injEq] at ho1
  obtain ⟨hpb, hbuf2⟩ := ho1
  simp only [show ¬ rest.length < l.val by omega, ite_false]
  generalize hP : List.take l.val rest = P at hpb ⊢
  have hPl : P.length = l.val := by rw [← hP]; simp; omega
  by_cases h8 : l.val < 8
  · have : ¬ (x ≥ 8#u8) := by scalar_tac
    simp only [this, ite_false, h8, ite_true]
    simp [okPart, Val.ofValue, hbuf2]
  have : x ≥ 8#u8 := by scalar_tac
  simp only [this, ite_true, h8, ite_false]
  simp only [List.drop_one, List.tail_cons, hP] at hpb hbuf2
  rcases P with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, P⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at hPl <;> try omega
  by_cases h12 : l.val = 12
  · have : x = 12#u8 := by apply UScalar.eq_of_val_eq; simp; omega
    simp only [this, h12, ite_false, ite_true]
    rcases P with _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, P⟩⟩⟩⟩ <;> simp at hPl <;> try omega
    step* <;> simp_all [Slice.length, leNat, okPart, Val.ofValue, u8_eq_one_iff]
  · have : x ≠ 12#u8 := by intro h; apply h12; rw [← hxl, h]; rfl
    simp only [this, h12, ite_false, ite_true]
    step* <;> simp_all [Slice.length, leNat, okPart, Val.ofValue, u8_eq_one_iff]

theorem bin_str_case (ct : constants.ColumnType) (flags : constants.ColumnFlags)
    (hct : isLenencStrType ct = true) (buf : io.ParseBuf)
    (Q : Option Val → List U8 → Prop)
    (h : io.ParseBuf.checked_eat_lenenc_str buf ⦃ o rest => Q ((o.map (·.val)).map Val.bytes) rest.val ⦄) :
    value.Value.deserialize_bin (ct, flags) buf ⦃ r rest => Q ((okPart r).map Val.ofValue) rest.val ⦄ := by
  cases ct <;> simp [isLenencStrType] at hct <;> unfold value.Value.deserialize_bin <;> dsimp only <;>
  · apply WP.spec_bind h
    rintro ⟨o, rest⟩ hq
    simp only [WP.uncurry'_pair] at hq
    cases o with
    | none =>
      try simp only
      step with unexpected_buf_eof_spec
      simpa [okPart] using hq
    | some x =>
      try simp only
      step with alloc.slice.Slice.to_vec_spec as ⟨v, hv⟩
      have hvx : v.val = x.val := by simp [alloc.vec.Vec.val, hv]
      simpa [okPart, Val.ofValue, hvx] using hq

theorem float_spec (buf : io.ParseBuf) (flags : constants.ColumnFlags) :
    value.Value.deserialize_bin (.MYSQL_TYPE_FLOAT, flags) buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = binRead .MYSQL_TYPE_FLOAT (isUnsigned flags) buf.val ⦄ := by
  unfold value.Value.deserialize_bin; dsimp only
  simp only [binRead, isLenencStrType, Bool.false_eq_true, ite_false]
  step with io.ParseBuf.checked_eat_f32_le_spec as ⟨o, rest, ho⟩
  split_ifs at ho with hl
  · obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
    simp only [Option.map_some, Option.some.injEq] at ho
    simp [okPart, Val.ofValue, readLE, hl, ho]
  · obtain ⟨rfl, rfl⟩ := ho
    simp only
    step with unexpected_buf_eof_spec
    simp [okPart, readLE, hl]

theorem double_spec (buf : io.ParseBuf) (flags : constants.ColumnFlags) :
    value.Value.deserialize_bin (.MYSQL_TYPE_DOUBLE, flags) buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = binRead .MYSQL_TYPE_DOUBLE (isUnsigned flags) buf.val ⦄ := by
  unfold value.Value.deserialize_bin; dsimp only
  simp only [binRead, isLenencStrType, Bool.false_eq_true, ite_false]
  step with io.ParseBuf.checked_eat_f64_le_spec as ⟨o, rest, ho⟩
  split_ifs at ho with hl
  · obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
    simp only [Option.map_some, Option.some.injEq] at ho
    simp [okPart, Val.ofValue, readLE, hl, ho]
  · obtain ⟨rfl, rfl⟩ := ho
    simp only
    step with unexpected_buf_eof_spec
    simp [okPart, readLE, hl]

theorem bin_nonstr_spec (ct : constants.ColumnType) (flags : constants.ColumnFlags)
    (hs : isLenencStrType ct = false) (hct : binSupported ct = true) (buf : io.ParseBuf) :
    value.Value.deserialize_bin (ct, flags) buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = binRead ct (isUnsigned flags) buf.val ⦄ := by
  cases ct <;> simp [isLenencStrType] at hs <;> simp [binSupported] at hct
  case MYSQL_TYPE_FLOAT => exact float_spec buf flags
  case MYSQL_TYPE_DOUBLE => exact double_spec buf flags
  all_goals
    unfold value.Value.deserialize_bin; dsimp only
    simp only [binRead, isLenencStrType, Bool.false_eq_true, ite_false]
  case MYSQL_TYPE_NULL => simp [okPart, Val.ofValue]
  case MYSQL_TYPE_TIMESTAMP => exact deserialize_datetime_spec buf
  case MYSQL_TYPE_DATE => exact deserialize_datetime_spec buf
  case MYSQL_TYPE_DATETIME => exact deserialize_datetime_spec buf
  case MYSQL_TYPE_NEWDATE => exact deserialize_datetime_spec buf
  case MYSQL_TYPE_TIME => exact deserialize_time_spec buf
  case MYSQL_TYPE_TINY =>
    step with contains_unsigned as ⟨b, hb⟩; subst hb; exact deserialize_tiny_spec _ buf
  case MYSQL_TYPE_SHORT =>
    step with contains_unsigned as ⟨b, hb⟩; subst hb; exact deserialize_short_spec _ buf
  case MYSQL_TYPE_YEAR =>
    step with contains_unsigned as ⟨b, hb⟩; subst hb; exact deserialize_short_spec _ buf
  case MYSQL_TYPE_LONG =>
    step with contains_unsigned as ⟨b, hb⟩; subst hb; exact deserialize_long_spec _ buf
  case MYSQL_TYPE_INT24 =>
    step with contains_unsigned as ⟨b, hb⟩; subst hb; exact deserialize_long_spec _ buf
  case MYSQL_TYPE_LONGLONG =>
    step with contains_unsigned as ⟨b, hb⟩; subst hb
    have := deserialize_longlong_spec (isUnsigned flags) buf
    simpa [binRead, isLenencStrType] using this

theorem deserialize_bin_spec' (h64 : Target64) (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hct : binSupported ct = true) (buf : io.ParseBuf) :
    value.Value.deserialize_bin (ct, flags) buf ⦃ r rest =>
      ((okPart r).map Val.ofValue, rest.val) = binRead ct (isUnsigned flags) buf.val ⦄ := by
  cases hs : isLenencStrType ct
  · exact bin_nonstr_spec ct flags hs hct buf
  · apply bin_str_case ct flags hs buf (fun o rest => (o, rest) = binRead ct (isUnsigned flags) buf.val)
    apply WP.spec_mono (io.ParseBuf.checked_eat_lenenc_str_spec h64 buf)
    rintro ⟨o, rest⟩ ho
    simp only [WP.uncurry'_pair] at ho ⊢
    simp only [binRead, hs, ite_true, ← ho]
    cases o <;> simp

theorem leNat_leBytes' (k n : Nat) : leNat (leBytes k n) = n % 2 ^ (8 * k) := by
  induction k generalizing n with
  | zero => simp [leBytes, leNat, Nat.mod_one]
  | succ k ih =>
    simp only [leBytes, leNat, ih, byte_val_mod]
    have h2 : 2 ^ (8 * (k+1)) = 256 * 2 ^ (8 * k) := by rw [Nat.mul_succ, Nat.pow_add]; omega
    rw [h2, Nat.mod_mul]

theorem readLE_leBytes (k n : Nat) (t : List U8) :
    readLE k (leBytes k n ++ t) = some (n % 2 ^ (8 * k), t) := by
  simp [readLE, length_leBytes', leNat_leBytes', List.take_append_of_le_length, List.drop_append_of_le_length]


theorem binRead_int (x : Int) (hx : -2 ^ 63 ≤ x ∧ x < 2 ^ 63) (u : Bool) (t : List U8) :
    binRead .MYSQL_TYPE_LONGLONG u (leBytesI 8 x ++ t) = (some (binNorm u (.int x)), t) := by
  simp only [binRead, isLenencStrType, Bool.false_eq_true, ite_false, leBytesI, readLE_leBytes]
  generalize hn : (x % (2 ^ (8 * 8) : Int)).toNat = n
  have hn' : (n : Int) = x % 2 ^ 64 := by rw [← hn]; exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have hlt : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt (by simpa using hlt)]
  cases u <;> simp only [binNorm, toSigned, Bool.false_eq_true, ite_false, ite_true, not_false_eq_true, not_true_eq_false] <;>
    split_ifs <;> simp <;> omega

theorem binRead_uint (x : Nat) (hx : x < 2 ^ 64) (u : Bool) (t : List U8) :
    binRead .MYSQL_TYPE_LONGLONG u (leBytes 8 x ++ t) = (some (binNorm u (.uint x)), t) := by
  simp only [binRead, isLenencStrType, Bool.false_eq_true, ite_false, readLE_leBytes]
  rw [Nat.mod_eq_of_lt (by simpa using hx)]
  cases u <;> simp [binNorm]

theorem dateRead_enc (y mo d h mi s us : Nat) (hy : y < 2 ^ 16) (hmo : mo < 256) (hd : d < 256)
    (hh : h < 256) (hmi : mi < 256) (hs : s < 256) (hus : us < 2 ^ 32) (t : List U8) :
    dateRead (binEnc (.date y mo d h mi s us) ++ t) = (some (.date y mo d h mi s us), t) := by
  simp only [binEnc]
  split_ifs with h0 h4 h7
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h0
    simp [dateRead, byte_val_mod]
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h4
    simp [dateRead, byte_val_mod, leBytes]
    rw [if_neg (by omega)]
    simp only [Option.some.injEq, Prod.mk.injEq, Val.date.injEq, and_true]
    omega
  · subst h7
    simp [dateRead, byte_val_mod, leBytes]
    rw [if_neg (by omega)]
    simp only [Option.some.injEq, Prod.mk.injEq, Val.date.injEq, and_true]
    omega
  · simp [dateRead, byte_val_mod, leBytes, leNat]
    rw [if_neg (by omega)]
    simp only [Option.some.injEq, Prod.mk.injEq, Val.date.injEq, and_true]
    omega

theorem binNorm_time (u neg : Bool) (d h m s us : Nat) :
    binNorm u (.time neg d h m s us) =
      if d = 0 ∧ h = 0 ∧ m = 0 ∧ s = 0 ∧ us = 0 then .time false 0 0 0 0 0 else .time neg d h m s us := by
  rcases d with _|d <;> rcases h with _|h <;> rcases m with _|m <;> rcases s with _|s <;>
    rcases us with _|us <;> simp [binNorm]

theorem timeRead_enc (neg : Bool) (d h mi s us : Nat) (hd : d < 2 ^ 32)
    (hh : h < 256) (hmi : mi < 256) (hs : s < 256) (hus : us < 2 ^ 32) (t : List U8) :
    timeRead (binEnc (.time neg d h mi s us) ++ t) = (some (binNorm false (.time neg d h mi s us)), t) := by
  rw [binNorm_time]
  by_cases h0 : d = 0 ∧ h = 0 ∧ mi = 0 ∧ s = 0 ∧ us = 0
  · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h0
    simp [binEnc, timeRead, byte_val_mod]
  rw [if_neg h0]
  by_cases h8 : us = 0
  · subst h8
    have h0' : ¬(d = 0 ∧ h = 0 ∧ mi = 0 ∧ s = 0) := by simpa using h0
    cases neg <;> simp [binEnc, h0', timeRead, byte_val_mod, leBytes, leNat, List.cons_append] <;>
      (rw [if_neg (by omega)]; simp only [Option.some.injEq, Prod.mk.injEq, Val.time.injEq, and_true]) <;>
      (simp only [true_and]; omega)
  · cases neg <;> simp [binEnc, h0, h8, timeRead, byte_val_mod, leBytes, leNat, List.cons_append] <;>
      (rw [if_neg (by omega)]; simp only [Option.some.injEq, Prod.mk.injEq, Val.time.injEq, and_true]) <;>
      (simp only [true_and]; omega)

theorem binRead_binEnc' (v : value.Value) (ct : constants.ColumnType)
    (u : Bool) (t : List U8) (hc : binCompatible (Val.ofValue v) ct)
    (hnb : ∀ x, v ≠ .Bytes x) :
    binRead ct u (binEnc (Val.ofValue v) ++ t) = (some (binNorm u (Val.ofValue v)), t) := by
  cases v with
  | NULL => simp only [Val.ofValue, binCompatible] at hc; subst hc; simp [binRead, isLenencStrType, binEnc, binNorm, Val.ofValue]
  | Bytes x => exact absurd rfl (hnb x)
  | Int x =>
    simp only [Val.ofValue, binCompatible] at hc; subst hc
    exact binRead_int _ (by scalar_tac) u t
  | UInt x =>
    simp only [Val.ofValue, binCompatible] at hc; subst hc
    exact binRead_uint _ (by scalar_tac) u t
  | Float x =>
    simp only [Val.ofValue, binCompatible] at hc; subst hc
    simp only [Val.ofValue, binRead, isLenencStrType, Bool.false_eq_true, ite_false, binEnc, readLE_leBytes, binNorm]
    rw [Nat.mod_eq_of_lt (by have := x.bits.hBounds; simpa using this)]
  | Double x =>
    simp only [Val.ofValue, binCompatible] at hc; subst hc
    simp only [Val.ofValue, binRead, isLenencStrType, Bool.false_eq_true, ite_false, binEnc, readLE_leBytes, binNorm]
    rw [Nat.mod_eq_of_lt (by have := x.bits.hBounds; simpa using this)]
  | Date y mo d h mi s us =>
    simp only [Val.ofValue, binCompatible] at hc ⊢
    have e := dateRead_enc y.val mo.val d.val h.val mi.val s.val us.val (by scalar_tac) (by scalar_tac)
      (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) t
    rcases hc with rfl | rfl | rfl | rfl <;> simpa [binRead, isLenencStrType, binNorm] using e
  | Time neg d h mi s us =>
    simp only [Val.ofValue, binCompatible] at hc ⊢
    subst hc
    have e := timeRead_enc neg d.val h.val mi.val s.val us.val (by scalar_tac) (by scalar_tac)
      (by scalar_tac) (by scalar_tac) (by scalar_tac) t
    simp only [binRead, isLenencStrType, Bool.false_eq_true, ite_false]
    rw [e, binNorm_time, binNorm_time]

theorem deserialize_bin_roundtrip' (v : value.Value) (ct : constants.ColumnType)
    (flags : constants.ColumnFlags) (hc : binCompatible (Val.ofValue v) ct)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = binEnc (Val.ofValue v) ++ tail) :
    value.Value.deserialize_bin (ct, flags) buf ⦃ r rest =>
      (okPart r).map Val.ofValue = some (binNorm (isUnsigned flags) (Val.ofValue v)) ∧
      rest.val = tail ⦄ := by
  cases v with
  | Bytes x =>
    simp only [Val.ofValue, binCompatible, binEnc] at hc h ⊢
    apply bin_str_case ct flags hc buf (fun o rest => o = some (binNorm (isUnsigned flags) (.bytes x.val)) ∧ rest = tail)
    apply WP.spec_mono (io.ParseBuf.checked_eat_lenenc_str_roundtrip _ tail buf h)
    rintro ⟨o, rest⟩ ⟨h1, h2⟩
    simp_all [binNorm]
  | _ =>
    have hs : isLenencStrType ct = false := by
      revert hc; cases ct <;> simp [Val.ofValue, binCompatible, isLenencStrType]
    have hsup : binSupported ct = true := by
      revert hc; cases ct <;> simp [Val.ofValue, binCompatible, binSupported]
    apply WP.spec_mono (bin_nonstr_spec ct flags hs hsup buf)
    rintro ⟨r, rest⟩ hr
    simp only [WP.uncurry'_pair] at hr ⊢
    rw [h, binRead_binEnc' _ ct _ tail hc (by intro x hx; cases hx)] at hr
    simp_all


@[simp] theorem new_debug_eq {T : Type} (i : core.fmt.Debug T) (x : T) :
    core.fmt.rt.Argument.new_debug i x = ok (by unfold core.fmt.rt.Argument; exact ()) := rfl

@[simp] theorem args_new_eq {N M : Usize} (a : Std.Array U8 N) (b : Std.Array core.fmt.rt.Argument M) :
    core.fmt.Arguments.new a b = ok (by unfold core.fmt.Arguments; exact ()) := rfl

end mysql_common.ValueUtil
