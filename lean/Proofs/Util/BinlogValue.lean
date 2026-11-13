import Proofs.Io.ParseBuf
import Proofs.Util.IntAndMisc
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
open Aeneas Aeneas.Std Result mysql_common Defs

/-! Helper lemmas for the binlog packed-time readers and `BinlogValue::deserialize`
(`Proofs/Binlog/Misc/*`, `Proofs/Binlog/Value/*`, `Proofs/Defs/LemmasBinlogCore.lean`). -/

namespace mysql_common.BinlogUtil

theorem toSigned_eq_bmod (n : Nat) (h : n < 2 ^ 64) : toSigned 64 n = Int.bmod n (2 ^ 64) := by
  unfold toSigned Int.bmod
  have : ((n:Int) % ((2^64 : Nat) : Int)) = n := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [this]; split_ifs <;> omega

@[step]
theorem make_int_spec (i : I64) :
    binlog.misc.my_packed_time_make_int i ⦃ r => r.val = wrapI64 (i.val * 2 ^ 24) ⦄ := by
  unfold binlog.misc.my_packed_time_make_int
  step*
  rw [UScalar.hcast_val_eq, wrapI64, toSigned_eq_bmod _ (by omega), i2_post, i1_post, IScalar.hcast_val_eq]
  simp only [U64.size, Nat.shiftLeft_eq, UScalarTy.numBits, U64.numBits]
  have h0 : (0:Int) ≤ i.val % 2^64 := Int.emod_nonneg _ (by norm_num)
  have h1 : (0:Int) ≤ (i.val * 2^24) % 2^64 := Int.emod_nonneg _ (by norm_num)
  congr 1
  zify [h0, h1]
  rw [Int.toNat_of_nonneg h0, Int.toNat_of_nonneg h1]
  push_cast
  rw [Int.mul_emod, Int.emod_emod_of_dvd _ (by norm_num), ← Int.mul_emod]

theorem wrapI64_bounds (x : Int) : -2 ^ 63 ≤ wrapI64 x ∧ wrapI64 x < 2 ^ 63 := by
  have h0 : (0:Int) ≤ x % 2^64 := Int.emod_nonneg _ (by norm_num)
  have h1 : x % 2^64 < 2^64 := Int.emod_lt_of_pos _ (by norm_num)
  unfold wrapI64 toSigned
  split_ifs <;> omega

theorem wrapI64_exact (x : Int) (h : -2 ^ 63 ≤ x ∧ x < 2 ^ 63) : wrapI64 x = x := by
  unfold wrapI64 toSigned
  split_ifs <;> omega

@[step]
theorem make_spec (i f : I64)
    (h : -2 ^ 63 ≤ wrapI64 (i.val * 2 ^ 24) + f.val ∧ wrapI64 (i.val * 2 ^ 24) + f.val < 2 ^ 63) :
    binlog.misc.my_packed_time_make i f ⦃ r => r.val = wrapI64 (i.val * 2 ^ 24) + f.val ⦄ := by
  have := make_int_spec i
  unfold binlog.misc.my_packed_time_make_int at this
  unfold binlog.misc.my_packed_time_make
  simp only [lift, Std.bind_ok] at this ⊢
  obtain ⟨v, hv, hv2⟩ := PBUtil.spec_eq_ok (show (IScalar.hcast UScalarTy.U64 i <<< 24#i32) ⦃ _ => True ⦄ by step*)
  rw [hv] at this ⊢
  simp only [Std.bind_ok, WP.spec_ok] at this ⊢
  step*

theorem iadd_overflow {ty : IScalarTy} (x y : IScalar ty)
    (h : ¬(-2 ^ (ty.numBits - 1) ≤ x.val + y.val ∧ x.val + y.val < 2 ^ (ty.numBits - 1))) :
    x + y = fail .integerOverflow := by
  show IScalar.add x y = _
  simp only [IScalar.add, IScalar.tryMk]
  have := IScalar.tryMkOpt_eq ty (x.val + y.val)
  cases hc : IScalar.tryMkOpt ty (x.val + y.val) with
  | none => rfl
  | some z => rw [hc] at this; exfalso; simp [IScalar.inBounds] at this; omega

theorem make_overflow (i f : I64)
    (h : ¬(-2 ^ 63 ≤ wrapI64 (i.val * 2 ^ 24) + f.val ∧ wrapI64 (i.val * 2 ^ 24) + f.val < 2 ^ 63)) :
    binlog.misc.my_packed_time_make i f = fail .integerOverflow := by
  have := make_int_spec i
  unfold binlog.misc.my_packed_time_make_int at this
  unfold binlog.misc.my_packed_time_make
  simp only [lift, Std.bind_ok] at this ⊢
  obtain ⟨v, hv, hv2⟩ := PBUtil.spec_eq_ok (show (IScalar.hcast UScalarTy.U64 i <<< 24#i32) ⦃ _ => True ⦄ by step*)
  rw [hv] at this ⊢
  simp only [Std.bind_ok, WP.spec_ok] at this ⊢
  apply iadd_overflow
  simp only [IScalarTy.numBits, this]
  exact h

@[step]
theorem get_int_part_spec (i : I64) :
    binlog.misc.my_packed_time_get_int_part i ⦃ r => r.val = packedIntPart i.val ⦄ := by
  unfold binlog.misc.my_packed_time_get_int_part
  step*
  rw [r_post, packedIntPart, Int.shiftRight_eq_div_pow, Int.fdiv_eq_ediv_of_nonneg _ (by norm_num)]
  rfl

@[step]
theorem get_frac_part_spec (i : I64) :
    binlog.misc.my_packed_time_get_frac_part i ⦃ r => r.val = packedFracPart i.val ⦄ := by
  unfold binlog.misc.my_packed_time_get_frac_part
  step*
  have : i1.val = 2^24 := by rw [i1_post]; simp [I64.size, Int.bmod, I64.numBits, Int.shiftLeft_eq]
  rw [r_post, this, packedFracPart]

theorem shr_nat (x : I64) (n k : Nat) (hx : x.val = (n : Int)) : x.val >>> k = ((n / 2 ^ k : Nat) : Int) := by
  rw [hx, Int.shiftRight_eq_div_pow]; push_cast; rfl

theorem hcast32_nat (x : I64) (n : Nat) (hx : x.val = (n : Int)) :
    (IScalar.hcast .U32 x).val = n % 2 ^ 32 := by
  rw [IScalar.hcast_val_eq, hx]; simp only [UScalarTy.numBits]; omega

theorem hcast64_nat (x : I64) (n : Nat) (hx : x.val = (n : Int)) :
    (IScalar.hcast .U64 x).val = n % 2 ^ 64 := by
  rw [IScalar.hcast_val_eq, hx]; simp only [UScalarTy.numBits]; omega

theorem cast8_small {ty : UScalarTy} (x : UScalar ty) (h : x.val < 256) :
    (UScalar.cast .U8 x).val = x.val := by
  rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega

theorem cast16_small {ty : UScalarTy} (x : UScalar ty) (h : x.val < 2 ^ 16) :
    (UScalar.cast .U16 x).val = x.val := by
  rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega

theorem time_from_packed_spec (tmp : I64) (h : tmp.val ≠ -2 ^ 63) :
    binlog.misc.time_from_packed tmp ⦃ v => Val.ofValue v = timeFromPacked tmp.val ⦄ := by
  unfold binlog.misc.time_from_packed
  split
  · step*
    have hneg : tmp.val < 0 := by scalar_tac
    have ha : x.val = ((tmp.val.natAbs : Nat) : Int) := by omega
    simp only [Val.ofValue, timeFromPacked, decide_eq_true hneg]
    generalize tmp.val.natAbs = a at ha ⊢
    have hb : a < 2^63 := by scalar_tac
    have hhms : hms.val = ((a / 2^24 : Nat) : Int) := by
      rw [hms_post, packedIntPart, ha, Int.fdiv_eq_ediv_of_nonneg _ (by norm_num)]; push_cast; rfl
    have hu : u.val = ((a % 2^24 : Nat) : Int) := by
      rw [u_post, packedFracPart, ha]; push_cast; rfl
    rw [shr_nat _ _ _ hhms] at i_post i3_post
    rw [i1_post, hcast32_nat _ _ i_post] at h_post
    rw [i4_post, hcast32_nat _ _ i3_post] at m_post
    rw [i6_post, hcast32_nat _ _ hhms] at s_post
    have hi2 : i2.val = 1024 := by rw [i2_post]; simp [U32.size, U32.numBits]
    have hi5 : i5.val = 64 := by rw [i5_post]; simp [U32.size, U32.numBits]
    rw [hi2] at h_post; rw [hi5] at m_post s_post
    rw [i7_post, cast8_small _ (by omega), i8_post, cast8_small _ (by omega), i9_post, cast8_small _ (by omega), i10_post, hcast32_nat _ _ hu]
    simp only [Val.time.injEq, true_and]
    norm_num at *
    omega
  · step*
    have hneg : ¬ tmp.val < 0 := by scalar_tac
    have ha : tmp.val = ((tmp.val.natAbs : Nat) : Int) := by omega
    simp only [Val.ofValue, timeFromPacked, decide_eq_false hneg]
    generalize tmp.val.natAbs = a at ha ⊢
    have hb : a < 2^63 := by scalar_tac
    have hhms : hms.val = ((a / 2^24 : Nat) : Int) := by
      rw [hms_post, packedIntPart, ha, Int.fdiv_eq_ediv_of_nonneg _ (by norm_num)]; push_cast; rfl
    have hu : u.val = ((a % 2^24 : Nat) : Int) := by
      rw [u_post, packedFracPart, ha]; push_cast; rfl
    rw [shr_nat _ _ _ hhms] at i_post i3_post
    rw [i1_post, hcast32_nat _ _ i_post] at h_post
    rw [i4_post, hcast32_nat _ _ i3_post] at m_post
    rw [i6_post, hcast32_nat _ _ hhms] at s_post
    have hi2 : i2.val = 1024 := by rw [i2_post]; simp [U32.size, U32.numBits]
    have hi5 : i5.val = 64 := by rw [i5_post]; simp [U32.size, U32.numBits]
    rw [hi2] at h_post; rw [hi5] at m_post s_post
    rw [i7_post, cast8_small _ (by omega), i8_post, cast8_small _ (by omega), i9_post, cast8_small _ (by omega), i10_post, hcast32_nat _ _ hu]
    simp only [Val.time.injEq, true_and]
    norm_num at *
    omega

end mysql_common.BinlogUtil

namespace mysql_common.BinlogUtil

theorem ineg_overflow {ty : IScalarTy} (x : IScalar ty)
    (h : ¬(-2 ^ (ty.numBits - 1) ≤ -x.val ∧ -x.val < 2 ^ (ty.numBits - 1))) :
    -. x = fail .integerOverflow := by
  show IScalar.neg x = _
  simp only [IScalar.neg, IScalar.tryMk]
  have := IScalar.tryMkOpt_eq ty (-x.val)
  cases hc : IScalar.tryMkOpt ty (-x.val) with
  | none => rfl
  | some z => rw [hc] at this; exfalso; simp [IScalar.inBounds] at this; omega

theorem time_from_packed_min (tmp : I64) (h : tmp.val = -2 ^ 63) :
    binlog.misc.time_from_packed tmp = fail .integerOverflow := by
  unfold binlog.misc.time_from_packed
  have hlt : tmp < 0#i64 := by scalar_tac
  simp [hlt, ineg_overflow tmp (by simp only [IScalarTy.numBits]; omega)]

theorem datetime_from_packed_min (tmp : I64) (h : tmp.val = -2 ^ 63) :
    binlog.misc.datetime_from_packed tmp = fail .integerOverflow := by
  unfold binlog.misc.datetime_from_packed
  have hlt : tmp < 0#i64 := by scalar_tac
  simp [hlt, ineg_overflow tmp (by simp only [IScalarTy.numBits]; omega)]

theorem tmod_nat (x : Int) (n k : Nat) (hx : x = (n : Int)) : x.tmod (k : Int) = ((n % k : Nat) : Int) := by
  subst hx; rfl

theorem tdiv_nat (x : Int) (n k : Nat) (hx : x = (n : Int)) : x.tdiv (k : Int) = ((n / k : Nat) : Int) := by
  subst hx; rfl

theorem hcast8_nat (x : I64) (n : Nat) (hx : x.val = (n : Int)) :
    (IScalar.hcast .U8 x).val = n % 2 ^ 8 := by
  rw [IScalar.hcast_val_eq, hx]; simp only [UScalarTy.numBits]; omega

theorem datetime_from_packed_spec (tmp : I64) (h : tmp.val ≠ -2 ^ 63) :
    binlog.misc.datetime_from_packed tmp ⦃ v => Val.ofValue v = datetimeFromPacked tmp.val ⦄ := by
  unfold binlog.misc.datetime_from_packed
  split
  · step*
    have ha : tmp1.val = ((tmp.val.natAbs : Nat) : Int) := by scalar_tac
    simp only [Val.ofValue, datetimeFromPacked]
    generalize tmp.val.natAbs = a at ha ⊢
    have hb : a < 2^63 := by scalar_tac
    have hymdhms : ymdhms.val = ((a / 2^24 : Nat) : Int) := by
      rw [ymdhms_post, packedIntPart, ha, Int.fdiv_eq_ediv_of_nonneg _ (by norm_num)]; push_cast; rfl
    have hu : usec.val = ((a % 2^24 : Nat) : Int) := by
      rw [usec_post, packedFracPart, ha]; push_cast; rfl
    rw [shr_nat _ _ _ hymdhms] at ymd_post
    rw [shr_nat _ _ _ ymd_post] at ym_post
    have hi : i.val = ((2^17 : Nat) : Int) := by rw [i_post]; simp [I64.size, Int.bmod, I64.numBits, Int.shiftLeft_eq]
    have hi1 : i1.val = ((2^5 : Nat) : Int) := by rw [i1_post]; simp [I64.size, Int.bmod, I64.numBits, Int.shiftLeft_eq]
    have hi3 : i3.val = ((2^6 : Nat) : Int) := by rw [i3_post]; simp [I64.size, Int.bmod, I64.numBits, Int.shiftLeft_eq]
    have hhms : hms.val = ((a / 2^24 % 2^17 : Nat) : Int) := by rw [hms_post, hi]; exact tmod_nat _ _ _ hymdhms
    have hday : day.val = ((a / 2^24 / 2^17 % 2^5 : Nat) : Int) := by rw [day_post, hi1]; exact tmod_nat _ _ _ ymd_post
    have hmon : mon.val = ((a / 2^24 / 2^17 / 2^5 % 13 : Nat) : Int) := by rw [mon_post]; exact tmod_nat _ _ 13 ym_post
    have hi2 : i2.val = ((a / 2^24 / 2^17 / 2^5 / 13 : Nat) : Int) := by rw [i2_post]; exact tdiv_nat _ _ 13 ym_post
    have hsec : sec.val = ((a / 2^24 % 2^17 % 2^6 : Nat) : Int) := by rw [sec_post, hi3]; exact tmod_nat _ _ _ hhms
    have hi4 : i4.val = ((a / 2^24 % 2^17 / 2^6 : Nat) : Int) := by rw [i4_post]; exact shr_nat _ _ _ hhms
    have hi5 : i5.val = ((a / 2^24 % 2^17 / 2^12 : Nat) : Int) := by rw [i5_post]; exact shr_nat _ _ _ hhms
    have hmin : min.val = ((a / 2^24 % 2^17 / 2^6 % 2^6 : Nat) : Int) := by rw [min_post, hi3]; exact tmod_nat _ _ _ hi4
    have hyear : year.val = a / 2^24 / 2^17 / 2^5 / 13 % 2^32 := by rw [year_post]; exact hcast32_nat _ _ hi2
    have hhour : hour.val = a / 2^24 % 2^17 / 2^12 % 2^32 := by rw [hour_post]; exact hcast32_nat _ _ hi5
    rw [i6_post, cast16_small _ (by rw [hyear]; omega), i7_post, hcast8_nat _ _ hmon, i8_post, hcast8_nat _ _ hday,
      i9_post, cast8_small _ (by rw [hhour]; omega), i10_post, hcast8_nat _ _ hmin, i11_post, hcast8_nat _ _ hsec,
      i12_post, hcast32_nat _ _ hu, hyear, hhour]
    simp only [Val.date.injEq]
    norm_num at *
    omega
  · step*
    have ha : tmp.val = ((tmp.val.natAbs : Nat) : Int) := by scalar_tac
    simp only [Val.ofValue, datetimeFromPacked]
    generalize tmp.val.natAbs = a at ha ⊢
    have hb : a < 2^63 := by scalar_tac
    have hymdhms : ymdhms.val = ((a / 2^24 : Nat) : Int) := by
      rw [ymdhms_post, packedIntPart, ha, Int.fdiv_eq_ediv_of_nonneg _ (by norm_num)]; push_cast; rfl
    have hu : usec.val = ((a % 2^24 : Nat) : Int) := by
      rw [usec_post, packedFracPart, ha]; push_cast; rfl
    rw [shr_nat _ _ _ hymdhms] at ymd_post
    rw [shr_nat _ _ _ ymd_post] at ym_post
    have hi : i.val = ((2^17 : Nat) : Int) := by rw [i_post]; simp [I64.size, Int.bmod, I64.numBits, Int.shiftLeft_eq]
    have hi1 : i1.val = ((2^5 : Nat) : Int) := by rw [i1_post]; simp [I64.size, Int.bmod, I64.numBits, Int.shiftLeft_eq]
    have hi3 : i3.val = ((2^6 : Nat) : Int) := by rw [i3_post]; simp [I64.size, Int.bmod, I64.numBits, Int.shiftLeft_eq]
    have hhms : hms.val = ((a / 2^24 % 2^17 : Nat) : Int) := by rw [hms_post, hi]; exact tmod_nat _ _ _ hymdhms
    have hday : day.val = ((a / 2^24 / 2^17 % 2^5 : Nat) : Int) := by rw [day_post, hi1]; exact tmod_nat _ _ _ ymd_post
    have hmon : mon.val = ((a / 2^24 / 2^17 / 2^5 % 13 : Nat) : Int) := by rw [mon_post]; exact tmod_nat _ _ 13 ym_post
    have hi2 : i2.val = ((a / 2^24 / 2^17 / 2^5 / 13 : Nat) : Int) := by rw [i2_post]; exact tdiv_nat _ _ 13 ym_post
    have hsec : sec.val = ((a / 2^24 % 2^17 % 2^6 : Nat) : Int) := by rw [sec_post, hi3]; exact tmod_nat _ _ _ hhms
    have hi4 : i4.val = ((a / 2^24 % 2^17 / 2^6 : Nat) : Int) := by rw [i4_post]; exact shr_nat _ _ _ hhms
    have hi5 : i5.val = ((a / 2^24 % 2^17 / 2^12 : Nat) : Int) := by rw [i5_post]; exact shr_nat _ _ _ hhms
    have hmin : min.val = ((a / 2^24 % 2^17 / 2^6 % 2^6 : Nat) : Int) := by rw [min_post, hi3]; exact tmod_nat _ _ _ hi4
    have hyear : year.val = a / 2^24 / 2^17 / 2^5 / 13 % 2^32 := by rw [year_post]; exact hcast32_nat _ _ hi2
    have hhour : hour.val = a / 2^24 % 2^17 / 2^12 % 2^32 := by rw [hour_post]; exact hcast32_nat _ _ hi5
    rw [i6_post, cast16_small _ (by rw [hyear]; omega), i7_post, hcast8_nat _ _ hmon, i8_post, hcast8_nat _ _ hday,
      i9_post, cast8_small _ (by rw [hhour]; omega), i10_post, hcast8_nat _ _ hmin, i11_post, hcast8_nat _ _ hsec,
      i12_post, hcast32_nat _ _ hu, hyear, hhour]
    simp only [Val.date.injEq]
    norm_num at *
    omega

end mysql_common.BinlogUtil

namespace mysql_common.BinlogUtil

/-- The opaque `read_exact_eof` returns (it builds an `io::Error`); nothing in the trusted base says so. -/
def EofOk : Prop := ∃ e, binlog.trusted.read_exact_eof = ok e

theorem read_eof_spec (input : io.ParseBuf) (hE : EofOk) :
    binlog.misc.read_eof input ⦃ _ rest => rest.val = [] ⦄ := by
  obtain ⟨e, he⟩ := hE
  unfold binlog.misc.read_eof
  step*
  simp [he, s_post]

set_option hygiene false in
/-- The shape of every `read_*` helper: a checked read, or `read_eof` on a short input. -/
local macro "read_tac " sp:term:max hE:term:max : tactic => `(tactic| (
  step with $sp as ⟨o, input1, ho⟩
  split_ifs at ho with hl
  · obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
    simp only [Option.map_some, Option.some.injEq] at ho
    simp [okPart, hl, ho]
  · obtain ⟨rfl, rfl⟩ := ho
    simp only
    step with read_eof_spec _ (($hE).resolve_left hl) as ⟨e, input2, h2⟩
    simp [okPart, hl, h2]))

theorem beNat_take1 (l : List U8) : beNat (l.take 1) = leNat (l.take 1) := by
  cases l <;> simp [beNat]

theorem read_u8_spec (input : io.ParseBuf) (hE : 1 ≤ input.length ∨ EofOk) :
    binlog.misc.read_u8 input ⦃ r rest =>
      if 1 ≤ input.length then (okPart r).map (·.val) = some (leNat (input.val.take 1)) ∧ rest.val = input.val.drop 1
      else okPart r = none ∧ rest.val = [] ⦄ := by
  unfold binlog.misc.read_u8; read_tac (io.ParseBuf.checked_eat_u8_spec input) hE

theorem read_i8_spec (input : io.ParseBuf) (hE : 1 ≤ input.length ∨ EofOk) :
    binlog.misc.read_i8 input ⦃ r rest =>
      if 1 ≤ input.length then (okPart r).map (·.val) = some (toSigned 8 (leNat (input.val.take 1))) ∧ rest.val = input.val.drop 1
      else okPart r = none ∧ rest.val = [] ⦄ := by
  unfold binlog.misc.read_i8; read_tac (io.ParseBuf.checked_eat_i8_spec input) hE

theorem read_u16_be_spec (input : io.ParseBuf) (hE : 2 ≤ input.length ∨ EofOk) :
    binlog.misc.read_u16_be input ⦃ r rest =>
      if 2 ≤ input.length then (okPart r).map (·.val) = some (beNat (input.val.take 2)) ∧ rest.val = input.val.drop 2
      else okPart r = none ∧ rest.val = [] ⦄ := by
  unfold binlog.misc.read_u16_be; read_tac (io.ParseBuf.checked_eat_u16_be_spec input) hE

theorem read_i16_be_spec (input : io.ParseBuf) (hE : 2 ≤ input.length ∨ EofOk) :
    binlog.misc.read_i16_be input ⦃ r rest =>
      if 2 ≤ input.length then (okPart r).map (·.val) = some (toSigned 16 (beNat (input.val.take 2))) ∧ rest.val = input.val.drop 2
      else okPart r = none ∧ rest.val = [] ⦄ := by
  unfold binlog.misc.read_i16_be; read_tac (io.ParseBuf.checked_eat_i16_be_spec input) hE

theorem read_u24_be_spec (input : io.ParseBuf) (hE : 3 ≤ input.length ∨ EofOk) :
    binlog.misc.read_u24_be input ⦃ r rest =>
      if 3 ≤ input.length then (okPart r).map (·.val) = some (beNat (input.val.take 3)) ∧ rest.val = input.val.drop 3
      else okPart r = none ∧ rest.val = [] ⦄ := by
  unfold binlog.misc.read_u24_be; read_tac (io.ParseBuf.checked_eat_u24_be_spec input) hE

theorem read_u32_be_spec (input : io.ParseBuf) (hE : 4 ≤ input.length ∨ EofOk) :
    binlog.misc.read_u32_be input ⦃ r rest =>
      if 4 ≤ input.length then (okPart r).map (·.val) = some (beNat (input.val.take 4)) ∧ rest.val = input.val.drop 4
      else okPart r = none ∧ rest.val = [] ⦄ := by
  unfold binlog.misc.read_u32_be; read_tac (io.ParseBuf.checked_eat_u32_be_spec input) hE

theorem read_u40_be_spec (input : io.ParseBuf) (hE : 5 ≤ input.length ∨ EofOk) :
    binlog.misc.read_u40_be input ⦃ r rest =>
      if 5 ≤ input.length then (okPart r).map (·.val) = some (beNat (input.val.take 5)) ∧ rest.val = input.val.drop 5
      else okPart r = none ∧ rest.val = [] ⦄ := by
  unfold binlog.misc.read_u40_be; read_tac (io.ParseBuf.checked_eat_u40_be_spec input) hE

theorem read_u48_be_spec (input : io.ParseBuf) (hE : 6 ≤ input.length ∨ EofOk) :
    binlog.misc.read_u48_be input ⦃ r rest =>
      if 6 ≤ input.length then (okPart r).map (·.val) = some (beNat (input.val.take 6)) ∧ rest.val = input.val.drop 6
      else okPart r = none ∧ rest.val = [] ⦄ := by
  unfold binlog.misc.read_u48_be; read_tac (io.ParseBuf.checked_eat_u48_be_spec input) hE

theorem read_i24_be_spec (input : io.ParseBuf) (hE : 3 ≤ input.length ∨ EofOk) :
    binlog.misc.read_i24_be input ⦃ r rest =>
      if 3 ≤ input.length then (okPart r).map (·.val) = some (toSigned 24 (beNat (input.val.take 3))) ∧ rest.val = input.val.drop 3
      else okPart r = none ∧ rest.val = [] ⦄ := by
  unfold binlog.misc.read_i24_be
  step with io.ParseBuf.checked_eat_u24_be_spec input as ⟨o, input1, ho⟩
  split_ifs at ho with hl
  · obtain ⟨x, rfl⟩ : ∃ x, o = some x := by cases o <;> simp_all
    simp only [Option.map_some, Option.some.injEq] at ho
    simp only
    step*
    have hx : x.val < 2^24 := by
      have := PBUtil.leNat_lt (List.take 3 input.val).reverse
      rw [ho.1, beNat]; simp only [List.length_reverse, List.length_take] at this
      have : 2 ^ (8 * min 3 input.val.length) ≤ 2^24 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    simp only [hl, ite_true, okPart, Option.map_some, Option.some.injEq, ho.2, and_true]
    rw [i2_post, i1_post, UScalar.hcast_val_eq, i_post, Int.shiftRight_eq_div_pow, ← ho.1]
    simp only [U32.size, U32.numBits, UScalarTy.numBits, IScalarTy.numBits, Nat.shiftLeft_eq, toSigned]
    have : (x.val * 2^8 % 2^32 : Nat) = x.val * 2^8 := Nat.mod_eq_of_lt (by omega)
    rw [this]
    unfold Int.bmod
    have h2 : ((x.val * 2^8 : Nat) : Int) % ((2^32 : Nat) : Int) = ((x.val * 2^8 : Nat) : Int) :=
      Int.emod_eq_of_lt (by omega) (by omega)
    simp only [h2]
    split_ifs <;> push_cast at * <;> omega
  · obtain ⟨rfl, rfl⟩ := ho
    simp only
    step with read_eof_spec _ (hE.resolve_left hl) as ⟨e, input2, h2⟩
    simp [okPart, hl, h2]


theorem ok_of_spec {α : Type} {m : Result (core.result.Result α core.io.error.Error × io.ParseBuf)}
    {V : α → Int} {v : Int} {t : List U8}
    (h : m ⦃ r rest => (okPart r).map V = some v ∧ rest.val = t ⦄) :
    ∃ y rest, m = ok (.Ok y, rest) ∧ V y = v ∧ rest.val = t := by
  obtain ⟨⟨r, rest⟩, hm, h1, h2⟩ := PBUtil.spec_eq_ok h
  cases r with
  | Ok y => exact ⟨y, rest, hm, by simpa [okPart] using h1, h2⟩
  | Err e => simp [okPart] at h1

theorem ok_of_spec_nat {α : Type} {m : Result (core.result.Result α core.io.error.Error × io.ParseBuf)}
    {V : α → Nat} {v : Nat} {t : List U8}
    (h : m ⦃ r rest => (okPart r).map V = some v ∧ rest.val = t ⦄) :
    ∃ y rest, m = ok (.Ok y, rest) ∧ V y = v ∧ rest.val = t := by
  obtain ⟨⟨r, rest⟩, hm, h1, h2⟩ := PBUtil.spec_eq_ok h
  cases r with
  | Ok y => exact ⟨y, rest, hm, by simpa [okPart] using h1, h2⟩
  | Err e => simp [okPart] at h1

theorem read_u8_ok (input : io.ParseBuf) (h : 1 ≤ input.length) :
    ∃ y rest, binlog.misc.read_u8 input = ok (.Ok y, rest) ∧ y.val = leNat (input.val.take 1) ∧ rest.val = input.val.drop 1 :=
  ok_of_spec_nat (WP.spec_mono (read_u8_spec input (Or.inl h)) (fun _ hh => by simpa [h] using hh))
theorem read_i8_ok (input : io.ParseBuf) (h : 1 ≤ input.length) :
    ∃ y rest, binlog.misc.read_i8 input = ok (.Ok y, rest) ∧ y.val = toSigned 8 (leNat (input.val.take 1)) ∧ rest.val = input.val.drop 1 :=
  ok_of_spec (WP.spec_mono (read_i8_spec input (Or.inl h)) (fun _ hh => by simpa [h] using hh))
theorem read_u16_be_ok (input : io.ParseBuf) (h : 2 ≤ input.length) :
    ∃ y rest, binlog.misc.read_u16_be input = ok (.Ok y, rest) ∧ y.val = beNat (input.val.take 2) ∧ rest.val = input.val.drop 2 :=
  ok_of_spec_nat (WP.spec_mono (read_u16_be_spec input (Or.inl h)) (fun _ hh => by simpa [h] using hh))
theorem read_i16_be_ok (input : io.ParseBuf) (h : 2 ≤ input.length) :
    ∃ y rest, binlog.misc.read_i16_be input = ok (.Ok y, rest) ∧ y.val = toSigned 16 (beNat (input.val.take 2)) ∧ rest.val = input.val.drop 2 :=
  ok_of_spec (WP.spec_mono (read_i16_be_spec input (Or.inl h)) (fun _ hh => by simpa [h] using hh))
theorem read_u24_be_ok (input : io.ParseBuf) (h : 3 ≤ input.length) :
    ∃ y rest, binlog.misc.read_u24_be input = ok (.Ok y, rest) ∧ y.val = beNat (input.val.take 3) ∧ rest.val = input.val.drop 3 :=
  ok_of_spec_nat (WP.spec_mono (read_u24_be_spec input (Or.inl h)) (fun _ hh => by simpa [h] using hh))
theorem read_i24_be_ok (input : io.ParseBuf) (h : 3 ≤ input.length) :
    ∃ y rest, binlog.misc.read_i24_be input = ok (.Ok y, rest) ∧ y.val = toSigned 24 (beNat (input.val.take 3)) ∧ rest.val = input.val.drop 3 :=
  ok_of_spec (WP.spec_mono (read_i24_be_spec input (Or.inl h)) (fun _ hh => by simpa [h] using hh))
theorem read_u32_be_ok (input : io.ParseBuf) (h : 4 ≤ input.length) :
    ∃ y rest, binlog.misc.read_u32_be input = ok (.Ok y, rest) ∧ y.val = beNat (input.val.take 4) ∧ rest.val = input.val.drop 4 :=
  ok_of_spec_nat (WP.spec_mono (read_u32_be_spec input (Or.inl h)) (fun _ hh => by simpa [h] using hh))
theorem read_u40_be_ok (input : io.ParseBuf) (h : 5 ≤ input.length) :
    ∃ y rest, binlog.misc.read_u40_be input = ok (.Ok y, rest) ∧ y.val = beNat (input.val.take 5) ∧ rest.val = input.val.drop 5 :=
  ok_of_spec_nat (WP.spec_mono (read_u40_be_spec input (Or.inl h)) (fun _ hh => by simpa [h] using hh))
theorem read_u48_be_ok (input : io.ParseBuf) (h : 6 ≤ input.length) :
    ∃ y rest, binlog.misc.read_u48_be input = ok (.Ok y, rest) ∧ y.val = beNat (input.val.take 6) ∧ rest.val = input.val.drop 6 :=
  ok_of_spec_nat (WP.spec_mono (read_u48_be_spec input (Or.inl h)) (fun _ hh => by simpa [h] using hh))


theorem hcast32_toSigned (x : U32) : (UScalar.hcast .I32 x).val = toSigned 32 x.val := by
  rw [UScalar.hcast_val_eq]
  have := x.hBounds
  simp only [IScalarTy.numBits, toSigned]
  unfold Int.bmod
  have h2 : ((x.val : Int) % ((2^32 : Nat) : Int)) = x.val := Int.emod_eq_of_lt (by omega) (by simp at this ⊢; omega)
  simp only [h2]
  split_ifs <;> simp at this <;> omega

theorem okS {α β : Type} {m : Result (core.result.Result α core.io.error.Error × io.ParseBuf)}
    {V : α → β} {v : β} {t : List U8}
    (h : ∃ y rest, m = ok (.Ok y, rest) ∧ V y = v ∧ rest.val = t) :
    m ⦃ r rest => ∃ y, r = .Ok y ∧ V y = v ∧ rest.val = t ⦄ := by
  obtain ⟨y, rest, hm, h1, h2⟩ := h
  rw [hm]; simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨y, rfl, h1, h2⟩

theorem timestamp_ok (input : io.ParseBuf) (dec : U8) (hl : 4 + fracBytes dec.val ≤ input.length) :
    binlog.misc.my_timestamp_from_binary input dec ⦃ r rest =>
      ∃ sec usec : I32, r = .Ok (sec, usec) ∧
        timestamp2Read dec.val input.val = some ((sec.val, usec.val), rest.val) ⦄ := by
  unfold binlog.misc.my_timestamp_from_binary
  step with okS (read_u32_be_ok input (by unfold fracBytes at hl; split_ifs at hl <;> omega)) as ⟨r, in1, x, hr, hx, hin1⟩
  subst hr
  have hlen1 : in1.length = input.length - 4 := by simp [Slice.length, hin1]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift]
  have hsec : (UScalar.hcast .I32 x).val = toSigned 32 (beNat (input.val.take 4)) := by rw [hcast32_toSigned, hx]
  split
  case h_1 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl ⊢
    norm_num [fracBytes] at hl
    step with okS (read_i8_ok in1 (by simp only [Slice.length] at *; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    step*
    refine ⟨_, _, rfl, ?_⟩
    have hc : (IScalar.cast IScalarTy.I32 y).val = y.val := by simp [IScalar.cast_val_eq]
    rw [usec_post, hc]
    simp only [timestamp2Read, fracBytes, temporalFracRead, BitVec.toNat_ofNat, hsec, hy, hin2, hin1, List.drop_drop]
    norm_num
    try simp only [beNat_take1]
    first | exact ⟨hl, trivial⟩ | exact hl
  case h_2 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl ⊢
    norm_num [fracBytes] at hl
    step with okS (read_i8_ok in1 (by simp only [Slice.length] at *; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    step*
    refine ⟨_, _, rfl, ?_⟩
    have hc : (IScalar.cast IScalarTy.I32 y).val = y.val := by simp [IScalar.cast_val_eq]
    rw [usec_post, hc]
    simp only [timestamp2Read, fracBytes, temporalFracRead, BitVec.toNat_ofNat, hsec, hy, hin2, hin1, List.drop_drop]
    norm_num
    try simp only [beNat_take1]
    first | exact ⟨hl, trivial⟩ | exact hl
  case h_3 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl ⊢
    norm_num [fracBytes] at hl
    step with okS (read_i16_be_ok in1 (by simp only [Slice.length] at *; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    step*
    refine ⟨_, _, rfl, ?_⟩
    have hc : (IScalar.cast IScalarTy.I32 y).val = y.val := by simp [IScalar.cast_val_eq]
    rw [usec_post, hc]
    simp only [timestamp2Read, fracBytes, temporalFracRead, BitVec.toNat_ofNat, hsec, hy, hin2, hin1, List.drop_drop]
    norm_num
    try simp only [beNat_take1]
    first | exact ⟨hl, trivial⟩ | exact hl
  case h_4 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl ⊢
    norm_num [fracBytes] at hl
    step with okS (read_i16_be_ok in1 (by simp only [Slice.length] at *; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    step*
    refine ⟨_, _, rfl, ?_⟩
    have hc : (IScalar.cast IScalarTy.I32 y).val = y.val := by simp [IScalar.cast_val_eq]
    rw [usec_post, hc]
    simp only [timestamp2Read, fracBytes, temporalFracRead, BitVec.toNat_ofNat, hsec, hy, hin2, hin1, List.drop_drop]
    norm_num
    try simp only [beNat_take1]
    first | exact ⟨hl, trivial⟩ | exact hl
  case h_5 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl ⊢
    norm_num [fracBytes] at hl
    step with okS (read_i24_be_ok in1 (by simp only [Slice.length] at *; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    step*
    refine ⟨_, _, rfl, ?_⟩
    simp only [timestamp2Read, fracBytes, temporalFracRead, BitVec.toNat_ofNat, hsec, hy, hin2, hin1, List.drop_drop]
    norm_num
    try simp only [beNat_take1]
    first | exact ⟨hl, trivial⟩ | exact hl
  case h_6 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl ⊢
    norm_num [fracBytes] at hl
    step with okS (read_i24_be_ok in1 (by simp only [Slice.length] at *; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    step*
    refine ⟨_, _, rfl, ?_⟩
    simp only [timestamp2Read, fracBytes, temporalFracRead, BitVec.toNat_ofNat, hsec, hy, hin2, hin1, List.drop_drop]
    norm_num
    try simp only [beNat_take1]
    first | exact ⟨hl, trivial⟩ | exact hl
  case h_7 h1 h2 h3 h4 h5 h6 =>
    have hd : ¬(dec.val = 1 ∨ dec.val = 2 ∨ dec.val = 3 ∨ dec.val = 4 ∨ dec.val = 5 ∨ dec.val = 6) := by
      intro hd
      rcases hd with hd | hd | hd | hd | hd | hd
      · exact h1 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h2 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h3 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h4 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h5 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h6 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
    simp only [WP.spec_ok, WP.uncurry'_pair]
    refine ⟨_, _, rfl, ?_⟩
    have hf : fracBytes dec.val = 0 := by unfold fracBytes; split_ifs <;> omega
    have ht : temporalFracRead dec.val [] = 0 := by unfold temporalFracRead; split_ifs <;> omega
    simp only [timestamp2Read, hf, hsec, hin1, List.take_zero, ht]
    simp only [Slice.length] at hl
    norm_num
    omega

end mysql_common.BinlogUtil

namespace Defs

theorem timeFromPacked_timePack' (neg : Bool) (d h m s us : Nat)
    (hr : h < 24 ∧ m < 60 ∧ s < 60 ∧ d * 24 + h < 1024 ∧ us < 2 ^ 24)
    (hz : ¬(neg = true ∧ d = 0 ∧ h = 0 ∧ m = 0 ∧ s = 0 ∧ us = 0)) :
    timeFromPacked (timePack neg d h m s us) = .time neg d h m s us := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hr
  have hA : packedMake (((d * 24 + h) * 2 ^ 12 + m * 2 ^ 6 + s : Nat) : Int) (us : Int) =
      ((((d * 24 + h) * 2 ^ 12 + m * 2 ^ 6 + s) * 2 ^ 24 + us : Nat) : Int) := by
    unfold packedMake; push_cast; ring
  obtain ⟨A, hAd⟩ : ∃ A, ((d * 24 + h) * 2 ^ 12 + m * 2 ^ 6 + s) * 2 ^ 24 + us = A := ⟨_, rfl⟩
  rw [hAd] at hA
  have key : A / 2 ^ 24 / 2 ^ 12 % 2 ^ 10 / 24 = d ∧ A / 2 ^ 24 / 2 ^ 12 % 2 ^ 10 % 24 = h ∧
      A / 2 ^ 24 / 2 ^ 6 % 2 ^ 6 = m ∧ A / 2 ^ 24 % 2 ^ 6 = s ∧ A % 2 ^ 24 = us := by
    subst hAd; simp only [Nat.reducePow]; omega
  unfold timeFromPacked timePack
  simp only [hA]
  cases neg
  · simp only [Bool.false_eq_true, ite_false, Int.natAbs_natCast, Val.time.injEq]
    exact ⟨by simp, key⟩
  · simp only [ite_true, Int.natAbs_neg, Int.natAbs_natCast, Val.time.injEq]
    refine ⟨?_, key⟩
    simp only [true_and] at hz
    simp only [decide_eq_true_eq]
    have : 0 < A := by subst hAd; simp only [Nat.reducePow]; omega
    omega

theorem datetimeFromPacked_datetimePack' (y mo d h mi s us : Nat)
    (hr : y ≤ 9999 ∧ mo ≤ 12 ∧ d < 32 ∧ h < 24 ∧ mi < 60 ∧ s < 60 ∧ us < 2 ^ 24) :
    datetimeFromPacked (datetimePack y mo d h mi s us) = .date y mo d h mi s us := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
  have hA : datetimePack y mo d h mi s us =
      (((((y * 13 + mo) * 2 ^ 5 + d) * 2 ^ 17 + (h * 2 ^ 12 + mi * 2 ^ 6 + s)) * 2 ^ 24 + us : Nat) : Int) := by
    unfold datetimePack packedMake; push_cast; ring
  obtain ⟨A, hAd⟩ : ∃ A, (((y * 13 + mo) * 2 ^ 5 + d) * 2 ^ 17 + (h * 2 ^ 12 + mi * 2 ^ 6 + s)) * 2 ^ 24 + us = A := ⟨_, rfl⟩
  rw [hAd] at hA
  rw [hA]
  unfold datetimeFromPacked
  simp only [Int.natAbs_natCast, Val.date.injEq]
  subst hAd; simp only [Nat.reducePow]; omega

@[simp] theorem length_beBytesI' (k : Nat) (x : Int) : (beBytesI k x).length = k := by
  simp [beBytesI]

theorem beNat_beBytesI (k : Nat) (x : Int) : beNat (beBytesI k x) = (x % (2 ^ (8 * k) : Int)).toNat := by
  simp [beNat, beBytesI, IntAndMisc.leNat_leBytesI]

theorem packed_facts (p : Int) :
    (0 ≤ p → 0 ≤ packedFracPart p ∧ packedFracPart p < 2 ^ 24 ∧ p = packedIntPart p * 2 ^ 24 + packedFracPart p) ∧
    (p < 0 → -2 ^ 24 < packedFracPart p ∧ packedFracPart p ≤ 0 ∧
      (packedFracPart p = 0 → p = packedIntPart p * 2 ^ 24) ∧
      (packedFracPart p ≠ 0 → p = (packedIntPart p + 1) * 2 ^ 24 + packedFracPart p)) := by
  unfold packedFracPart packedIntPart
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by norm_num), Int.tmod_eq_emod]
  simp only [Int.dvd_iff_emod_eq_zero]
  split_ifs <;> simp <;> omega

theorem time2Read_time2Bin' (dec : Nat) (p : Int) (tail : List U8) (hp : -2 ^ 47 ≤ p ∧ p < 2 ^ 47)
    (hf : packedFracPart p % (fracUnit dec : Int) = 0 ∧ (packedFracPart p).natAbs < 10 ^ 6) :
    time2Read dec (time2Bin dec p ++ tail) = some (p, tail) := by
  have hPF := packed_facts p
  unfold time2Read time2Bin fracUnit fracBytes at *
  by_cases h12 : dec = 1 ∨ dec = 2
  · simp only [h12, ite_true] at hf ⊢
    rw [List.append_assoc]
    have h1 : List.take 3 (beBytesI 3 (packedIntPart p + 8388608) ++ (beBytesI 1 ((packedFracPart p).tdiv 10000) ++ tail)) = beBytesI 3 (packedIntPart p + 8388608) := List.take_left' (by simp)
    have h2 : List.drop 3 (beBytesI 3 (packedIntPart p + 8388608) ++ (beBytesI 1 ((packedFracPart p).tdiv 10000) ++ tail)) = beBytesI 1 ((packedFracPart p).tdiv 10000) ++ tail := List.drop_left' (by simp)
    have h3 : List.take 1 (beBytesI 1 ((packedFracPart p).tdiv 10000) ++ tail) = beBytesI 1 ((packedFracPart p).tdiv 10000) := List.take_left' (by simp)
    have h4 : List.drop (3 + 1) (beBytesI 3 (packedIntPart p + 8388608) ++ (beBytesI 1 ((packedFracPart p).tdiv 10000) ++ tail)) = tail := by
      rw [← List.drop_drop, h2]; exact List.drop_left' (by simp)
    simp only [h1, h2, h3, h4, beNat_beBytesI, List.length_append, length_beBytesI']
    rw [Int.tdiv_eq_ediv_of_dvd (Int.dvd_of_emod_eq_zero (by exact_mod_cast hf.1))]
    have hq := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero (by exact_mod_cast hf.1) : (10000:Int) ∣ packedFracPart p)
    obtain ⟨hf1, hf2⟩ := hf
    generalize packedIntPart p = I at *
    generalize packedFracPart p = F at *
    unfold packedMake
    simp only [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (2:Int)^(8*3) ≠ 0)), Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (2:Int)^(8*1) ≠ 0))]
    norm_num at hf1 ⊢
    refine ⟨by omega, ?_⟩
    by_cases hpn : p < 0
    · obtain ⟨a1, a2, a3, a4⟩ := hPF.2 hpn
      by_cases hF0 : F = 0
      · have := a3 hF0; split_ifs <;> omega
      · have := a4 hF0
        have hI : (I + 8388608) / 16777216 = 0 := by omega
        have hd : F / 10000 / 256 = -1 := by omega
        split_ifs <;> omega
    · obtain ⟨a1, a2, a3⟩ := hPF.1 (by omega)
      have hI : (I + 8388608) / 16777216 = 0 := by omega
      have hd : F / 10000 / 256 = 0 := by omega
      split_ifs <;> omega
  · by_cases h34 : dec = 3 ∨ dec = 4
    · simp only [h12, h34, ite_true, ite_false] at hf ⊢
      rw [List.append_assoc]
      have h1 : List.take 3 (beBytesI 3 (packedIntPart p + 8388608) ++ (beBytesI 2 ((packedFracPart p).tdiv 100) ++ tail)) = beBytesI 3 (packedIntPart p + 8388608) := List.take_left' (by simp)
      have h2 : List.drop 3 (beBytesI 3 (packedIntPart p + 8388608) ++ (beBytesI 2 ((packedFracPart p).tdiv 100) ++ tail)) = beBytesI 2 ((packedFracPart p).tdiv 100) ++ tail := List.drop_left' (by simp)
      have h3 : List.take 2 (beBytesI 2 ((packedFracPart p).tdiv 100) ++ tail) = beBytesI 2 ((packedFracPart p).tdiv 100) := List.take_left' (by simp)
      have h4 : List.drop (3 + 2) (beBytesI 3 (packedIntPart p + 8388608) ++ (beBytesI 2 ((packedFracPart p).tdiv 100) ++ tail)) = tail := by
        rw [← List.drop_drop, h2]; exact List.drop_left' (by simp)
      simp only [h1, h2, h3, h4, beNat_beBytesI, List.length_append, length_beBytesI']
      rw [Int.tdiv_eq_ediv_of_dvd (Int.dvd_of_emod_eq_zero (by exact_mod_cast hf.1))]
      have hq := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero (by exact_mod_cast hf.1) : (100:Int) ∣ packedFracPart p)
      obtain ⟨hf1, hf2⟩ := hf
      generalize packedIntPart p = I at *
      generalize packedFracPart p = F at *
      unfold packedMake
      simp only [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (2:Int)^(8*3) ≠ 0)), Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (2:Int)^(8*2) ≠ 0))]
      norm_num at hf1 ⊢
      refine ⟨by omega, ?_⟩
      by_cases hpn : p < 0
      · obtain ⟨a1, a2, a3, a4⟩ := hPF.2 hpn
        by_cases hF0 : F = 0
        · have := a3 hF0; split_ifs <;> omega
        · have := a4 hF0
          have hI : (I + 8388608) / 16777216 = 0 := by omega
          have hd : F / 100 / 65536 = -1 := by omega
          split_ifs <;> omega
      · obtain ⟨a1, a2, a3⟩ := hPF.1 (by omega)
        have hI : (I + 8388608) / 16777216 = 0 := by omega
        have hd : F / 100 / 65536 = 0 := by omega
        split_ifs <;> omega
    · by_cases h56 : dec = 5 ∨ dec = 6
      · simp only [h12, h34, h56, ite_true, ite_false] at hf ⊢
        have h4 : List.take 6 (beBytesI 6 (p + 140737488355328) ++ tail) = beBytesI 6 (p + 140737488355328) := List.take_left' (by simp)
        have h5 : List.drop (3 + 3) (beBytesI 6 (p + 140737488355328) ++ tail) = tail := List.drop_left' (by simp)
        simp only [h4, h5, beNat_beBytesI, List.length_append, length_beBytesI']
        simp only [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (2:Int)^(8*6) ≠ 0))]
        norm_num
        omega
      · simp only [h12, h34, h56, ite_true, ite_false] at hf ⊢
        have h4 : List.take 3 (beBytesI 3 (packedIntPart p + 8388608) ++ tail) = beBytesI 3 (packedIntPart p + 8388608) := List.take_left' (by simp)
        have h5 : List.drop (3 + 0) (beBytesI 3 (packedIntPart p + 8388608) ++ tail) = tail := List.drop_left' (by simp)
        simp only [h4, h5, beNat_beBytesI, List.length_append, length_beBytesI']
        obtain ⟨hf1, hf2⟩ := hf
        generalize packedIntPart p = I at *
        generalize packedFracPart p = F at *
        unfold packedMake
        simp only [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (2:Int)^(8*3) ≠ 0))]
        norm_num at hf1 ⊢
        have hF : F = 0 := by omega
        by_cases hpn : p < 0
        · obtain ⟨a1, a2, a3, a4⟩ := hPF.2 hpn
          have := a3 hF
          have hI : (I + 8388608) / 16777216 = 0 := by omega
          omega
        · obtain ⟨a1, a2, a3⟩ := hPF.1 (by omega)
          have hI : (I + 8388608) / 16777216 = 0 := by omega
          omega

theorem length_temporalFracBin (dec : Nat) (f : Int) : (temporalFracBin dec f).length = fracBytes dec := by
  unfold temporalFracBin fracBytes; split_ifs <;> simp

theorem temporalFracRead_temporalFracBin (dec : Nat) (f : Int)
    (hf : f % (fracUnit dec : Int) = 0 ∧ f.natAbs < 10 ^ 6) :
    temporalFracRead dec (temporalFracBin dec f) = f := by
  obtain ⟨hf1, hf2⟩ := hf
  unfold temporalFracRead temporalFracBin fracUnit at *
  by_cases h12 : dec = 1 ∨ dec = 2
  · simp only [h12, ite_true] at hf1 ⊢
    rw [Int.tdiv_eq_ediv_of_dvd (Int.dvd_of_emod_eq_zero (by exact_mod_cast hf1)), beNat_beBytesI, toSigned]
    simp only [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (2:Int)^(8*1) ≠ 0))]
    norm_num at hf1 ⊢
    split_ifs <;> omega
  · by_cases h34 : dec = 3 ∨ dec = 4
    · simp only [h12, h34, ite_true, ite_false] at hf1 ⊢
      rw [Int.tdiv_eq_ediv_of_dvd (Int.dvd_of_emod_eq_zero (by exact_mod_cast hf1)), beNat_beBytesI, toSigned]
      simp only [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (2:Int)^(8*2) ≠ 0))]
      norm_num at hf1 ⊢
      split_ifs <;> omega
    · by_cases h56 : dec = 5 ∨ dec = 6
      · simp only [h12, h34, h56, ite_true, ite_false] at hf1 ⊢
        rw [beNat_beBytesI, toSigned]
        simp only [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (2:Int)^(8*3) ≠ 0))]
        norm_num
        split_ifs <;> omega
      · simp only [h12, h34, h56, ite_false] at hf1 ⊢
        norm_num at hf1
        omega

theorem datetime2Read_datetime2Bin' (dec : Nat) (p : Int) (tail : List U8) (hp : 0 ≤ p ∧ p < 2 ^ 63)
    (hf : packedFracPart p % (fracUnit dec : Int) = 0 ∧ packedFracPart p < 10 ^ 6) :
    datetime2Read dec (datetime2Bin dec p ++ tail) = some (p, tail) := by
  have hPF := (packed_facts p).1 hp.1
  have hfr := temporalFracRead_temporalFracBin dec (packedFracPart p) ⟨hf.1, by omega⟩
  have hlf := length_temporalFracBin dec (packedFracPart p)
  unfold datetime2Read datetime2Bin
  rw [List.append_assoc]
  have h1 : List.take 5 (beBytesI 5 (packedIntPart p + 549755813888) ++ (temporalFracBin dec (packedFracPart p) ++ tail)) = beBytesI 5 (packedIntPart p + 549755813888) := List.take_left' (by simp)
  have h2 : List.drop 5 (beBytesI 5 (packedIntPart p + 549755813888) ++ (temporalFracBin dec (packedFracPart p) ++ tail)) = temporalFracBin dec (packedFracPart p) ++ tail := List.drop_left' (by simp)
  have h3 : List.take (fracBytes dec) (temporalFracBin dec (packedFracPart p) ++ tail) = temporalFracBin dec (packedFracPart p) := List.take_left' hlf
  have h4 : List.drop (5 + fracBytes dec) (beBytesI 5 (packedIntPart p + 549755813888) ++ (temporalFracBin dec (packedFracPart p) ++ tail)) = tail := by
    rw [← List.drop_drop, h2]; exact List.drop_left' hlf
  simp only [h1, h2, h3, h4, hfr, beNat_beBytesI, List.length_append, length_beBytesI', hlf]
  generalize packedIntPart p = I at *
  generalize packedFracPart p = F at *
  unfold packedMake
  simp only [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (2:Int)^(8*5) ≠ 0))]
  norm_num
  have hI : (I + 549755813888) / 1099511627776 = 0 := by omega
  omega

theorem timestamp2Read_timestamp2Bin' (dec sec usec : Nat) (tail : List U8) (hs : sec < 2 ^ 31)
    (hu : usec < 10 ^ 6 ∧ usec % fracUnit dec = 0) :
    timestamp2Read dec (timestamp2Bin dec sec usec ++ tail) = some (((sec : Int), (usec : Int)), tail) := by
  have hfr := temporalFracRead_temporalFracBin dec (usec : Int) ⟨by exact_mod_cast hu.2, by omega⟩
  have hlf := length_temporalFracBin dec (usec : Int)
  have hlb : (beBytes 4 sec).length = 4 := by simp [beBytes, PBUtil.length_leBytes]
  unfold timestamp2Read timestamp2Bin
  rw [List.append_assoc]
  have h1 : List.take 4 (beBytes 4 sec ++ (temporalFracBin dec usec ++ tail)) = beBytes 4 sec := List.take_left' hlb
  have h2 : List.drop 4 (beBytes 4 sec ++ (temporalFracBin dec usec ++ tail)) = temporalFracBin dec usec ++ tail := List.drop_left' hlb
  have h3 : List.take (fracBytes dec) (temporalFracBin dec usec ++ tail) = temporalFracBin dec usec := List.take_left' hlf
  have h4 : List.drop (4 + fracBytes dec) (beBytes 4 sec ++ (temporalFracBin dec usec ++ tail)) = tail := by
    rw [← List.drop_drop, h2]; exact List.drop_left' hlf
  have hb : beNat (beBytes 4 sec) = sec := by
    simp only [beNat, beBytes, List.reverse_reverse, PBUtil.leNat_leBytes]; omega
  simp only [h1, h2, h3, h4, hfr, hb, List.length_append, hlb, hlf, toSigned]
  norm_num
  omega

theorem time2NegFracBug_time2Bin' (dec : Nat) (p : Int) (tail : List U8) (hd : dec = 1 ∨ dec = 2)
    (hp : -2 ^ 47 ≤ p ∧ p < 2 ^ 47)
    (hf : packedFracPart p % (fracUnit dec : Int) = 0 ∧ (packedFracPart p).natAbs < 10 ^ 6) :
    time2NegFracBug dec (time2Bin dec p ++ tail) ↔ p < 0 ∧ packedFracPart p ≠ 0 := by
  have hPF := packed_facts p
  unfold time2NegFracBug time2Bin fracUnit at *
  simp only [hd, ite_true, true_and] at hf ⊢
  rw [List.append_assoc]
  have h1 : List.take 3 (beBytesI 3 (packedIntPart p + 8388608) ++ (beBytesI 1 ((packedFracPart p).tdiv 10000) ++ tail)) = beBytesI 3 (packedIntPart p + 8388608) := List.take_left' (by simp)
  have h2 : List.drop 3 (beBytesI 3 (packedIntPart p + 8388608) ++ (beBytesI 1 ((packedFracPart p).tdiv 10000) ++ tail)) = beBytesI 1 ((packedFracPart p).tdiv 10000) ++ tail := List.drop_left' (by simp)
  have h3 : List.take 1 (beBytesI 1 ((packedFracPart p).tdiv 10000) ++ tail) = beBytesI 1 ((packedFracPart p).tdiv 10000) := List.take_left' (by simp)
  simp only [h1, h2, h3, beNat_beBytesI, List.length_append, length_beBytesI']
  rw [Int.tdiv_eq_ediv_of_dvd (Int.dvd_of_emod_eq_zero (by exact_mod_cast hf.1))]
  have hq := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero (by exact_mod_cast hf.1) : (10000:Int) ∣ packedFracPart p)
  obtain ⟨hf1, hf2⟩ := hf
  generalize packedIntPart p = I at *
  generalize packedFracPart p = F at *
  norm_num at hf1 ⊢
  by_cases hpn : p < 0
  · obtain ⟨a1, a2, a3, a4⟩ := hPF.2 hpn
    by_cases hF0 : F = 0
    · have := a3 hF0
      have hI : (I + 8388608) / 16777216 = 0 := by omega
      omega
    · have := a4 hF0
      have hI : (I + 8388608) / 16777216 = 0 := by omega
      have hd : F / 10000 / 256 = -1 := by omega
      omega
  · obtain ⟨a1, a2, a3⟩ := hPF.1 (by omega)
    have hI : (I + 8388608) / 16777216 = 0 := by omega
    have hd : F / 10000 / 256 = 0 := by omega
    omega

end Defs

namespace Defs
open constants.ColumnType

theorem readLE_app (k : Nat) (bs tail : List U8) (hk : bs.length = k) :
    readLE k (bs ++ tail) = some (leNat bs, tail) := by
  subst hk; simp [readLE]

theorem checkedLenPrefixed_app (k : Nat) (s tail : List U8) (hs : s.length < 2 ^ (8 * k)) :
    checkedLenPrefixed k (leBytes k s.length ++ s ++ tail) = (some s, tail) := by
  unfold checkedLenPrefixed
  rw [List.append_assoc, readLE_app _ _ _ (PBUtil.length_leBytes _ _), PBUtil.leNat_leBytes,
    Nat.mod_eq_of_lt hs]
  simp

theorem binlogStr_app (k : Nat) (s tail : List U8) (hs : s.length < 2 ^ (8 * k)) :
    binlogStr k (leBytes k s.length ++ s ++ tail) = .ok (.bytes s) tail := by
  simp only [binlogStr]; rw [checkedLenPrefixed_app k s tail hs]

set_option hygiene false in
local macro "enc_intro" : tactic => `(tactic| (
  (try simp only at h) <;> (split_ifs at h with hc) <;> (simp only [reduceCtorEq, Option.some.injEq] at h) <;> subst h))

theorem u8_lt (b : U8) : b.val < 256 := by have := b.hBounds; simpa using this

theorem stringFieldLen_lt (b0 b1 : Nat) (h0 : 1 ≤ b0) (h1 : b1 < 256) : stringFieldLen b0 b1 < 1024 := by
  unfold stringFieldLen
  split_ifs
  · have ha : b0 &&& 48 < 64 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
    have hx : (b0 &&& 48) ^^^ 48 < 2 ^ 6 := Nat.xor_lt_two_pow ha (by norm_num)
    have hs : ((b0 &&& 48) ^^^ 48) <<< 4 < 2 ^ 10 := by rw [Nat.shiftLeft_eq]; omega
    exact Nat.or_lt_two_pow (by omega) hs
  · omega

theorem timePack_facts (neg : Bool) (d h m s us : Nat)
    (hr : h < 24 ∧ m < 60 ∧ s < 60 ∧ d * 24 + h < 1024 ∧ us < 10 ^ 6) :
    -2 ^ 47 ≤ timePack neg d h m s us ∧ timePack neg d h m s us < 2 ^ 47 ∧
      packedFracPart (timePack neg d h m s us) = (if neg then -(us : Int) else us) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hr
  unfold timePack packedMake packedFracPart
  obtain ⟨H, hH⟩ : ∃ H, (d * 24 + h) * 2 ^ 12 + m * 2 ^ 6 + s = H := ⟨_, rfl⟩
  have hHb : H < 2 ^ 22 := by subst hH; simp only [Nat.reducePow]; omega
  simp only [hH]
  rw [Int.tmod_eq_emod]
  simp only [Int.dvd_iff_emod_eq_zero]
  cases neg <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> split_ifs <;> push_cast at * <;> omega

theorem datetimePack_facts (y mo d h mi s us : Nat)
    (hr : y ≤ 9999 ∧ mo ≤ 12 ∧ d < 32 ∧ h < 24 ∧ mi < 60 ∧ s < 60 ∧ us < 10 ^ 6) :
    0 ≤ datetimePack y mo d h mi s us ∧ datetimePack y mo d h mi s us < 2 ^ 63 ∧
      packedFracPart (datetimePack y mo d h mi s us) = us := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
  unfold datetimePack packedMake packedFracPart
  obtain ⟨H, hH⟩ : ∃ H, ((y * 13 + mo) * 2 ^ 5 + d) * 2 ^ 17 + (h * 2 ^ 12 + mi * 2 ^ 6 + s) = H := ⟨_, rfl⟩
  have hHb : H < 2 ^ 39 := by subst hH; simp only [Nat.reducePow]; omega
  simp only [hH]
  rw [Int.tmod_eq_emod]
  simp only [Int.dvd_iff_emod_eq_zero]
  split_ifs <;> push_cast at * <;> omega

theorem binlogRead_binlogEnc' (ct : constants.ColumnType) (md : List U8) (uns : Bool) (v : Val)
    (bs tail : List U8) (h : binlogEnc ct md uns v = some bs) :
    binlogRead ct md uns (bs ++ tail) = .ok v tail := by
  unfold binlogEnc at h
  split_ifs at h with hm
  cases ct <;> cases v <;> simp only [reduceCtorEq] at h
  all_goals try (simp [binlogIntEnc] at h; done)
  case MYSQL_TYPE_TINY.int x =>
    unfold binlogIntEnc at h; enc_intro
    simp [binlogRead, binlogEffType, binlogMetaLen, BinlogOut.ofRead, binRead, isLenencStrType, readIntVal, binlogNum, readLE_app _ _ _ (IntAndMisc.length_leBytesI _ _), readLE_app _ _ _ (PBUtil.length_leBytes _ _), IntAndMisc.leNat_leBytesI, PBUtil.leNat_leBytes]
    rcases hc with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ <;> norm_num [toSigned] at hc ⊢ <;> (try split_ifs) <;> omega
  case MYSQL_TYPE_SHORT.int x =>
    unfold binlogIntEnc at h; enc_intro
    simp [binlogRead, binlogEffType, binlogMetaLen, BinlogOut.ofRead, binRead, isLenencStrType, readIntVal, binlogNum, readLE_app _ _ _ (IntAndMisc.length_leBytesI _ _), readLE_app _ _ _ (PBUtil.length_leBytes _ _), IntAndMisc.leNat_leBytesI, PBUtil.leNat_leBytes]
    rcases hc with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ <;> norm_num [toSigned] at hc ⊢ <;> (try split_ifs) <;> omega
  case MYSQL_TYPE_LONG.int x =>
    unfold binlogIntEnc at h; enc_intro
    simp [binlogRead, binlogEffType, binlogMetaLen, BinlogOut.ofRead, binRead, isLenencStrType, readIntVal, binlogNum, readLE_app _ _ _ (IntAndMisc.length_leBytesI _ _), readLE_app _ _ _ (PBUtil.length_leBytes _ _), IntAndMisc.leNat_leBytesI, PBUtil.leNat_leBytes]
    rcases hc with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ <;> norm_num [toSigned] at hc ⊢ <;> (try split_ifs) <;> omega
  case MYSQL_TYPE_LONGLONG.int x =>
    unfold binlogIntEnc at h; enc_intro
    simp [binlogRead, binlogEffType, binlogMetaLen, BinlogOut.ofRead, binRead, isLenencStrType, readIntVal, binlogNum, readLE_app _ _ _ (IntAndMisc.length_leBytesI _ _), readLE_app _ _ _ (PBUtil.length_leBytes _ _), IntAndMisc.leNat_leBytesI, PBUtil.leNat_leBytes]
    rcases hc with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ <;> norm_num [toSigned] at hc ⊢ <;> (try split_ifs) <;> (try simp only [Val.int.injEq, reduceCtorEq] at *) <;> omega
  case MYSQL_TYPE_INT24.int x =>
    unfold binlogIntEnc at h; enc_intro
    simp [binlogRead, binlogEffType, binlogMetaLen, BinlogOut.ofRead, binRead, isLenencStrType, readIntVal, binlogNum, readLE_app _ _ _ (IntAndMisc.length_leBytesI _ _), readLE_app _ _ _ (PBUtil.length_leBytes _ _), IntAndMisc.leNat_leBytesI, PBUtil.leNat_leBytes]
    rcases hc with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ <;> norm_num [toSigned] at hc ⊢ <;> (try split_ifs) <;> omega
  case MYSQL_TYPE_LONGLONG.uint x =>
    unfold binlogIntEnc at h; enc_intro
    simp [binlogRead, binlogEffType, binlogMetaLen, BinlogOut.ofRead, binRead, isLenencStrType, readIntVal, binlogNum, readLE_app _ _ _ (IntAndMisc.length_leBytesI _ _), readLE_app _ _ _ (PBUtil.length_leBytes _ _), IntAndMisc.leNat_leBytesI, PBUtil.leNat_leBytes]
    obtain ⟨-, rfl, h1, h2⟩ := hc
    have : ¬ x < 9223372036854775808 := by omega
    have h3 : x % 18446744073709551616 = x := Nat.mod_eq_of_lt (by omega)
    simp [h3, this]
  case MYSQL_TYPE_FLOAT.float b =>
    enc_intro
    simp [binlogRead, binlogEffType, binlogMetaLen, BinlogOut.ofRead, binRead, isLenencStrType, readIntVal, binlogNum, readLE_app _ _ _ (IntAndMisc.length_leBytesI _ _), readLE_app _ _ _ (PBUtil.length_leBytes _ _), IntAndMisc.leNat_leBytesI, PBUtil.leNat_leBytes]
    omega
  case MYSQL_TYPE_DOUBLE.double b =>
    enc_intro
    simp [binlogRead, binlogEffType, binlogMetaLen, BinlogOut.ofRead, binRead, isLenencStrType, readIntVal, binlogNum, readLE_app _ _ _ (IntAndMisc.length_leBytesI _ _), readLE_app _ _ _ (PBUtil.length_leBytes _ _), IntAndMisc.leNat_leBytesI, PBUtil.leNat_leBytes]
    omega
  case MYSQL_TYPE_TIMESTAMP.int x =>
    enc_intro
    simp [binlogRead, binlogEffType, binlogMetaLen, BinlogOut.ofRead, binRead, isLenencStrType, readIntVal, binlogNum, readLE_app _ _ _ (IntAndMisc.length_leBytesI _ _), readLE_app _ _ _ (PBUtil.length_leBytes _ _), IntAndMisc.leNat_leBytesI, PBUtil.leNat_leBytes]
    omega
  case MYSQL_TYPE_TINY_BLOB.bytes b =>
    enc_intro
    obtain ⟨h1, h2, h3⟩ := hc
    have hm' : ¬ md.length < 1 := by simpa [binlogMetaLen] using hm
    simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false, h1, h2, and_self, ite_true]
    exact binlogStr_app _ _ _ h3
  case MYSQL_TYPE_MEDIUM_BLOB.bytes b =>
    enc_intro
    obtain ⟨h1, h2, h3⟩ := hc
    have hm' : ¬ md.length < 1 := by simpa [binlogMetaLen] using hm
    simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false, h1, h2, and_self, ite_true]
    exact binlogStr_app _ _ _ h3
  case MYSQL_TYPE_LONG_BLOB.bytes b =>
    enc_intro
    obtain ⟨h1, h2, h3⟩ := hc
    have hm' : ¬ md.length < 1 := by simpa [binlogMetaLen] using hm
    simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false, h1, h2, and_self, ite_true]
    exact binlogStr_app _ _ _ h3
  case MYSQL_TYPE_BLOB.bytes b =>
    enc_intro
    obtain ⟨h1, h2, h3⟩ := hc
    have hm' : ¬ md.length < 1 := by simpa [binlogMetaLen] using hm
    simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false, h1, h2, and_self, ite_true]
    exact binlogStr_app _ _ _ h3
  case MYSQL_TYPE_GEOMETRY.bytes b =>
    enc_intro
    obtain ⟨h1, h2, h3⟩ := hc
    have hm' : ¬ md.length < 1 := by simpa [binlogMetaLen] using hm
    simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false, h1, h2, and_self, ite_true]
    exact binlogStr_app _ _ _ h3
  case MYSQL_TYPE_VECTOR.bytes b =>
    enc_intro
    obtain ⟨h1, h2, h3⟩ := hc
    have hm' : ¬ md.length < 1 := by simpa [binlogMetaLen] using hm
    simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false, h1, h2, and_self, ite_true]
    exact binlogStr_app _ _ _ h3
  case MYSQL_TYPE_VARCHAR.bytes b =>
    enc_intro
    all_goals
      have hb0 := u8_lt (md.getD 0 (byte 0))
      have hb1 := u8_lt (md.getD 1 (byte 0))
      have hm' : ¬ md.length < 2 := by simpa [binlogMetaLen] using hm
      simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false]
      split_ifs <;> first | omega | exact binlogStr_app _ _ _ (by omega)
  case MYSQL_TYPE_VAR_STRING.bytes b =>
    enc_intro
    all_goals
      have hb0 := u8_lt (md.getD 0 (byte 0))
      have hb1 := u8_lt (md.getD 1 (byte 0))
      have hm' : ¬ md.length < 2 := by simpa [binlogMetaLen] using hm
      simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false]
      split_ifs <;> first | omega | exact binlogStr_app _ _ _ (by omega)
  case MYSQL_TYPE_STRING.bytes b =>
    enc_intro
    all_goals
      have hb1 := u8_lt (md.getD 1 (byte 0))
      have hl := stringFieldLen_lt _ _ hc.1 hb1
      have hm' : ¬ md.length < 2 := by simpa [binlogMetaLen] using hm
      simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false]
      split_ifs <;> first | omega | exact binlogStr_app _ _ _ (by omega)
  case MYSQL_TYPE_BIT.bytes b =>
    enc_intro
    have hm' : ¬ md.length < 2 := by simpa [binlogMetaLen] using hm
    simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false, binlogTake, ← hc]
    simp
  case MYSQL_TYPE_SET.bytes b =>
    enc_intro
    have hm' : ¬ md.length < 2 := by simpa [binlogMetaLen] using hm
    simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false, binlogTake, ← hc]
    simp
  case MYSQL_TYPE_ENUM.int x =>
    enc_intro
    have hm' : ¬ md.length < 2 := by simpa [binlogMetaLen] using hm
    simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false]
    obtain ⟨hk, h1, h2⟩ := hc
    rcases hk with hk | hk <;> rw [hk] at h2 <;> simp only [List.getD_eq_getElem?_getD] at hk <;>
      simp [hk, binlogNum, readLE_app _ _ _ (PBUtil.length_leBytes _ _), PBUtil.leNat_leBytes] <;> omega
  case MYSQL_TYPE_TIME.time neg d hh mi sc us =>
    rcases d with _ | d <;> rcases us with _ | us <;> simp only [reduceCtorEq] at h
    have hT : ∀ X : Int, -8388608 ≤ X → X < 8388608 → toSigned 24 (X % (2 ^ (8 * 3) : Int)).toNat = X := by
      intro X h1 h2; unfold toSigned; split_ifs <;> omega
    cases neg <;> simp only [Bool.false_eq_true, ite_true, ite_false, Option.ite_none_right_eq_some, Option.some.injEq] at h <;> obtain ⟨⟨c1, c2, c3, c4⟩, rfl⟩ := h
    all_goals
      have hm' : ¬ md.length < 0 := by omega
      simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false, binlogNum,
        readLE_app _ _ _ (IntAndMisc.length_leBytesI _ _), IntAndMisc.leNat_leBytesI, oldTimeVal]
      rw [hT _ (by push_cast; omega) (by push_cast; omega)]
      simp only [Val.time.injEq, BinlogOut.ok.injEq, and_true, one_mul, neg_one_mul, Int.natAbs_neg,
        Int.natAbs_natCast, decide_eq_true_eq, decide_eq_false_iff_not, true_and]
      simp at c4
      omega
  case MYSQL_TYPE_DATETIME.date y mo d hh mi sc us =>
    rcases us with _ | us <;> simp only [reduceCtorEq] at h
    enc_intro
    have hm' : ¬ md.length < 0 := by omega
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hc
    rw [show (y * 10000 + mo * 100 + d) * 10 ^ 6 + hh * 10000 + mi * 100 + sc = (y * 10000 + mo * 100 + d) * 10 ^ 6 + hh * 10000 + mi * 100 + sc from rfl]
    have hN : (y * 10000 + mo * 100 + d) * 10 ^ 6 + hh * 10000 + mi * 100 + sc < 2 ^ (8 * 8) := by
      simp only [Nat.reducePow, Nat.reduceMul]; omega
    simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false, binlogNum, Nat.mod_eq_of_lt hN,
      readLE_app _ _ _ (PBUtil.length_leBytes _ _), PBUtil.leNat_leBytes]
    simp only [BinlogOut.ok.injEq, Val.date.injEq, and_true, Nat.reduceMul, Nat.reducePow]
    omega
  case MYSQL_TYPE_NEWDATE.date y mo d hh mi sc us =>
    rcases hh with _ | hh <;> rcases mi with _ | mi <;> rcases sc with _ | sc <;> rcases us with _ | us <;>
      simp only [reduceCtorEq] at h
    enc_intro
    have hm' : ¬ md.length < 0 := by omega
    obtain ⟨c1, c2, c3⟩ := hc
    simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false, binlogNum,
      readLE_app _ _ _ (PBUtil.length_leBytes _ _), PBUtil.leNat_leBytes]
    simp only [BinlogOut.ok.injEq, Val.date.injEq, and_true, Nat.reduceMul, Nat.reducePow]
    omega
  case MYSQL_TYPE_TIME2.time neg d hh mi sc us =>
    enc_intro
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
    obtain ⟨p1, p2, p3⟩ := timePack_facts neg d hh mi sc us ⟨c1, c2, c3, c4, c5⟩
    have hm' : ¬ md.length < 1 := by simpa [binlogMetaLen] using hm
    have hr := time2Read_time2Bin' (md.getD 0 (byte 0)).val (timePack neg d hh mi sc us) tail ⟨p1, p2⟩
      ⟨by
        have hd : (fracUnit (md.getD 0 (byte 0)).val : Int) ∣ (us : Int) := Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero c6)
        rw [p3]; cases neg
        · exact Int.emod_eq_zero_of_dvd hd
        · exact Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr hd),
       by rw [p3]; cases neg <;> simp <;> omega⟩
    simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false, hr]
    rw [timeFromPacked_timePack' neg d hh mi sc us ⟨c1, c2, c3, c4, by omega⟩ c7]
  case MYSQL_TYPE_DATETIME2.date y mo d hh mi sc us =>
    enc_intro
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hc
    obtain ⟨p1, p2, p3⟩ := datetimePack_facts y mo d hh mi sc us ⟨c1, c2, c3, c4, c5, c6, c7⟩
    have hm' : ¬ md.length < 1 := by simpa [binlogMetaLen] using hm
    have hr := datetime2Read_datetime2Bin' (md.getD 0 (byte 0)).val (datetimePack y mo d hh mi sc us) tail ⟨p1, p2⟩
      ⟨by rw [p3]; omega, by rw [p3]; omega⟩
    have hn : ¬ datetimePack y mo d hh mi sc us ≤ -2 ^ 63 := by omega
    simp only [binlogRead, binlogEffType, binlogMetaLen, hm', ite_false, hr, hn]
    rw [datetimeFromPacked_datetimePack' y mo d hh mi sc us ⟨c1, c2, c3, c4, c5, c6, by omega⟩]

theorem not_binlogBug_of_binlogEnc' (ct : constants.ColumnType) (md : List U8) (uns : Bool) (v : Val)
    (bs tail : List U8) (h : binlogEnc ct md uns v = some bs) (hb : ¬ binlogEncBug ct md uns v) :
    ¬ binlogBug ct md uns (bs ++ tail) := by
  unfold binlogEnc at h
  split_ifs at h with hm
  cases ct <;> cases v <;> simp only [reduceCtorEq] at h
  all_goals try (simp [binlogIntEnc] at h; done)
  all_goals try (simp [binlogBug, binlogEffType]; done)
  case MYSQL_TYPE_INT24.int x =>
    unfold binlogIntEnc at h; enc_intro
    simp only [binlogEncBug, true_and, not_and, not_lt] at hb
    simp only [binlogBug, binlogEffType, not_and, not_le]
    intro hu _
    have hx := hb hu
    rw [List.take_left' (IntAndMisc.length_leBytesI _ _), IntAndMisc.leNat_leBytesI]
    rcases hc with ⟨h1, _⟩ | ⟨_, h2, h3⟩
    · simp [h1] at hu
    · norm_num at h3 ⊢; omega
  case MYSQL_TYPE_TIME.time neg d hh mi sc us =>
    rcases d with _ | d <;> rcases us with _ | us <;> simp only [reduceCtorEq] at h
    simp only [binlogEncBug, true_and, not_or, not_le, reduceCtorEq, false_and, or_false] at hb
    obtain ⟨hn, hh2⟩ := hb
    simp only [Bool.not_eq_true] at hn
    subst hn
    simp only [Bool.false_eq_true, ite_false, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨c1, c2, c3, c4⟩, rfl⟩ := h
    simp only [binlogBug, binlogEffType, not_and, not_or, not_le]
    intro _
    rw [List.take_left' (IntAndMisc.length_leBytesI _ _), IntAndMisc.leNat_leBytesI]
    norm_num
    have hg : ((hh:Int) * 10000 + mi * 100 + sc) / 16777216 = 0 := by omega
    omega
  case MYSQL_TYPE_TIME2.time neg d hh mi sc us =>
    enc_intro
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
    obtain ⟨p1, p2, p3⟩ := timePack_facts neg d hh mi sc us ⟨c1, c2, c3, c4, c5⟩
    simp only [binlogBug, binlogEffType]
    by_cases hd : (md.getD 0 (byte 0)).val = 1 ∨ (md.getD 0 (byte 0)).val = 2
    · rw [time2NegFracBug_time2Bin' _ _ tail hd ⟨p1, p2⟩ ⟨by
          have hdv : (fracUnit (md.getD 0 (byte 0)).val : Int) ∣ (us : Int) := Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero c6)
          rw [p3]; cases neg
          · exact Int.emod_eq_zero_of_dvd hdv
          · exact Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr hdv), by rw [p3]; cases neg <;> simp <;> omega⟩]
      simp only [binlogEncBug, reduceCtorEq, false_and, false_or, true_and, not_and] at hb
      rw [p3]
      have hb' := hb hd
      cases neg
      · intro ⟨hlt, _⟩
        unfold timePack packedMake at hlt; simp at hlt; omega
      · simp at hb' ⊢; omega
    · unfold time2NegFracBug; exact fun h => hd h.1

end Defs

namespace mysql_common.BinlogUtil

theorem length_timestamp2Bin (dec sec usec : Nat) :
    (timestamp2Bin dec sec usec).length = 4 + fracBytes dec := by
  simp [timestamp2Bin, beBytes, PBUtil.length_leBytes, length_temporalFracBin]

theorem timestamp_roundtrip (dec : U8) (sec usec : Nat) (hs : sec < 2 ^ 31)
    (hu : usec < 10 ^ 6 ∧ usec % fracUnit dec.val = 0)
    (tail : List U8) (input : io.ParseBuf) (h : input.val = timestamp2Bin dec.val sec usec ++ tail) :
    binlog.misc.my_timestamp_from_binary input dec ⦃ r rest =>
      (okPart r).map (fun x => (x.1.val, x.2.val)) = some ((sec : Int), (usec : Int)) ∧
        rest.val = tail ⦄ := by
  have hl : 4 + fracBytes dec.val ≤ input.length := by
    simp only [Slice.length, h, List.length_append, length_timestamp2Bin]; omega
  apply WP.spec_mono (timestamp_ok input dec hl)
  rintro ⟨r, rest⟩ ⟨s', u', rfl, hr⟩
  rw [h, timestamp2Read_timestamp2Bin' _ _ _ _ hs hu] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  simp [okPart, hr]

theorem datetime_ok (input : io.ParseBuf) (dec : U32) (hl : 5 + fracBytes dec.val ≤ input.length)
    (hp : ∀ p t, datetime2Read dec.val input.val = some (p, t) → -2 ^ 63 ≤ p) :
    binlog.misc.my_datetime_packed_from_binary input dec ⦃ r rest =>
      ∃ p : I64, r = .Ok p ∧ datetime2Read dec.val input.val = some (p.val, rest.val) ⦄ := by
  unfold binlog.misc.my_datetime_packed_from_binary
  step with okS (read_u40_be_ok input (by unfold fracBytes at hl; split_ifs at hl <;> omega)) as ⟨r, in1, x, hr, hx, hin1⟩
  subst hr
  have hlen1 : in1.length = input.length - 5 := by simp [Slice.length, hin1]
  have hx40 : x.val < 2 ^ 40 := by
    have := PBUtil.leNat_lt (List.take 5 input.val).reverse
    rw [hx, beNat]; simp only [List.length_reverse, List.length_take] at this
    have : 2 ^ (8 * min 5 input.val.length) ≤ 2^40 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift]
  have hi : (UScalar.hcast .I64 x).val = x.val := by
    rw [UScalar.hcast_val_eq]; simp only [IScalarTy.numBits]
    unfold Int.bmod
    have : ((x.val : Int) % ((2^64 : Nat) : Int)) = x.val := Int.emod_eq_of_lt (by omega) (by omega)
    simp only [this]; split_ifs <;> omega
  step with I64.sub_spec as ⟨intpart, hip⟩
  · simp [binlog.misc.DATETIMEF_INT_OFS]; scalar_tac
  have hip' : intpart.val = (beNat (input.val.take 5) : Int) - 549755813888 := by
    rw [hip, hi, hx]; simp [binlog.misc.DATETIMEF_INT_OFS]
  have hipb : -549755813888 ≤ intpart.val ∧ intpart.val < 549755813888 := by rw [hip']; omega
  have hw : wrapI64 (intpart.val * 2 ^ 24) = intpart.val * 2 ^ 24 := wrapI64_exact _ (by omega)
  split
  case h_1 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl hp ⊢
    norm_num [fracBytes] at hl hp
    step with okS (read_i8_ok in1 (by simp only [Slice.length] at *; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    step*
    all_goals
      have hF : (IScalar.cast IScalarTy.I64 frac).val = toSigned 8 (beNat ((input.val.drop 5).take 1)) * 10000 := by have hc1 : (IScalar.cast .I32 y).val = y.val := (by simp [IScalar.cast_val_eq]); have hc2 : (IScalar.cast .I64 frac).val = frac.val := (by simp [IScalar.cast_val_eq]); rw [hc2, frac_post, hc1, hy, hin1, beNat_take1]
      have hD : datetime2Read 1 input.val = some (packedMake intpart.val (toSigned 8 (beNat ((input.val.drop 5).take 1)) * 10000), input.val.drop (5 + 1)) := by
        simp only [datetime2Read, fracBytes, temporalFracRead, hip']; norm_num; omega
      have hpl := hp _ _ hD
      have hb : beNat ((input.val.drop 5).take 1) < 2 ^ (8 * 1) := by
        have := PBUtil.leNat_lt ((input.val.drop 5).take 1).reverse
        simp only [List.length_reverse, List.length_take, List.length_drop] at this
        rw [show min 1 (input.val.length - 5) = 1 by omega] at this
        simpa [beNat] using this
      unfold packedMake at hpl hD
      rw [hw] at *
    case h => rw [hF]; unfold toSigned at *; split_ifs at * <;> omega
    refine ⟨_, rfl, ?_⟩
    simp only [show (1#32 : BitVec 32).toNat = 1 from rfl]
    rw [hD]
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨by omega, by rw [hin2, hin1, List.drop_drop]⟩
  case h_2 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl hp ⊢
    norm_num [fracBytes] at hl hp
    step with okS (read_i8_ok in1 (by simp only [Slice.length] at *; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    step*
    all_goals
      have hF : (IScalar.cast IScalarTy.I64 frac).val = toSigned 8 (beNat ((input.val.drop 5).take 1)) * 10000 := by have hc1 : (IScalar.cast .I32 y).val = y.val := (by simp [IScalar.cast_val_eq]); have hc2 : (IScalar.cast .I64 frac).val = frac.val := (by simp [IScalar.cast_val_eq]); rw [hc2, frac_post, hc1, hy, hin1, beNat_take1]
      have hD : datetime2Read 2 input.val = some (packedMake intpart.val (toSigned 8 (beNat ((input.val.drop 5).take 1)) * 10000), input.val.drop (5 + 1)) := by
        simp only [datetime2Read, fracBytes, temporalFracRead, hip']; norm_num; omega
      have hpl := hp _ _ hD
      have hb : beNat ((input.val.drop 5).take 1) < 2 ^ (8 * 1) := by
        have := PBUtil.leNat_lt ((input.val.drop 5).take 1).reverse
        simp only [List.length_reverse, List.length_take, List.length_drop] at this
        rw [show min 1 (input.val.length - 5) = 1 by omega] at this
        simpa [beNat] using this
      unfold packedMake at hpl hD
      rw [hw] at *
    case h => rw [hF]; unfold toSigned at *; split_ifs at * <;> omega
    refine ⟨_, rfl, ?_⟩
    simp only [show (2#32 : BitVec 32).toNat = 2 from rfl]
    rw [hD]
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨by omega, by rw [hin2, hin1, List.drop_drop]⟩
  case h_3 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl hp ⊢
    norm_num [fracBytes] at hl hp
    step with okS (read_i16_be_ok in1 (by simp only [Slice.length] at *; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    step*
    all_goals
      have hF : (IScalar.cast IScalarTy.I64 frac).val = toSigned 16 (beNat ((input.val.drop 5).take 2)) * 100 := by have hc1 : (IScalar.cast .I32 y).val = y.val := (by simp [IScalar.cast_val_eq]); have hc2 : (IScalar.cast .I64 frac).val = frac.val := (by simp [IScalar.cast_val_eq]); rw [hc2, frac_post, hc1, hy, hin1]
      have hD : datetime2Read 3 input.val = some (packedMake intpart.val (toSigned 16 (beNat ((input.val.drop 5).take 2)) * 100), input.val.drop (5 + 2)) := by
        simp only [datetime2Read, fracBytes, temporalFracRead, hip']; norm_num; omega
      have hpl := hp _ _ hD
      have hb : beNat ((input.val.drop 5).take 2) < 2 ^ (8 * 2) := by
        have := PBUtil.leNat_lt ((input.val.drop 5).take 2).reverse
        simp only [List.length_reverse, List.length_take, List.length_drop] at this
        rw [show min 2 (input.val.length - 5) = 2 by omega] at this
        simpa [beNat] using this
      unfold packedMake at hpl hD
      rw [hw] at *
    case h => rw [hF]; unfold toSigned at *; split_ifs at * <;> omega
    refine ⟨_, rfl, ?_⟩
    simp only [show (3#32 : BitVec 32).toNat = 3 from rfl]
    rw [hD]
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨by omega, by rw [hin2, hin1, List.drop_drop]⟩
  case h_4 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl hp ⊢
    norm_num [fracBytes] at hl hp
    step with okS (read_i16_be_ok in1 (by simp only [Slice.length] at *; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    step*
    all_goals
      have hF : (IScalar.cast IScalarTy.I64 frac).val = toSigned 16 (beNat ((input.val.drop 5).take 2)) * 100 := by have hc1 : (IScalar.cast .I32 y).val = y.val := (by simp [IScalar.cast_val_eq]); have hc2 : (IScalar.cast .I64 frac).val = frac.val := (by simp [IScalar.cast_val_eq]); rw [hc2, frac_post, hc1, hy, hin1]
      have hD : datetime2Read 4 input.val = some (packedMake intpart.val (toSigned 16 (beNat ((input.val.drop 5).take 2)) * 100), input.val.drop (5 + 2)) := by
        simp only [datetime2Read, fracBytes, temporalFracRead, hip']; norm_num; omega
      have hpl := hp _ _ hD
      have hb : beNat ((input.val.drop 5).take 2) < 2 ^ (8 * 2) := by
        have := PBUtil.leNat_lt ((input.val.drop 5).take 2).reverse
        simp only [List.length_reverse, List.length_take, List.length_drop] at this
        rw [show min 2 (input.val.length - 5) = 2 by omega] at this
        simpa [beNat] using this
      unfold packedMake at hpl hD
      rw [hw] at *
    case h => rw [hF]; unfold toSigned at *; split_ifs at * <;> omega
    refine ⟨_, rfl, ?_⟩
    simp only [show (4#32 : BitVec 32).toNat = 4 from rfl]
    rw [hD]
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨by omega, by rw [hin2, hin1, List.drop_drop]⟩
  case h_5 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl hp ⊢
    norm_num [fracBytes] at hl hp
    step with okS (read_i24_be_ok in1 (by simp only [Slice.length] at *; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    step*
    all_goals
      have hF : (IScalar.cast IScalarTy.I64 y).val = toSigned 24 (beNat ((input.val.drop 5).take 3)) := by have hc1 : (IScalar.cast .I64 y).val = y.val := (by simp [IScalar.cast_val_eq]); rw [hc1, hy, hin1]
      have hD : datetime2Read 5 input.val = some (packedMake intpart.val (toSigned 24 (beNat ((input.val.drop 5).take 3))), input.val.drop (5 + 3)) := by
        simp only [datetime2Read, fracBytes, temporalFracRead, hip']; norm_num; omega
      have hpl := hp _ _ hD
      have hb : beNat ((input.val.drop 5).take 3) < 2 ^ (8 * 3) := by
        have := PBUtil.leNat_lt ((input.val.drop 5).take 3).reverse
        simp only [List.length_reverse, List.length_take, List.length_drop] at this
        rw [show min 3 (input.val.length - 5) = 3 by omega] at this
        simpa [beNat] using this
      unfold packedMake at hpl hD
      rw [hw] at *
    case h => rw [hF]; unfold toSigned at *; split_ifs at * <;> omega
    refine ⟨_, rfl, ?_⟩
    simp only [show (5#32 : BitVec 32).toNat = 5 from rfl]
    rw [hD]
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨by omega, by rw [hin2, hin1, List.drop_drop]⟩
  case h_6 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl hp ⊢
    norm_num [fracBytes] at hl hp
    step with okS (read_i24_be_ok in1 (by simp only [Slice.length] at *; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    step*
    all_goals
      have hF : (IScalar.cast IScalarTy.I64 y).val = toSigned 24 (beNat ((input.val.drop 5).take 3)) := by have hc1 : (IScalar.cast .I64 y).val = y.val := (by simp [IScalar.cast_val_eq]); rw [hc1, hy, hin1]
      have hD : datetime2Read 6 input.val = some (packedMake intpart.val (toSigned 24 (beNat ((input.val.drop 5).take 3))), input.val.drop (5 + 3)) := by
        simp only [datetime2Read, fracBytes, temporalFracRead, hip']; norm_num; omega
      have hpl := hp _ _ hD
      have hb : beNat ((input.val.drop 5).take 3) < 2 ^ (8 * 3) := by
        have := PBUtil.leNat_lt ((input.val.drop 5).take 3).reverse
        simp only [List.length_reverse, List.length_take, List.length_drop] at this
        rw [show min 3 (input.val.length - 5) = 3 by omega] at this
        simpa [beNat] using this
      unfold packedMake at hpl hD
      rw [hw] at *
    case h => rw [hF]; unfold toSigned at *; split_ifs at * <;> omega
    refine ⟨_, rfl, ?_⟩
    simp only [show (6#32 : BitVec 32).toNat = 6 from rfl]
    rw [hD]
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨by omega, by rw [hin2, hin1, List.drop_drop]⟩
  case h_7 h1 h2 h3 h4 h5 h6 =>
    have hd : ¬(dec.val = 1 ∨ dec.val = 2 ∨ dec.val = 3 ∨ dec.val = 4 ∨ dec.val = 5 ∨ dec.val = 6) := by
      intro hd
      rcases hd with hd | hd | hd | hd | hd | hd
      · exact h1 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h2 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h3 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h4 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h5 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h6 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
    step*
    refine ⟨_, rfl, ?_⟩
    have hf : fracBytes dec.val = 0 := by unfold fracBytes; split_ifs <;> omega
    have ht : temporalFracRead dec.val [] = 0 := by unfold temporalFracRead; split_ifs <;> omega
    simp only [datetime2Read, hf, List.take_zero, ht, packedMake]
    rw [if_neg (by simp only [Slice.length, hf] at hl; omega)]
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨by rw [i1_post, hw, hip']; omega, by rw [hin1]⟩

theorem length_datetime2Bin (dec : Nat) (p : Int) :
    (datetime2Bin dec p).length = 5 + fracBytes dec := by
  simp [datetime2Bin, length_temporalFracBin]

theorem datetime_roundtrip (dec : U32) (p : Int)
    (hp : 0 ≤ p ∧ p < 2 ^ 63)
    (hf : packedFracPart p % (fracUnit dec.val : Int) = 0 ∧ packedFracPart p < 10 ^ 6)
    (tail : List U8) (input : io.ParseBuf) (h : input.val = datetime2Bin dec.val p ++ tail) :
    binlog.misc.my_datetime_packed_from_binary input dec ⦃ r rest =>
      (okPart r).map (·.val) = some p ∧ rest.val = tail ⦄ := by
  have hr := datetime2Read_datetime2Bin' dec.val p tail hp hf
  have hl : 5 + fracBytes dec.val ≤ input.length := by
    simp only [Slice.length, h, List.length_append, length_datetime2Bin]; omega
  apply WP.spec_mono (datetime_ok input dec hl (by intro p' t ht; rw [h, hr] at ht; simp at ht; omega))
  rintro ⟨r, rest⟩ ⟨q, rfl, hq⟩
  rw [h, hr] at hq
  simp only [Option.some.injEq, Prod.mk.injEq] at hq
  simp [okPart, hq]

end mysql_common.BinlogUtil

namespace mysql_common.BinlogUtil

theorem u8_lt' (b : U8) : b.val < 256 := by have := b.hBounds; simpa using this

theorem wrapI64_mul (z : Int) (h : -2 ^ 39 ≤ z ∧ z < 2 ^ 39) : wrapI64 (z * 2 ^ 24) = z * 2 ^ 24 :=
  wrapI64_exact _ (by omega)

theorem cast64_i32 (z : I32) : (IScalar.cast .I64 z).val = z.val := by simp [IScalar.cast_val_eq]

theorem time_ok (input : io.ParseBuf) (dec : U32) (hl : 3 + fracBytes dec.val ≤ input.length)
    (hbug : ¬ time2NegFracBug dec.val input.val) :
    binlog.misc.my_time_packed_from_binary input dec ⦃ r rest =>
      ∃ p : I64, r = .Ok p ∧ time2Read dec.val input.val = some (p.val, rest.val) ⦄ := by
  unfold binlog.misc.my_time_packed_from_binary
  have hx24 : beNat (input.val.take 3) < 2 ^ 24 := by
    have := PBUtil.leNat_lt (List.take 3 input.val).reverse
    simp only [List.length_reverse, List.length_take] at this
    rw [show min 3 input.val.length = 3 by simp only [Slice.length] at hl; unfold fracBytes at hl; split_ifs at hl <;> omega] at this
    simpa [beNat] using this
  split
  case h_1 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl hbug ⊢
    norm_num [fracBytes, time2NegFracBug] at hl hbug
    step with okS (read_u24_be_ok input (by simp only [Slice.length] at *; omega)) as ⟨r, in1, x, hr, hx, hin1⟩
    subst hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift]
    have hi : (UScalar.hcast .I64 x).val = x.val := by
      rw [UScalar.hcast_val_eq]; simp only [IScalarTy.numBits]
      unfold Int.bmod
      have : ((x.val : Int) % ((2^64 : Nat) : Int)) = x.val := Int.emod_eq_of_lt (by omega) (by omega)
      simp only [this]; split_ifs <;> omega
    step with I64.sub_spec as ⟨intpart, hip⟩
    · simp [binlog.misc.TIMEF_INT_OFS]; scalar_tac
    have hip' : intpart.val = (beNat (input.val.take 3) : Int) - 8388608 := by
      rw [hip, hi, hx]; simp [binlog.misc.TIMEF_INT_OFS]
    step with okS (read_u8_ok in1 (by simp only [Slice.length, hin1] at *; simp; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    have hyv : (UScalar.cast UScalarTy.U32 y).val = beNat ((input.val.drop 3).take 1) := by
      have := u8_lt' y
      rw [UScalar.cast_val_eq, beNat_take1, ← hin1, ← hy]; simp only [UScalarTy.numBits]; omega
    by_cases hneg : intpart < 0#i64
    · have hy0 : ¬ (UScalar.cast UScalarTy.U32 y > 0#u32) := by
        have h1 : intpart.val < 0 := by scalar_tac
        intro h2
        have h3 : (UScalar.cast UScalarTy.U32 y).val > 0 := by scalar_tac
        rw [hyv] at h3
        have := hbug hl (by omega)
        omega
      simp only [hneg, hy0, ite_true, ite_false, Std.bind_ok]
      have hF : (UScalar.hcast IScalarTy.I64 (UScalar.cast UScalarTy.U32 y)).val = beNat ((input.val.drop 3).take 1) := by
        rw [UScalar.hcast_val_eq, hyv]
        have hb : beNat ((input.val.drop 3).take 1) < 256 := by rw [← hyv]; have := u8_lt' y; rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
        simp only [IScalarTy.numBits]; unfold Int.bmod
        have : ((beNat ((input.val.drop 3).take 1) : Int) % ((2^64 : Nat) : Int)) = beNat ((input.val.drop 3).take 1) := Int.emod_eq_of_lt (by omega) (by omega)
        simp only [this]; split_ifs <;> omega
      have hw : wrapI64 (intpart.val * 2 ^ 24) = intpart.val * 2 ^ 24 := wrapI64_exact _ (by rw [hip']; omega)
      have hb : beNat ((input.val.drop 3).take 1) < 256 := by rw [← hyv]; have := u8_lt' y; rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
      step*
      case h => rw [hw]; scalar_tac
      refine ⟨_, rfl, ?_⟩
      simp only [show (1#32 : BitVec 32).toNat = 1 from rfl]
      have hlen : ¬ (input.val.length < 3 + fracBytes 1) := by simp [fracBytes]; omega
      simp only [time2Read, hlen, ite_false, fracBytes]
      norm_num
      refine ⟨hl, ?_, by simp [hin2, hin1, List.drop_drop]⟩
      rw [if_neg (by intro ⟨a, b⟩; exact b (hbug hl a)), i3_post, hw, i2_post, hF, hip']
      unfold packedMake; ring
    · simp only [hneg, ite_false, Std.bind_ok]
      have hF : (UScalar.hcast IScalarTy.I64 (UScalar.cast UScalarTy.U32 y)).val = beNat ((input.val.drop 3).take 1) := by
        rw [UScalar.hcast_val_eq, hyv]
        have hb : beNat ((input.val.drop 3).take 1) < 256 := by rw [← hyv]; have := u8_lt' y; rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
        simp only [IScalarTy.numBits]; unfold Int.bmod
        have : ((beNat ((input.val.drop 3).take 1) : Int) % ((2^64 : Nat) : Int)) = beNat ((input.val.drop 3).take 1) := Int.emod_eq_of_lt (by omega) (by omega)
        simp only [this]; split_ifs <;> omega
      have hw : wrapI64 (intpart.val * 2 ^ 24) = intpart.val * 2 ^ 24 := wrapI64_exact _ (by rw [hip']; omega)
      have hb : beNat ((input.val.drop 3).take 1) < 256 := by rw [← hyv]; have := u8_lt' y; rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
      step*
      case h => rw [hw]; scalar_tac
      refine ⟨_, rfl, ?_⟩
      simp only [show (1#32 : BitVec 32).toNat = 1 from rfl]
      have hlen : ¬ (input.val.length < 3 + fracBytes 1) := by simp [fracBytes]; omega
      simp only [time2Read, hlen, ite_false, fracBytes]
      norm_num
      refine ⟨hl, ?_, by simp [hin2, hin1, List.drop_drop]⟩
      rw [if_neg (by intro ⟨a, b⟩; exact b (hbug hl a)), i3_post, hw, i2_post, hF, hip']
      unfold packedMake; ring

  case h_2 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl hbug ⊢
    norm_num [fracBytes, time2NegFracBug] at hl hbug
    step with okS (read_u24_be_ok input (by simp only [Slice.length] at *; omega)) as ⟨r, in1, x, hr, hx, hin1⟩
    subst hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift]
    have hi : (UScalar.hcast .I64 x).val = x.val := by
      rw [UScalar.hcast_val_eq]; simp only [IScalarTy.numBits]
      unfold Int.bmod
      have : ((x.val : Int) % ((2^64 : Nat) : Int)) = x.val := Int.emod_eq_of_lt (by omega) (by omega)
      simp only [this]; split_ifs <;> omega
    step with I64.sub_spec as ⟨intpart, hip⟩
    · simp [binlog.misc.TIMEF_INT_OFS]; scalar_tac
    have hip' : intpart.val = (beNat (input.val.take 3) : Int) - 8388608 := by
      rw [hip, hi, hx]; simp [binlog.misc.TIMEF_INT_OFS]
    step with okS (read_u8_ok in1 (by simp only [Slice.length, hin1] at *; simp; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    have hyv : (UScalar.cast UScalarTy.U32 y).val = beNat ((input.val.drop 3).take 1) := by
      have := u8_lt' y
      rw [UScalar.cast_val_eq, beNat_take1, ← hin1, ← hy]; simp only [UScalarTy.numBits]; omega
    by_cases hneg : intpart < 0#i64
    · have hy0 : ¬ (UScalar.cast UScalarTy.U32 y > 0#u32) := by
        have h1 : intpart.val < 0 := by scalar_tac
        intro h2
        have h3 : (UScalar.cast UScalarTy.U32 y).val > 0 := by scalar_tac
        rw [hyv] at h3
        have := hbug hl (by omega)
        omega
      simp only [hneg, hy0, ite_true, ite_false, Std.bind_ok]
      have hF : (UScalar.hcast IScalarTy.I64 (UScalar.cast UScalarTy.U32 y)).val = beNat ((input.val.drop 3).take 1) := by
        rw [UScalar.hcast_val_eq, hyv]
        have hb : beNat ((input.val.drop 3).take 1) < 256 := by rw [← hyv]; have := u8_lt' y; rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
        simp only [IScalarTy.numBits]; unfold Int.bmod
        have : ((beNat ((input.val.drop 3).take 1) : Int) % ((2^64 : Nat) : Int)) = beNat ((input.val.drop 3).take 1) := Int.emod_eq_of_lt (by omega) (by omega)
        simp only [this]; split_ifs <;> omega
      have hw : wrapI64 (intpart.val * 2 ^ 24) = intpart.val * 2 ^ 24 := wrapI64_exact _ (by rw [hip']; omega)
      have hb : beNat ((input.val.drop 3).take 1) < 256 := by rw [← hyv]; have := u8_lt' y; rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
      step*
      case h => rw [hw]; scalar_tac
      refine ⟨_, rfl, ?_⟩
      simp only [show (2#32 : BitVec 32).toNat = 2 from rfl]
      have hlen : ¬ (input.val.length < 3 + fracBytes 2) := by simp [fracBytes]; omega
      simp only [time2Read, hlen, ite_false, fracBytes]
      norm_num
      refine ⟨hl, ?_, by simp [hin2, hin1, List.drop_drop]⟩
      rw [if_neg (by intro ⟨a, b⟩; exact b (hbug hl a)), i3_post, hw, i2_post, hF, hip']
      unfold packedMake; ring
    · simp only [hneg, ite_false, Std.bind_ok]
      have hF : (UScalar.hcast IScalarTy.I64 (UScalar.cast UScalarTy.U32 y)).val = beNat ((input.val.drop 3).take 1) := by
        rw [UScalar.hcast_val_eq, hyv]
        have hb : beNat ((input.val.drop 3).take 1) < 256 := by rw [← hyv]; have := u8_lt' y; rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
        simp only [IScalarTy.numBits]; unfold Int.bmod
        have : ((beNat ((input.val.drop 3).take 1) : Int) % ((2^64 : Nat) : Int)) = beNat ((input.val.drop 3).take 1) := Int.emod_eq_of_lt (by omega) (by omega)
        simp only [this]; split_ifs <;> omega
      have hw : wrapI64 (intpart.val * 2 ^ 24) = intpart.val * 2 ^ 24 := wrapI64_exact _ (by rw [hip']; omega)
      have hb : beNat ((input.val.drop 3).take 1) < 256 := by rw [← hyv]; have := u8_lt' y; rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
      step*
      case h => rw [hw]; scalar_tac
      refine ⟨_, rfl, ?_⟩
      simp only [show (2#32 : BitVec 32).toNat = 2 from rfl]
      have hlen : ¬ (input.val.length < 3 + fracBytes 2) := by simp [fracBytes]; omega
      simp only [time2Read, hlen, ite_false, fracBytes]
      norm_num
      refine ⟨hl, ?_, by simp [hin2, hin1, List.drop_drop]⟩
      rw [if_neg (by intro ⟨a, b⟩; exact b (hbug hl a)), i3_post, hw, i2_post, hF, hip']
      unfold packedMake; ring

  case h_3 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl hbug ⊢
    norm_num [fracBytes, time2NegFracBug] at hl hbug
    step with okS (read_u24_be_ok input (by simp only [Slice.length] at *; omega)) as ⟨r, in1, x, hr, hx, hin1⟩
    subst hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift]
    have hi : (UScalar.hcast .I64 x).val = x.val := by
      rw [UScalar.hcast_val_eq]; simp only [IScalarTy.numBits]
      unfold Int.bmod
      have : ((x.val : Int) % ((2^64 : Nat) : Int)) = x.val := Int.emod_eq_of_lt (by omega) (by omega)
      simp only [this]; split_ifs <;> omega
    step with I64.sub_spec as ⟨intpart, hip⟩
    · simp [binlog.misc.TIMEF_INT_OFS]; scalar_tac
    have hip' : intpart.val = (beNat (input.val.take 3) : Int) - 8388608 := by
      rw [hip, hi, hx]; simp [binlog.misc.TIMEF_INT_OFS]
    step with okS (read_u16_be_ok in1 (by simp only [Slice.length, hin1] at *; simp; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    have hb2 : beNat ((input.val.drop 3).take 2) < 65536 := by
      have := PBUtil.leNat_lt ((input.val.drop 3).take 2).reverse
      simp only [List.length_reverse, List.length_take, List.length_drop] at this
      rw [show min 2 (input.val.length - 3) = 2 by omega] at this
      simpa [beNat] using this
    have hyv : (UScalar.hcast IScalarTy.I32 y).val = beNat ((input.val.drop 3).take 2) := by
      rw [UScalar.hcast_val_eq, hy, hin1]; simp only [IScalarTy.numBits]; unfold Int.bmod
      have : ((beNat ((input.val.drop 3).take 2) : Int) % ((2^32 : Nat) : Int)) = beNat ((input.val.drop 3).take 2) := Int.emod_eq_of_lt (by omega) (by omega)
      simp only [this]; split_ifs <;> omega
    have hlen : ¬ (input.val.length < 3 + fracBytes 3) := by simp [fracBytes]; omega
    by_cases hneg : intpart < 0#i64
    · have hneg' : intpart.val < 0 := by scalar_tac
      by_cases hpos : UScalar.hcast IScalarTy.I32 y > 0#i32
      · have hpos' : (UScalar.hcast IScalarTy.I32 y).val > 0 := by scalar_tac
        simp only [hneg, hpos, ite_true, Std.bind_ok]
        step*
        case h =>
          simp (disch := omega) only [wrapI64_mul] at *
          simp only [cast64_i32] at *
          scalar_tac
        refine ⟨_, rfl, ?_⟩
        simp only [show (3#32 : BitVec 32).toNat = 3 from rfl, time2Read, hlen, ite_false, fracBytes]
        norm_num
        refine ⟨by omega, ?_, by simp [hin2, hin1, List.drop_drop]⟩
        simp (disch := omega) only [wrapI64_mul] at *
        simp only [cast64_i32] at *
        split_ifs <;> unfold packedMake <;> omega
      · have hpos' : ¬ (UScalar.hcast IScalarTy.I32 y).val > 0 := by scalar_tac
        simp only [hneg, hpos, ite_true, ite_false, Std.bind_ok]
        step*
        case h =>
          simp (disch := omega) only [wrapI64_mul] at *
          simp only [cast64_i32] at *
          scalar_tac
        refine ⟨_, rfl, ?_⟩
        simp only [show (3#32 : BitVec 32).toNat = 3 from rfl, time2Read, hlen, ite_false, fracBytes]
        norm_num
        refine ⟨by omega, ?_, by simp [hin2, hin1, List.drop_drop]⟩
        simp (disch := omega) only [wrapI64_mul] at *
        simp only [cast64_i32] at *
        split_ifs <;> unfold packedMake <;> omega
    · have hneg' : ¬ intpart.val < 0 := by scalar_tac
      simp only [hneg, ite_false, Std.bind_ok]
      step*
      case h =>
        simp (disch := omega) only [wrapI64_mul] at *
        simp only [cast64_i32] at *
        scalar_tac
      refine ⟨_, rfl, ?_⟩
      simp only [show (3#32 : BitVec 32).toNat = 3 from rfl, time2Read, hlen, ite_false, fracBytes]
      norm_num
      refine ⟨by omega, ?_, by simp [hin2, hin1, List.drop_drop]⟩
      simp (disch := omega) only [wrapI64_mul] at *
      simp only [cast64_i32] at *
      split_ifs <;> unfold packedMake <;> omega

  case h_4 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl hbug ⊢
    norm_num [fracBytes, time2NegFracBug] at hl hbug
    step with okS (read_u24_be_ok input (by simp only [Slice.length] at *; omega)) as ⟨r, in1, x, hr, hx, hin1⟩
    subst hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift]
    have hi : (UScalar.hcast .I64 x).val = x.val := by
      rw [UScalar.hcast_val_eq]; simp only [IScalarTy.numBits]
      unfold Int.bmod
      have : ((x.val : Int) % ((2^64 : Nat) : Int)) = x.val := Int.emod_eq_of_lt (by omega) (by omega)
      simp only [this]; split_ifs <;> omega
    step with I64.sub_spec as ⟨intpart, hip⟩
    · simp [binlog.misc.TIMEF_INT_OFS]; scalar_tac
    have hip' : intpart.val = (beNat (input.val.take 3) : Int) - 8388608 := by
      rw [hip, hi, hx]; simp [binlog.misc.TIMEF_INT_OFS]
    step with okS (read_u16_be_ok in1 (by simp only [Slice.length, hin1] at *; simp; omega)) as ⟨r2, in2, y, hr2, hy, hin2⟩
    subst hr2
    simp only [Std.bind_ok]
    have hb2 : beNat ((input.val.drop 3).take 2) < 65536 := by
      have := PBUtil.leNat_lt ((input.val.drop 3).take 2).reverse
      simp only [List.length_reverse, List.length_take, List.length_drop] at this
      rw [show min 2 (input.val.length - 3) = 2 by omega] at this
      simpa [beNat] using this
    have hyv : (UScalar.hcast IScalarTy.I32 y).val = beNat ((input.val.drop 3).take 2) := by
      rw [UScalar.hcast_val_eq, hy, hin1]; simp only [IScalarTy.numBits]; unfold Int.bmod
      have : ((beNat ((input.val.drop 3).take 2) : Int) % ((2^32 : Nat) : Int)) = beNat ((input.val.drop 3).take 2) := Int.emod_eq_of_lt (by omega) (by omega)
      simp only [this]; split_ifs <;> omega
    have hlen : ¬ (input.val.length < 3 + fracBytes 4) := by simp [fracBytes]; omega
    by_cases hneg : intpart < 0#i64
    · have hneg' : intpart.val < 0 := by scalar_tac
      by_cases hpos : UScalar.hcast IScalarTy.I32 y > 0#i32
      · have hpos' : (UScalar.hcast IScalarTy.I32 y).val > 0 := by scalar_tac
        simp only [hneg, hpos, ite_true, Std.bind_ok]
        step*
        case h =>
          simp (disch := omega) only [wrapI64_mul] at *
          simp only [cast64_i32] at *
          scalar_tac
        refine ⟨_, rfl, ?_⟩
        simp only [show (4#32 : BitVec 32).toNat = 4 from rfl, time2Read, hlen, ite_false, fracBytes]
        norm_num
        refine ⟨by omega, ?_, by simp [hin2, hin1, List.drop_drop]⟩
        simp (disch := omega) only [wrapI64_mul] at *
        simp only [cast64_i32] at *
        split_ifs <;> unfold packedMake <;> omega
      · have hpos' : ¬ (UScalar.hcast IScalarTy.I32 y).val > 0 := by scalar_tac
        simp only [hneg, hpos, ite_true, ite_false, Std.bind_ok]
        step*
        case h =>
          simp (disch := omega) only [wrapI64_mul] at *
          simp only [cast64_i32] at *
          scalar_tac
        refine ⟨_, rfl, ?_⟩
        simp only [show (4#32 : BitVec 32).toNat = 4 from rfl, time2Read, hlen, ite_false, fracBytes]
        norm_num
        refine ⟨by omega, ?_, by simp [hin2, hin1, List.drop_drop]⟩
        simp (disch := omega) only [wrapI64_mul] at *
        simp only [cast64_i32] at *
        split_ifs <;> unfold packedMake <;> omega
    · have hneg' : ¬ intpart.val < 0 := by scalar_tac
      simp only [hneg, ite_false, Std.bind_ok]
      step*
      case h =>
        simp (disch := omega) only [wrapI64_mul] at *
        simp only [cast64_i32] at *
        scalar_tac
      refine ⟨_, rfl, ?_⟩
      simp only [show (4#32 : BitVec 32).toNat = 4 from rfl, time2Read, hlen, ite_false, fracBytes]
      norm_num
      refine ⟨by omega, ?_, by simp [hin2, hin1, List.drop_drop]⟩
      simp (disch := omega) only [wrapI64_mul] at *
      simp only [cast64_i32] at *
      split_ifs <;> unfold packedMake <;> omega

  case h_5 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl hbug ⊢
    norm_num [fracBytes, time2NegFracBug] at hl
    step with okS (read_u48_be_ok input (by simp only [Slice.length] at *; omega)) as ⟨r, in1, x, hr, hx, hin1⟩
    subst hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift]
    have hx48 : x.val < 2 ^ 48 := by
      have := PBUtil.leNat_lt (List.take 6 input.val).reverse
      simp only [List.length_reverse, List.length_take] at this
      rw [show min 6 input.val.length = 6 by omega] at this
      rw [hx]; simpa [beNat] using this
    have hi : (UScalar.hcast .I64 x).val = x.val := by
      rw [UScalar.hcast_val_eq]; simp only [IScalarTy.numBits]
      unfold Int.bmod
      have : ((x.val : Int) % ((2^64 : Nat) : Int)) = x.val := Int.emod_eq_of_lt (by omega) (by omega)
      simp only [this]; split_ifs <;> omega
    step with I64.sub_spec as ⟨v, hv⟩
    · simp [binlog.misc.TIMEF_OFS]; scalar_tac
    refine ⟨_, rfl, ?_⟩
    have hlen : ¬ (input.val.length < 3 + fracBytes 5) := by simp [fracBytes]; omega
    simp only [show (5#32 : BitVec 32).toNat = 5 from rfl, time2Read, hlen, ite_false, fracBytes]
    norm_num
    refine ⟨hl, ?_, by simp [hin1]⟩
    rw [hv, hi, hx]; simp [binlog.misc.TIMEF_OFS]
  case h_6 =>
    simp only [PBUtil.val_mk, BitVec.toNat_ofNat] at hl hbug ⊢
    norm_num [fracBytes, time2NegFracBug] at hl
    step with okS (read_u48_be_ok input (by simp only [Slice.length] at *; omega)) as ⟨r, in1, x, hr, hx, hin1⟩
    subst hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift]
    have hx48 : x.val < 2 ^ 48 := by
      have := PBUtil.leNat_lt (List.take 6 input.val).reverse
      simp only [List.length_reverse, List.length_take] at this
      rw [show min 6 input.val.length = 6 by omega] at this
      rw [hx]; simpa [beNat] using this
    have hi : (UScalar.hcast .I64 x).val = x.val := by
      rw [UScalar.hcast_val_eq]; simp only [IScalarTy.numBits]
      unfold Int.bmod
      have : ((x.val : Int) % ((2^64 : Nat) : Int)) = x.val := Int.emod_eq_of_lt (by omega) (by omega)
      simp only [this]; split_ifs <;> omega
    step with I64.sub_spec as ⟨v, hv⟩
    · simp [binlog.misc.TIMEF_OFS]; scalar_tac
    refine ⟨_, rfl, ?_⟩
    have hlen : ¬ (input.val.length < 3 + fracBytes 6) := by simp [fracBytes]; omega
    simp only [show (6#32 : BitVec 32).toNat = 6 from rfl, time2Read, hlen, ite_false, fracBytes]
    norm_num
    refine ⟨hl, ?_, by simp [hin1]⟩
    rw [hv, hi, hx]; simp [binlog.misc.TIMEF_OFS]
  case h_7 h1 h2 h3 h4 h5 h6 =>
    have hd : ¬(dec.val = 1 ∨ dec.val = 2 ∨ dec.val = 3 ∨ dec.val = 4 ∨ dec.val = 5 ∨ dec.val = 6) := by
      intro hd
      rcases hd with hd | hd | hd | hd | hd | hd
      · exact h1 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h2 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h3 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h4 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h5 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
      · exact h6 (by apply UScalar.eq_of_val_eq; simpa [PBUtil.val_mk] using hd)
    have hf : fracBytes dec.val = 0 := by unfold fracBytes; split_ifs <;> omega
    rw [hf] at hl
    step with okS (read_u24_be_ok input (by simp only [Slice.length] at *; omega)) as ⟨r, in1, x, hr, hx, hin1⟩
    subst hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, lift]
    have hi : (UScalar.hcast .I64 x).val = x.val := by
      rw [UScalar.hcast_val_eq]; simp only [IScalarTy.numBits]
      unfold Int.bmod
      have : ((x.val : Int) % ((2^64 : Nat) : Int)) = x.val := Int.emod_eq_of_lt (by omega) (by omega)
      simp only [this]; split_ifs <;> omega
    step with I64.sub_spec as ⟨intpart, hip⟩
    · simp [binlog.misc.TIMEF_INT_OFS]; scalar_tac
    have hip' : intpart.val = (beNat (input.val.take 3) : Int) - 8388608 := by
      rw [hip, hi, hx]; simp [binlog.misc.TIMEF_INT_OFS]
    step*
    refine ⟨_, rfl, ?_⟩
    have hlen : ¬ (input.val.length < 3 + fracBytes dec.val) := by simp only [Slice.length] at hl; omega
    have hd12 : ¬(dec.val = 1 ∨ dec.val = 2) := by omega
    have hd34 : ¬(dec.val = 3 ∨ dec.val = 4) := by omega
    have hd56 : ¬(dec.val = 5 ∨ dec.val = 6) := by omega
    simp only [time2Read, hlen, ite_false, hd12, hd34, hd56, hf, packedMake]
    norm_num
    refine ⟨by simp only [Slice.length] at hl; omega, ?_, by simp [hin1]⟩
    rw [i2_post, wrapI64_mul _ (by rw [hip']; omega), hip']
    norm_num

theorem length_time2Bin (dec : Nat) (p : Int) : (time2Bin dec p).length = 3 + fracBytes dec := by
  unfold time2Bin fracBytes; split_ifs <;> simp

theorem time_roundtrip (dec : U32) (p : Int)
    (hp : -2 ^ 47 ≤ p ∧ p < 2 ^ 47)
    (hf : packedFracPart p % (fracUnit dec.val : Int) = 0 ∧ (packedFracPart p).natAbs < 10 ^ 6)
    (hbug : ¬((dec.val = 1 ∨ dec.val = 2) ∧ p < 0 ∧ packedFracPart p ≠ 0))
    (tail : List U8) (input : io.ParseBuf) (h : input.val = time2Bin dec.val p ++ tail) :
    binlog.misc.my_time_packed_from_binary input dec ⦃ r rest =>
      (okPart r).map (·.val) = some p ∧ rest.val = tail ⦄ := by
  have hr := time2Read_time2Bin' dec.val p tail hp hf
  have hl : 3 + fracBytes dec.val ≤ input.length := by
    simp only [Slice.length, h, List.length_append, length_time2Bin]; omega
  have hb : ¬ time2NegFracBug dec.val input.val := by
    by_cases hd : dec.val = 1 ∨ dec.val = 2
    · rw [h, time2NegFracBug_time2Bin' _ _ _ hd hp hf]; exact fun h' => hbug ⟨hd, h'⟩
    · exact fun h' => hd h'.1
  apply WP.spec_mono (time_ok input dec hl hb)
  rintro ⟨r, rest⟩ ⟨q, rfl, hq⟩
  rw [h, hr] at hq
  simp only [Option.some.injEq, Prod.mk.injEq] at hq
  simp [okPart, hq]

end mysql_common.BinlogUtil
