import Proofs.Io.ParseBuf
import Proofs.Util.IntAndMisc
set_option autoImplicit false
open Aeneas Aeneas.Std Result mysql_common Defs

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
