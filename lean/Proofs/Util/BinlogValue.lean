import Proofs.Io.ParseBuf
import Proofs.Util.IntAndMisc
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
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
