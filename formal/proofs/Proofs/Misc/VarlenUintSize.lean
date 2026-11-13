import Proofs.Util.IntAndMisc

/-! Statements for `fn varlen_uint_size` (spec file: `Specs/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `varlen_uint_size(v)`: the number of bytes of the encoding (`(varlenUint v).length = varlenUintSize v` is `Defs.varlenUint_length`). -/
theorem misc.varlen_uint_size_spec (v : U64) :
    misc.varlen_uint_size v ⦃ n => n.val = varlenUintSize v.val ⦄ := by
  have hsz : varlenUintSize v.val = if v.val < 128 then 1 else if v.val < 16384 then 2
      else if v.val < 2097152 then 3 else if v.val < 268435456 then 4 else if v.val < 34359738368 then 5
      else if v.val < 4398046511104 then 6 else if v.val < 562949953421312 then 7
      else if v.val < 72057594037927936 then 8 else 9 := by
    simp only [varlenUintSize, List.range', List.find?]
    norm_num
    split_ifs <;> simp [*]
  rw [hsz]
  unfold misc.varlen_uint_size
  apply spec_bind (Pₘ := fun d => d.val = if v.val = 0 then 0 else Nat.log 2 v.val + 1)
  · split
    · rename_i h0; subst h0; simp
    · rename_i h0
      have hv0 : v.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      have hlog : Nat.log 2 v.val < 64 := Nat.log_lt_of_lt_pow hv0 (by scalar_tac)
      have hbv : v.bv ≠ 0 := fun h => hv0 (by have := congrArg BitVec.toNat h; exact this)
      have hi : (core.num.U64.leading_zeros v).val = 63 - Nat.log 2 v.val := by
        simp only [core.num.U64.leading_zeros, BitVec.leadingZeros, hbv, ite_false]
        change (64 - Nat.log 2 v.val - 1) % 2 ^ 32 = _
        omega
      step*
  · intro d hd
    have key : ∀ k : Nat, v.val < 2 ^ k ↔ d.val ≤ k := by
      intro k
      rw [hd]; split
      · simp_all
      · rename_i hv0
        rw [← Nat.log_lt_iff_lt_pow (by norm_num) hv0]; omega
    have k7 := key 7
    have k14 := key 14
    have k21 := key 21
    have k28 := key 28
    have k35 := key 35
    have k42 := key 42
    have k49 := key 49
    have k56 := key 56
    have hD : d.val ≤ 64 := (key 64).1 (by scalar_tac)
    norm_num at k7 k14 k21 k28 k35 k42 k49 k56
    simp only [k7, k14, k21, k28, k35, k42, k49, k56]
    clear k7 k14 k21 k28 k35 k42 k49 k56 key hsz hd
    simp only [UScalar.le_equiv]
    generalize hDd : d.val = D at *
    clear hDd
    iterate 65 (rcases D with _ | D; · simp)
    omega

end mysql_common
