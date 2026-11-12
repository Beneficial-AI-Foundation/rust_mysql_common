import Proofs.Util.IntAndMisc
import Proofs.Misc.VarlenUintSize

/-! Statements for `fn write_varlen_uint` (spec file: `Specs/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `write_varlen_uint`: appends the serialization-library encoding `varlenUint v` (1 to 9 bytes). -/
theorem misc.write_varlen_uint_spec (buf : alloc.vec.Vec U8) (v : U64) (h : buf.length + 9 ≤ Usize.max) :
    misc.write_varlen_uint buf v ⦃ buf' => buf'.val = buf.val ++ varlenUint v.val ⦄ := by
  unfold misc.write_varlen_uint
  step with misc.varlen_uint_size_spec as ⟨ k, hk ⟩
  obtain ⟨h1, h9, hlt, hge⟩ := IntAndMisc.varlenUintSize_spec v.val
  rw [← hk] at h1 h9 hlt hge
  split
  · rename_i hk9
    step*
    apply spec_mono (IntAndMisc.put_slice_spec buf1 s (by simp [buf1_post, s_post]; scalar_tac))
    intro b hb
    have hk9' : varlenUintSize v.val = 9 := by rw [← hk, hk9]; rfl
    rw [hb, buf1_post, s_post]
    simp [varlenUint, hk9', a_post, IntAndMisc.leBytes_bv 8 rfl]
    rfl
  · rename_i hk9
    have hk8 : k.val ≤ 8 := by
      have : k.val ≠ 9 := fun h' => hk9 (UScalar.eq_of_val_eq (by rw [h']; rfl))
      omega
    have hv7 := hlt hk8
    have hsz : U64.size = 2 ^ 64 := by rw [U64.size_def]; try simp [U64.numBits]
    have hp1 := Nat.one_le_two_pow (n := k.val - 1)
    have hpk : (2 : Nat) ^ k.val = 2 * 2 ^ (k.val - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hpow8 : (2 : Nat) ^ (8 * k.val) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsmall : v.val * 2 ^ k.val < 2 ^ (8 * k.val) := by
      have e1 : (2 : Nat) ^ (8 * k.val) = 2 ^ (7 * k.val) * 2 ^ k.val := by
        rw [← pow_add]; congr 1; ring
      rw [e1]; exact Nat.mul_lt_mul_of_pos_right hv7 (by positivity)
    step*
    all_goals
      have hi1 : i1.val = 2 ^ (k.val - 1) := by
        rw [i1_post, i_post, Nat.one_shiftLeft, hsz]
        try exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega)) (le_refl _))
    · rw [hi1]; simp
    · have hsh : shifted.val = v.val * 2 ^ k.val := by
        rw [shifted_post, Nat.shiftLeft_eq, hsz]
        try exact Nat.mod_eq_of_lt (lt_of_lt_of_le hsmall hpow8)
      have htr : trailer.val = 2 ^ (k.val - 1) - 1 := by rw [trailer_post, hi1]
      have henc : encoded.val = v.val * 2 ^ k.val + (2 ^ (k.val - 1) - 1) := by
        rw [encoded_post, UScalar.val_or, hsh, htr, ← Nat.shiftLeft_eq,
          ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
      apply spec_mono (IntAndMisc.put_slice_spec buf s (by rw [s_post1]; scalar_tac))
      intro b hb
      have hk9' : varlenUintSize v.val ≠ 9 := by rw [← hk]; omega
      rw [hb, s_post]
      simp [varlenUint, ← hk, a_post, IntAndMisc.leBytes_bv 8 rfl, List.slice,
        IntAndMisc.take_leBytes _ _ _ hk8, henc]
      intro h'; omega

end mysql_common
