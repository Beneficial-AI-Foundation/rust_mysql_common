import Proofs.Util.IntAndMisc

/-! Statements for `fn read_varlen_uint` (spec file: `Specs/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

private theorem tbody_spec (fb : U8) (t : Usize) (ht : t.val ≤ 8)
    (hall : ∀ j < t.val, fb.val.testBit j = true) :
    misc.read_varlen_uint_loop.body fb t ⦃ r => match r with
      | .done y => y.val = trailingOnes fb
      | .cont t' => (t'.val ≤ 8 ∧ ∀ j < t'.val, fb.val.testBit j = true) ∧ 8 - t'.val < 8 - t.val ⦄ := by
  unfold misc.read_varlen_uint_loop.body
  split_ifs with hlt
  · have hlt' : t.val < 8 := by scalar_tac
    step as ⟨ i, hi1, hi2 ⟩
    step as ⟨ i1, hj1, hj2 ⟩
    have hv : i1.val = (fb.val >>> t.val) % 2 := by
      rw [hj1, UScalar.val_and, hi1]
      rw [show (1#u8).val = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    have htb : fb.val.testBit t.val = decide ((fb.val >>> t.val) % 2 = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
    split
    · rename_i h1
      have hb : fb.val.testBit t.val = true := by
        rw [htb, ← hv, h1]; rfl
      step*
      refine ⟨by omega, ?_, by omega⟩
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 (show j < t.val + 1 by omega) with hj' | rfl
      · exact hall j hj'
      · exact hb
    · rename_i h1
      have hb : fb.val.testBit t.val = false := by
        rw [htb]; simp only [decide_eq_false_iff_not]; intro h; apply h1
        exact UScalar.eq_of_val_eq (by rw [hv, h]; rfl)
      simp only [spec_ok]
      exact (IntAndMisc.trailingOnes_eq fb t.val ht hall (fun _ => hb)).symm
  · have : t.val = 8 := by scalar_tac
    simp only [spec_ok]
    exact (IntAndMisc.trailingOnes_eq fb t.val ht hall (by omega)).symm

private theorem tloop_spec (fb : U8) :
    misc.read_varlen_uint_loop fb 0#usize ⦃ r => r.val = trailingOnes fb ⦄ := by
  unfold misc.read_varlen_uint_loop
  apply loop.spec_decr_nat (fun t => 8 - t.val) (fun t => t.val ≤ 8 ∧ ∀ j < t.val, fb.val.testBit j = true)
  · rintro t ⟨ht, hall⟩
    apply spec_mono (tbody_spec fb t ht hall)
    intro r h; cases r <;> exact h
  · exact ⟨by decide, by intro j hj; simp at hj⟩

/-- `read_varlen_uint`: total; the serialization-library decoder `varlenUintDecode`. On error
    (empty or truncated input) the buffer is unchanged. -/
theorem misc.read_varlen_uint_spec (buf : io.ParseBuf) :
    misc.read_varlen_uint buf ⦃ r rest =>
      (okPart r).map (fun n => (n.val, rest.val)) = varlenUintDecode buf.val ∧
      (okPart r = none → rest = buf) ⦄ := by
  unfold misc.read_varlen_uint
  step with io.ParseBuf.is_empty_spec as ⟨ be, hbe ⟩
  split_ifs with hbt
  · have hnil : buf.val = [] := hbe.1 hbt
    step*
    simp [okPart, hnil, varlenUintDecode]
  · obtain ⟨c, rest, hcr⟩ : ∃ c rest, buf.val = c :: rest := by
      cases h : buf.val with
      | nil => exact absurd (hbe.2 h) hbt
      | cons c rest => exact ⟨c, rest, rfl⟩
    step*
    have hfb : first_byte = c := by simp [first_byte_post, hcr]
    subst hfb
    step with tloop_spec as ⟨ t, ht ⟩
    have hlen : buf.length = rest.length + 1 := by simp [Slice.length, hcr]
    have hdec := hcr
    simp only [hcr, varlenUintDecode]
    split
    · rename_i h8
      have h8' : trailingOnes first_byte = 8 := by rw [← ht, h8]; rfl
      simp only [h8', ↓reduceIte]
      step*
      · have : rest.length < 8 := by scalar_tac
        simp [okPart, readLE, show ¬ 8 ≤ rest.length by omega]
      · have hr8 : 8 ≤ rest.length := by scalar_tac
        have hs : s.val = rest := by rw [s_post, hcr]; simp
        have hv : i1.val = leNat (rest.take 8) := by
          have : i1.val = i1.bv.toNat := rfl
          rw [this, i1_post, PBUtil.fromLEBytes_cast_toNat, to_slice_mut_back_post, s3_post,
            Array.from_slice_val _ _ (by simp [s2_post1]), s2_post, hs]
          simp [List.slice]
        simp [okPart, readLE, hr8, hv, s4_post, hs]
    · rename_i h8
      have h8' : trailingOnes first_byte ≠ 8 := by
        intro h; apply h8; exact UScalar.eq_of_val_eq (by rw [ht, h]; rfl)
      have hle8 : trailingOnes first_byte ≤ 8 := by
        unfold trailingOnes; have := (List.takeWhile_sublist (l := List.range 8) (fun i => first_byte.val.testBit i)).length_le; simpa using this
      simp only [h8', ↓reduceIte]
      step*
      · have : ¬ trailingOnes first_byte + 1 ≤ rest.length + 1 := by scalar_tac
        simp [okPart, this]
      · have hk : num_bytes.val = trailingOnes first_byte + 1 := by rw [num_bytes_post, ht]
        have hkl : trailingOnes first_byte + 1 ≤ rest.length + 1 := by scalar_tac
        have hlev : le_val.val = leNat (buf.val.take num_bytes.val) := by
          have : le_val.val = le_val.bv.toNat := rfl
          rw [this, le_val_post, PBUtil.fromLEBytes_cast_toNat, s_post2, s2_post, s1_post]
          simp only [List.slice, List.drop_zero, Nat.sub_zero]
          exact PBUtil.padded_take_le 8 buf.val num_bytes.val (by omega)
        rw [hk] at hlev i1_post s3_post
        rw [hcr] at hlev s3_post
        simp [okPart, hkl, i1_post, hlev, s3_post, Nat.shiftRight_eq_div_pow]

/-- Round trip: `read_varlen_uint` reads back `varlenUint v` (what `write_varlen_uint` writes), for every `v : u64`. -/
theorem misc.read_varlen_uint_roundtrip (v : U64) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = varlenUint v.val ++ tail) :
    misc.read_varlen_uint buf ⦃ r rest => okPart r = some v ∧ rest.val = tail ⦄ := by
  apply spec_mono (misc.read_varlen_uint_spec buf)
  rintro ⟨r, rest⟩ ⟨h1, -⟩
  rw [h, IntAndMisc.varlenUintDecode_varlenUint' _ _ v.hBounds] at h1
  cases hr : okPart r with
  | none => rw [hr] at h1; simp at h1
  | some y =>
    rw [hr] at h1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    exact ⟨by rw [hr, UScalar.eq_of_val_eq h1.1], h1.2⟩

end mysql_common
