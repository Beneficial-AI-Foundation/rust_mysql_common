import Defs

/-! Statements for `fn parse_parsec_salt` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `parse_parsec_salt`: total; the data itself iff it is 20 bytes, starts with `'P'` and has an iteration factor of at most 20 (`parsecSaltOk`), else `None`. (The comment calls it the "20-byte prefix", but a longer input is rejected.) -/
theorem packets.parse_parsec_salt_spec (data : Slice U8) :
    packets.parse_parsec_salt data ⦃ r => r.map (·.val) = if parsecSaltOk data.val then some data.val else none ⦄ := by
  unfold packets.parse_parsec_salt
  by_cases hl : data.length = 20
  · have hlen : Slice.len data = 20#usize := by scalar_tac
    simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ite_false, core.array.TryFromSharedArraySlice.try_from]
    rw [Aeneas.dite_true]
    obtain ⟨d0, d1, rest, hd⟩ : ∃ d0 d1 rest, data.val = d0 :: d1 :: rest := by
      match h : data.val, (show data.val.length = 20 from hl) with
      | d0 :: d1 :: rest, _ => exact ⟨d0, d1, rest, rfl⟩
    step*
    all_goals
      have hp : parsecSaltOk data.val = (d0.val == 80 && decide (d1.val ≤ 20)) := by
        unfold parsecSaltOk
        rw [show data.val.length = 20 from hl, hd]
        simp
      rw [hp]
      simp only [hd, List.getElem_cons_zero, List.getElem_cons_succ] at algorithm_post factor_post
      subst algorithm_post factor_post
    all_goals (simp only [bne_iff_ne, ne_eq, Decidable.not_not, gt_iff_lt] at *)
    · have : algorithm.val ≠ 80 := fun h => ‹¬ algorithm = 80#u8› (UScalar.eq_of_val_eq (by simpa using h))
      simp [this]
    · have : ¬ factor.val ≤ 20 := by scalar_tac
      simp [this]
    · subst ‹algorithm = 80#u8›
      have : factor.val ≤ 20 := by scalar_tac
      simp [this]
  · have hlen : Slice.len data ≠ 20#usize := by intro h; apply hl; scalar_tac
    simp [hlen, parsecSaltOk, Slice.length] at hl ⊢
    simp [hl]

end mysql_common
