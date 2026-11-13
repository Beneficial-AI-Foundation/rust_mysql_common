import Proofs.Util.IntAndMisc
import Proofs.Misc.LenencIntLen

/-! Statements for `fn lenenc_str_len` (spec file: `Specs/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `lenenc_str_len(s)`: the length of the length-encoded string `s`. Precondition: that length
    fits in a `u64` (true of every real slice, whose length is at most `isize::MAX`). -/
theorem misc.lenenc_str_len_spec (s : Slice U8) (h : (lenencStr s.val).length < 2 ^ 64) :
    misc.lenenc_str_len s ⦃ n => n.val = (lenencStr s.val).length ⦄ := by
  unfold misc.lenenc_str_len
  step*
  have hs : s.val.length < 2 ^ 64 := by simp only [lenencStr, List.length_append] at h; omega
  have hl : len.val = s.val.length := by
    rw [len_post, UScalar.cast_val_eq]; exact Nat.mod_eq_of_lt (by simpa using hs)
  step with misc.lenenc_int_len_spec as ⟨ i1, hi1 ⟩
  simp only [lenencStr, List.length_append] at h ⊢
  rw [hl] at hi1
  step*

end mysql_common
