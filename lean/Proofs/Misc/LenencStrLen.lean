import Defs

/-! Statements for `fn lenenc_str_len` (spec file: `Specs/Misc.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `lenenc_str_len(s)`: the length of the length-encoded string `s`. Precondition: that length
    fits in a `u64` (true of every real slice, whose length is at most `isize::MAX`). -/
theorem misc.lenenc_str_len_spec (s : Slice U8) (h : (lenencStr s.val).length < 2 ^ 64) :
    misc.lenenc_str_len s ⦃ n => n.val = (lenencStr s.val).length ⦄ := by
  sorry

end mysql_common
