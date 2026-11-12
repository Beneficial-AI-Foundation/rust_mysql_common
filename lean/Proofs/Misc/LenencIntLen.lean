import Defs

/-! Statements for `fn lenenc_int_len` (spec file: `Specs/Misc.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `lenenc_int_len(x)`: the length of the length-encoded integer `x` (1, 3, 4 or 9). -/
theorem misc.lenenc_int_len_spec (x : U64) :
    misc.lenenc_int_len x ⦃ n => n.val = (lenencInt x.val).length ⦄ := by
  sorry

end mysql_common
