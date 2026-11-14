import Proofs.Util.IntAndMisc

/-! Statements for `fn lenenc_int_len` (spec file: `Specs/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `lenenc_int_len(x)`: the length of the length-encoded integer `x` (1, 3, 4 or 9). -/
theorem misc.lenenc_int_len_spec (x : U64) :
    misc.lenenc_int_len x ⦃ n => n.val = (lenencInt x.val).length ⦄ := by
  unfold misc.lenenc_int_len
  have h1 : x < 251#u64 ↔ x.val < 251 := by scalar_tac
  have h2 : x < 65536#u64 ↔ x.val < 2 ^ 16 := by scalar_tac
  have h3 : x < 16777216#u64 ↔ x.val < 2 ^ 24 := by scalar_tac
  simp only [lenencInt]
  split_ifs <;> simp_all <;> omega

end mysql_common
