import Defs

/-! Statements for `fn varlen_uint_size` (spec file: `Specs/Misc.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `varlen_uint_size(v)`: the number of bytes of the encoding (`(varlenUint v).length = varlenUintSize v` is `Defs.varlenUint_length`). -/
theorem misc.varlen_uint_size_spec (v : U64) :
    misc.varlen_uint_size v ⦃ n => n.val = varlenUintSize v.val ⦄ := by
  sorry

end mysql_common
