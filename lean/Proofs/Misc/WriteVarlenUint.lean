import Defs

/-! Statements for `fn write_varlen_uint` (spec file: `Specs/Misc.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `write_varlen_uint`: appends the serialization-library encoding `varlenUint v` (1 to 9 bytes). -/
theorem misc.write_varlen_uint_spec (buf : alloc.vec.Vec U8) (v : U64) (h : buf.length + 9 ≤ Usize.max) :
    misc.write_varlen_uint buf v ⦃ buf' => buf'.val = buf.val ++ varlenUint v.val ⦄ := by
  sorry

end mysql_common
