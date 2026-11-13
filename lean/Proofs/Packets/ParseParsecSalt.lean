import Defs

/-! Statements for `fn parse_parsec_salt` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `parse_parsec_salt`: total; the data itself iff it is 20 bytes, starts with `'P'` and has an iteration factor of at most 20 (`parsecSaltOk`), else `None`. (The comment calls it the "20-byte prefix", but a longer input is rejected.) -/
theorem packets.parse_parsec_salt_spec (data : Slice U8) :
    packets.parse_parsec_salt data ⦃ r => r.map (·.val) = if parsecSaltOk data.val then some data.val else none ⦄ := by
  sorry

end mysql_common
