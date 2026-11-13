import Defs

/-! Statements for `fn my_packed_time_get_int_part` (spec file: `Specs/Binlog/Misc.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `my_packed_time_get_int_part(i)`: total; `i >> 24` (arithmetic). -/
theorem binlog.misc.my_packed_time_get_int_part_spec (i : I64) :
    binlog.misc.my_packed_time_get_int_part i ⦃ r => r.val = packedIntPart i.val ⦄ := by
  sorry

end mysql_common
