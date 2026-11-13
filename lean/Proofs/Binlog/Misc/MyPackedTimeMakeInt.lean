import Defs

/-! Statements for `fn my_packed_time_make_int` (spec file: `Specs/Binlog/Misc.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `my_packed_time_make_int(i)`: total; `MY_PACKED_TIME_MAKE_INT(i)` = `(i as u64) << 24`, reinterpreted as `i64` (wraps; exact, `packedMake i 0`, for `|i| < 2^39`). -/
theorem binlog.misc.my_packed_time_make_int_spec (i : I64) :
    binlog.misc.my_packed_time_make_int i ⦃ r => r.val = wrapI64 (i.val * 2 ^ 24) ⦄ := by
  sorry

end mysql_common
