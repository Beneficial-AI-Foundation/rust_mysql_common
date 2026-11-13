import Defs

/-! Statements for `fn my_packed_time_make` (spec file: `Specs/Binlog/Misc.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `my_packed_time_make(i, f)`: `MY_PACKED_TIME_MAKE(i, f)`: `my_packed_time_make_int(i) + f`, when the sum fits in `i64`. -/
theorem binlog.misc.my_packed_time_make_spec (i f : I64)
    (h : -2 ^ 63 ≤ wrapI64 (i.val * 2 ^ 24) + f.val ∧ wrapI64 (i.val * 2 ^ 24) + f.val < 2 ^ 63) :
    binlog.misc.my_packed_time_make i f ⦃ r => r.val = wrapI64 (i.val * 2 ^ 24) + f.val ⦄ := by
  sorry

/-- `my_packed_time_make(i, f)` panics (`i64` overflow of the addition) otherwise. -/
theorem binlog.misc.my_packed_time_make_overflow (i f : I64)
    (h : ¬(-2 ^ 63 ≤ wrapI64 (i.val * 2 ^ 24) + f.val ∧ wrapI64 (i.val * 2 ^ 24) + f.val < 2 ^ 63)) :
    binlog.misc.my_packed_time_make i f = fail .integerOverflow := by
  sorry

end mysql_common
