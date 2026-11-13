import Defs

/-! Statements for `fn time_from_packed` (spec file: `Specs/Binlog/Misc.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `time_from_packed(tmp)`: MySQL's `TIME_from_longlong_time_packed` (`timeFromPacked`: sign, hours from 10 bits split into days and hours, minutes, seconds, microseconds), for every `tmp` but `i64::MIN`. -/
theorem binlog.misc.time_from_packed_spec (tmp : I64) (h : tmp.val ≠ -2 ^ 63) :
    binlog.misc.time_from_packed tmp ⦃ v => Val.ofValue v = timeFromPacked tmp.val ⦄ := by
  sorry

/-- `time_from_packed(i64::MIN)` panics (negation overflow; no TIME2 encoding gives it). -/
theorem binlog.misc.time_from_packed_min (tmp : I64) (h : tmp.val = -2 ^ 63) :
    binlog.misc.time_from_packed tmp = fail .integerOverflow := by
  sorry

end mysql_common
