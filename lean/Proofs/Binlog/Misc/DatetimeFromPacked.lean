import Defs

/-! Statements for `fn datetime_from_packed` (spec file: `Specs/Binlog/Misc.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `datetime_from_packed(tmp)`: MySQL's `TIME_from_longlong_datetime_packed` of `|tmp|` (`datetimeFromPacked`), for every `tmp` but `i64::MIN`. The sign MySQL records is dropped. -/
theorem binlog.misc.datetime_from_packed_spec (tmp : I64) (h : tmp.val ≠ -2 ^ 63) :
    binlog.misc.datetime_from_packed tmp ⦃ v => Val.ofValue v = datetimeFromPacked tmp.val ⦄ := by
  sorry

/-- `datetime_from_packed(i64::MIN)` panics (negation overflow). `my_datetime_packed_from_binary` returns `i64::MIN` for an integer part of five zero bytes with zero fraction (any `dec`), so the invalid DATETIME2 `00 00 00 00 00` crashes `BinlogValue` decoding. -/
theorem binlog.misc.datetime_from_packed_min (tmp : I64) (h : tmp.val = -2 ^ 63) :
    binlog.misc.datetime_from_packed tmp = fail .integerOverflow := by
  sorry

end mysql_common
