import Defs
import Proofs.Util.BinlogValue

/-! Statements for `fn my_packed_time_get_frac_part` (spec file: `Specs/Binlog/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `my_packed_time_get_frac_part(i)`: total; `i % 2^24` with the sign of `i` (C's and Rust's `%`). -/
theorem binlog.misc.my_packed_time_get_frac_part_spec (i : I64) :
    binlog.misc.my_packed_time_get_frac_part i ⦃ r => r.val = packedFracPart i.val ⦄ :=
  BinlogUtil.get_frac_part_spec i

end mysql_common
