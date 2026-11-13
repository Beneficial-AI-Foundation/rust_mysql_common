import Defs
import Proofs.Util.BinlogValue

/-! Statements for `fn my_packed_time_get_int_part` (spec file: `Specs/Binlog/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `my_packed_time_get_int_part(i)`: total; `i >> 24` (arithmetic). -/
theorem binlog.misc.my_packed_time_get_int_part_spec (i : I64) :
    binlog.misc.my_packed_time_get_int_part i ⦃ r => r.val = packedIntPart i.val ⦄ :=
  BinlogUtil.get_int_part_spec i

end mysql_common
