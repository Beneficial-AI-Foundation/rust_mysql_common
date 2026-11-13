import Defs
import Proofs.Util.BinlogConsts

/-! Statements for `enum BinlogRowValueOptions and its impls` (spec file: `Specs/Binlog/Row.lean`). Helper lemmas: `Proofs/Util/BinlogConsts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.BinlogConstsUtil

namespace mysql_common

/-- `TryFrom<u64> for BinlogRowValueOptions`: total; `PARTIAL_JSON_UPDATES` for 1, else the value back as the error. -/
theorem binlog.row.BinlogRowValueOptions.Insts.CoreConvertTryFromU64UnknownBinlogRowValueOptions.try_from_spec (value : U64) :
    binlog.row.BinlogRowValueOptions.Insts.CoreConvertTryFromU64UnknownBinlogRowValueOptions.try_from value =
      ok (match rowValueOptionsOfCode value.val with
        | some o => .Ok o
        | none => .Err value) := by
  unfold binlog.row.BinlogRowValueOptions.Insts.CoreConvertTryFromU64UnknownBinlogRowValueOptions.try_from
  split <;> first | rfl |
    simp_all [uscalar_eq_iff, uscalar_mk_val, rowValueOptionsOfCode]

end mysql_common
