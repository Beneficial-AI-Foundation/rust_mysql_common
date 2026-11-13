import Defs

/-! Statements for `enum BinlogVersion and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `From<BinlogVersion> for u16`: the version number. -/
theorem U16.Insts.CoreConvertFromBinlogVersion.from_spec (x : binlog.consts.BinlogVersion) :
    U16.Insts.CoreConvertFromBinlogVersion.from x ⦃ r => r.val = binlogVersionCode x ⦄ := by
  sorry

/-- `TryFrom<u16> for BinlogVersion`: total; the version with that number (1–4), or the number back as the error. -/
theorem binlog.consts.BinlogVersion.Insts.CoreConvertTryFromU16UnknownBinlogVersion.try_from_spec (value : U16) :
    binlog.consts.BinlogVersion.Insts.CoreConvertTryFromU16UnknownBinlogVersion.try_from value =
      ok (match binlogVersionOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  sorry

end mysql_common
