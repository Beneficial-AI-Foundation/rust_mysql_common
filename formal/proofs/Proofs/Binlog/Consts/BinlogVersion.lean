import Defs
import Proofs.Util.BinlogConsts

/-! Statements for `enum BinlogVersion and its impls` (spec file: `Specs/Binlog/Consts.lean`). Helper lemmas: `Proofs/Util/BinlogConsts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.BinlogConstsUtil

namespace mysql_common

/-- `From<BinlogVersion> for u16`: the version number. -/
@[step]
theorem U16.Insts.CoreConvertFromBinlogVersion.from_spec (x : binlog.consts.BinlogVersion) :
    U16.Insts.CoreConvertFromBinlogVersion.from x ⦃ r => r.val = binlogVersionCode x ⦄ := by
  cases x <;> simp [U16.Insts.CoreConvertFromBinlogVersion.from, binlogVersionCode, read_discriminant,
    binlog.consts.BinlogVersion.read_discriminant]

/-- `TryFrom<u16> for BinlogVersion`: total; the version with that number (1–4), or the number back as the error. -/
theorem binlog.consts.BinlogVersion.Insts.CoreConvertTryFromU16UnknownBinlogVersion.try_from_spec (value : U16) :
    binlog.consts.BinlogVersion.Insts.CoreConvertTryFromU16UnknownBinlogVersion.try_from value =
      ok (match binlogVersionOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  unfold binlog.consts.BinlogVersion.Insts.CoreConvertTryFromU16UnknownBinlogVersion.try_from
  split <;> first | rfl |
    simp_all [uscalar_eq_iff, uscalar_mk_val, binlogVersionOfCode, allBinlogVersions, binlogVersionCode, List.find?]

end mysql_common
