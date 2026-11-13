import Defs

/-! Statements for `enum StatusVarKey and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `TryFrom<u8> for StatusVarKey`: total; the query-event status variable with that code (MySQL's `Q_*` codes 0–20), or the byte back as the error. -/
theorem binlog.consts.StatusVarKey.Insts.CoreConvertTryFromU8UnknownStatusVarKey.try_from_spec (value : U8) :
    binlog.consts.StatusVarKey.Insts.CoreConvertTryFromU8UnknownStatusVarKey.try_from value =
      ok (match statusVarKeyOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  sorry

end mysql_common
