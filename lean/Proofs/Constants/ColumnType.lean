import Defs

/-! Statements for `enum ColumnType and its impls` (spec file: `Specs/Constants.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `TryFrom<u8> for ColumnType`: the type with that code, or the code back as the error. -/
theorem constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from_spec (value : U8) :
    constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from value =
      ok (match columnTypeOfCode value.val with
        | some ct => .Ok ct
        | none => .Err value) := by
  sorry

/-- `From<ColumnType> for u8`: the type code. -/
theorem U8.Insts.CoreConvertFromColumnType.from_spec (ct : constants.ColumnType) :
    U8.Insts.CoreConvertFromColumnType.from ct ⦃ r => r.val = columnTypeCode ct ⦄ := by
  sorry

end mysql_common
