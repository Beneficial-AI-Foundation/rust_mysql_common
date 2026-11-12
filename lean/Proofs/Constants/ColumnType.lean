import Defs
import Mathlib.Tactic.IntervalCases

/-! Statements for `enum ColumnType and its impls` (spec file: `Specs/Constants.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `TryFrom<u8> for ColumnType`: the type with that code, or the code back as the error. -/
theorem constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from_spec (value : U8) :
    constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from value =
      ok (match columnTypeOfCode value.val with
        | some ct => .Ok ct
        | none => .Err value) := by
  -- One case per byte value: both sides compute.
  obtain ⟨⟨⟨n, hn⟩⟩⟩ := value
  change n < 256 at hn
  interval_cases n <;> rfl

/-- `From<ColumnType> for u8`: the type code. -/
@[step]
theorem U8.Insts.CoreConvertFromColumnType.from_spec (ct : constants.ColumnType) :
    U8.Insts.CoreConvertFromColumnType.from ct ⦃ r => r.val = columnTypeCode ct ⦄ := by
  cases ct <;> simp [U8.Insts.CoreConvertFromColumnType.from, columnTypeCode, read_discriminant,
    constants.ColumnType.read_discriminant]

end mysql_common
