import Defs

/-! Statements for `struct Gno and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `Gno::MAX_GNO`: `i64::MAX` (`Defs.maxGno`, MySQL's `MAX_GNO`). -/
theorem binlog.consts.Gno.MAX_GNO_eq :
    binlog.consts.Gno.MAX_GNO = ok ⟨BitVec.ofNat 64 maxGno⟩ := by
  sorry

/-- `TryFrom<u64> for Gno`: total; `Ok` for `0` (the anonymous GTID's number) and for `MIN_GNO ≤ value < MAX_GNO`, else the value back as the error. **Quirk**: `MAX_GNO` itself is rejected, while the type's documentation and the error message ("out of range [MIN_GNO, MAX_GNO]") say it is in range. -/
theorem binlog.consts.Gno.Insts.CoreConvertTryFromU64InvalidGno.try_from_spec (value : U64) :
    binlog.consts.Gno.Insts.CoreConvertTryFromU64InvalidGno.try_from value =
      ok (if value.val = 0 ∨ (1 ≤ value.val ∧ value.val < maxGno) then .Ok value else .Err value) := by
  sorry

end mysql_common
