import Defs

/-! Statements for `enum LoadDuplicateHandling and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `From<LoadDuplicateHandling> for u8`: the code. -/
theorem U8.Insts.CoreConvertFromLoadDuplicateHandling.from_spec (x : binlog.consts.LoadDuplicateHandling) :
    U8.Insts.CoreConvertFromLoadDuplicateHandling.from x ⦃ r => r.val = loadDupCode x ⦄ := by
  sorry

/-- `TryFrom<u8> for LoadDuplicateHandling`: total; the handling with that code (0–2), or the byte back as the error. -/
theorem binlog.consts.LoadDuplicateHandling.Insts.CoreConvertTryFromU8UnknownDuplicateHandling.try_from_spec (value : U8) :
    binlog.consts.LoadDuplicateHandling.Insts.CoreConvertTryFromU8UnknownDuplicateHandling.try_from value =
      ok (match loadDupOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  sorry

end mysql_common
