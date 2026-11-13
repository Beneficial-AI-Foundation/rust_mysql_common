import Defs

/-! Statements for `enum IntvarEventType and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `From<IntvarEventType> for u8`: the code. -/
theorem U8.Insts.CoreConvertFromIntvarEventType.from_spec (x : binlog.consts.IntvarEventType) :
    U8.Insts.CoreConvertFromIntvarEventType.from x ⦃ r => r.val = intvarTypeCode x ⦄ := by
  sorry

/-- `TryFrom<u8> for IntvarEventType`: total; the type with that code (0–2), or the byte back as the error. -/
theorem binlog.consts.IntvarEventType.Insts.CoreConvertTryFromU8UnknownIntvarEventType.try_from_spec (value : U8) :
    binlog.consts.IntvarEventType.Insts.CoreConvertTryFromU8UnknownIntvarEventType.try_from value =
      ok (match intvarTypeOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  sorry

end mysql_common
