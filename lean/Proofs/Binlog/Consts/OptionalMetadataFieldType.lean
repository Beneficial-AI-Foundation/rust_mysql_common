import Defs

/-! Statements for `enum OptionalMetadataFieldType and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `TryFrom<u8> for OptionalMetadataFieldType`: total; the field type with that code (1–13), or the byte back as the error. -/
theorem binlog.consts.OptionalMetadataFieldType.Insts.CoreConvertTryFromU8UnknownOptionalMetadataFieldType.try_from_spec (value : U8) :
    binlog.consts.OptionalMetadataFieldType.Insts.CoreConvertTryFromU8UnknownOptionalMetadataFieldType.try_from value =
      ok (match optMetaFieldOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  sorry

end mysql_common
