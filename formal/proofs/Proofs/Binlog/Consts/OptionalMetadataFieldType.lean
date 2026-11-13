import Defs
import Proofs.Util.BinlogConsts

/-! Statements for `enum OptionalMetadataFieldType and its impls` (spec file: `Specs/Binlog/Consts.lean`). Helper lemmas: `Proofs/Util/BinlogConsts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.BinlogConstsUtil

namespace mysql_common

/-- `TryFrom<u8> for OptionalMetadataFieldType`: total; the field type with that code (1–13), or the byte back as the error. -/
theorem binlog.consts.OptionalMetadataFieldType.Insts.CoreConvertTryFromU8UnknownOptionalMetadataFieldType.try_from_spec (value : U8) :
    binlog.consts.OptionalMetadataFieldType.Insts.CoreConvertTryFromU8UnknownOptionalMetadataFieldType.try_from value =
      ok (match optMetaFieldOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  obtain ⟨⟨⟨n, hn⟩⟩⟩ := value
  change n < 256 at hn
  have h := hn
  repeat (obtain h | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h); swap; · rfl)
  exact absurd h (Nat.not_lt_zero _)

end mysql_common
