import Defs
import Proofs.Util.BinlogConsts

/-! Statements for `enum StatusVarKey and its impls` (spec file: `Specs/Binlog/Consts.lean`). Helper lemmas: `Proofs/Util/BinlogConsts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.BinlogConstsUtil

namespace mysql_common

/-- `TryFrom<u8> for StatusVarKey`: total; the query-event status variable with that code (MySQL's `Q_*` codes 0–20), or the byte back as the error. -/
theorem binlog.consts.StatusVarKey.Insts.CoreConvertTryFromU8UnknownStatusVarKey.try_from_spec (value : U8) :
    binlog.consts.StatusVarKey.Insts.CoreConvertTryFromU8UnknownStatusVarKey.try_from value =
      ok (match statusVarKeyOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  obtain ⟨⟨⟨n, hn⟩⟩⟩ := value
  change n < 256 at hn
  have h := hn
  repeat (obtain h | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h); swap; · rfl)
  exact absurd h (Nat.not_lt_zero _)

end mysql_common
