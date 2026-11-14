import Defs
import Proofs.Util.BinlogConsts

/-! Statements for `enum IntvarEventType and its impls` (spec file: `Specs/Binlog/Consts.lean`). Helper lemmas: `Proofs/Util/BinlogConsts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.BinlogConstsUtil

namespace mysql_common

/-- `From<IntvarEventType> for u8`: the code. -/
@[step]
theorem U8.Insts.CoreConvertFromIntvarEventType.from_spec (x : binlog.consts.IntvarEventType) :
    U8.Insts.CoreConvertFromIntvarEventType.from x ⦃ r => r.val = intvarTypeCode x ⦄ := by
  cases x <;> simp [U8.Insts.CoreConvertFromIntvarEventType.from, intvarTypeCode, read_discriminant,
    binlog.consts.IntvarEventType.read_discriminant]

/-- `TryFrom<u8> for IntvarEventType`: total; the type with that code (0–2), or the byte back as the error. -/
theorem binlog.consts.IntvarEventType.Insts.CoreConvertTryFromU8UnknownIntvarEventType.try_from_spec (value : U8) :
    binlog.consts.IntvarEventType.Insts.CoreConvertTryFromU8UnknownIntvarEventType.try_from value =
      ok (match intvarTypeOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  obtain ⟨⟨⟨n, hn⟩⟩⟩ := value
  change n < 256 at hn
  have h := hn
  repeat (obtain h | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h); swap; · rfl)
  exact absurd h (Nat.not_lt_zero _)

end mysql_common
