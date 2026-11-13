import Defs
import Proofs.Util.BinlogConsts

/-! Statements for `enum LoadDuplicateHandling and its impls` (spec file: `Specs/Binlog/Consts.lean`). Helper lemmas: `Proofs/Util/BinlogConsts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.BinlogConstsUtil

namespace mysql_common

/-- `From<LoadDuplicateHandling> for u8`: the code. -/
@[step]
theorem U8.Insts.CoreConvertFromLoadDuplicateHandling.from_spec (x : binlog.consts.LoadDuplicateHandling) :
    U8.Insts.CoreConvertFromLoadDuplicateHandling.from x ⦃ r => r.val = loadDupCode x ⦄ := by
  cases x <;> simp [U8.Insts.CoreConvertFromLoadDuplicateHandling.from, loadDupCode, read_discriminant,
    binlog.consts.LoadDuplicateHandling.read_discriminant]

/-- `TryFrom<u8> for LoadDuplicateHandling`: total; the handling with that code (0–2), or the byte back as the error. -/
theorem binlog.consts.LoadDuplicateHandling.Insts.CoreConvertTryFromU8UnknownDuplicateHandling.try_from_spec (value : U8) :
    binlog.consts.LoadDuplicateHandling.Insts.CoreConvertTryFromU8UnknownDuplicateHandling.try_from value =
      ok (match loadDupOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  obtain ⟨⟨⟨n, hn⟩⟩⟩ := value
  change n < 256 at hn
  have h := hn
  repeat (obtain h | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h); swap; · rfl)
  exact absurd h (Nat.not_lt_zero _)

end mysql_common
