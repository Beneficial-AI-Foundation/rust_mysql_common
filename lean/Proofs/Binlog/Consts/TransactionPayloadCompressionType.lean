import Defs
import Proofs.Util.BinlogConsts

/-! Statements for `enum TransactionPayloadCompressionType and its impls` (spec file: `Specs/Binlog/Consts.lean`). Helper lemmas: `Proofs/Util/BinlogConsts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.BinlogConstsUtil

namespace mysql_common

/-- `TryFrom<u8> for TransactionPayloadCompressionType`: total; the compression type (`ZSTD` = 0, `NONE` = 255) with that code, or the byte back as the error. -/
theorem binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU8UnknownTransactionPayloadCompressionType.try_from_spec (value : U8) :
    binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU8UnknownTransactionPayloadCompressionType.try_from value =
      ok (match txCompressionOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  obtain ⟨⟨⟨n, hn⟩⟩⟩ := value
  change n < 256 at hn
  have h := hn
  repeat (obtain h | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h); swap; · rfl)
  exact absurd h (Nat.not_lt_zero _)

/-- `TryFrom<u64> for TransactionPayloadCompressionType`, for values below 256: the compression type (`ZSTD` = 0, `NONE` = 255) with that code, or the value (as a byte) back as the error. -/
theorem binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU64UnknownTransactionPayloadCompressionType.try_from_spec (value : U64) (h : value.val < 256) :
    binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU64UnknownTransactionPayloadCompressionType.try_from value =
      ok (match txCompressionOfCode value.val with
        | some x => .Ok x
        | none => .Err (byte value.val)) := by
  unfold binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU64UnknownTransactionPayloadCompressionType.try_from
  split
  all_goals first | rfl | rw [u8_tryFrom_u64_unwrap_lt _ h]
  all_goals simp_all [uscalar_eq_iff, uscalar_mk_val, txCompressionOfCode, txCompressionCode, List.find?]

/-- **Crash path.** `TryFrom<u64> for TransactionPayloadCompressionType` panics on every value of 256 or more: the error payload is a `u8`, built with `x.try_into().unwrap()`. The value is read from the wire (a `TransactionPayloadEvent` header field), so a malformed event crashes the reader. -/
theorem binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU64UnknownTransactionPayloadCompressionType.try_from_panics (value : U64) (h : 256 ≤ value.val) :
    binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU64UnknownTransactionPayloadCompressionType.try_from value = fail .panic := by
  unfold binlog.consts.TransactionPayloadCompressionType.Insts.CoreConvertTryFromU64UnknownTransactionPayloadCompressionType.try_from
  split
  all_goals first | exact u8_tryFrom_u64_unwrap_ge _ h _ | simp_all [uscalar_mk_val]

end mysql_common
