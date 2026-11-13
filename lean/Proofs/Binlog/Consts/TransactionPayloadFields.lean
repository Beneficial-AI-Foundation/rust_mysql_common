import Defs

/-! Statements for `enum TransactionPayloadFields and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `TryFrom<u8> for TransactionPayloadFields`: total; the header field with that code, or the byte back as the error. -/
theorem binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU8UnknownTransactionPayloadFields.try_from_spec (value : U8) :
    binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU8UnknownTransactionPayloadFields.try_from value =
      ok (match txPayloadFieldOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  sorry

/-- `TryFrom<u64> for TransactionPayloadFields`, for values below 256: the header field with that code, or the value (as a byte) back as the error. -/
theorem binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU64UnknownTransactionPayloadFields.try_from_spec (value : U64) (h : value.val < 256) :
    binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU64UnknownTransactionPayloadFields.try_from value =
      ok (match txPayloadFieldOfCode value.val with
        | some x => .Ok x
        | none => .Err (byte value.val)) := by
  sorry

/-- **Crash path.** `TryFrom<u64> for TransactionPayloadFields` panics on every value of 256 or more: the error payload is a `u8`, built with `x.try_into().unwrap()`. The value is read from the wire (a `TransactionPayloadEvent` header field), so a malformed event crashes the reader. -/
theorem binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU64UnknownTransactionPayloadFields.try_from_panics (value : U64) (h : 256 ≤ value.val) :
    binlog.consts.TransactionPayloadFields.Insts.CoreConvertTryFromU64UnknownTransactionPayloadFields.try_from value = fail .panic := by
  sorry

end mysql_common
