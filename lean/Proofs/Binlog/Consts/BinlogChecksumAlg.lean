import Defs

/-! Statements for `enum BinlogChecksumAlg and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `TryFrom<u8> for BinlogChecksumAlg`: total; `OFF` (0), `CRC32` (1), else the byte back as the error (also MySQL's `BINLOG_CHECKSUM_ALG_UNDEF`, 255). -/
theorem binlog.consts.BinlogChecksumAlg.Insts.CoreConvertTryFromU8UnknownChecksumAlg.try_from_spec (value : U8) :
    binlog.consts.BinlogChecksumAlg.Insts.CoreConvertTryFromU8UnknownChecksumAlg.try_from value =
      ok (match checksumAlgOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  sorry

end mysql_common
