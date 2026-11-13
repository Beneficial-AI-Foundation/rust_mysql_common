import Defs

/-! Statements for `struct BinlogEventFooter and its impls` (spec file: `Specs/Binlog/Events.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `BINLOG_CHECKSUM_ALG_DESC_LEN`: 1. -/
theorem binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_ALG_DESC_LEN_eq :
    binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_ALG_DESC_LEN = 1#usize := by
  sorry

/-- `BINLOG_CHECKSUM_LEN`: 4. -/
theorem binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_LEN_eq :
    binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_LEN = 4#usize := by
  sorry

/-- `new(alg)`: that algorithm, checksums enabled. -/
theorem binlog.events.BinlogEventFooter.new_spec (alg : binlog.consts.BinlogChecksumAlg) :
    binlog.events.BinlogEventFooter.new alg ⦃ f => footerAlg f = some (checksumAlgCode alg) ∧ f.checksum_enabled = true ⦄ := by
  sorry

/-- `get_checksum_alg`: `Ok(None)` without an algorithm, the known algorithm, or the raw code as an error. -/
theorem binlog.events.BinlogEventFooter.get_checksum_alg_spec (f : binlog.events.BinlogEventFooter) :
    binlog.events.BinlogEventFooter.get_checksum_alg f ⦃ r => match footerAlg f with
      | none => r = .Ok none
      | some a => match checksumAlgOfCode a with
        | some alg => r = .Ok (some alg)
        | none => r = .Err (byte a) ⦄ := by
  sorry

/-- `get_checksum_enabled`. -/
theorem binlog.events.BinlogEventFooter.get_checksum_enabled_eq (f : binlog.events.BinlogEventFooter) :
    binlog.events.BinlogEventFooter.get_checksum_enabled f = ok f.checksum_enabled := by
  sorry

/-- `set_checksum_enabled`. -/
theorem binlog.events.BinlogEventFooter.set_checksum_enabled_eq (f : binlog.events.BinlogEventFooter) (b : Bool) :
    binlog.events.BinlogEventFooter.set_checksum_enabled f b = ok { f with checksum_enabled := b } := by
  sorry

/-- `Default`: algorithm `OFF` (0), checksums enabled. -/
theorem binlog.events.BinlogEventFooter.Insts.CoreDefaultDefault.default_spec :
    binlog.events.BinlogEventFooter.Insts.CoreDefaultDefault.default ⦃ f => footerAlg f = some 0 ∧ f.checksum_enabled = true ⦄ := by
  sorry

end mysql_common
