import Defs

/-! Statements for `struct ComStmtClose and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ComStmtClose::new(stmt_id)`: the statement id. -/
theorem packets.ComStmtClose.new_eq (stmt_id : U32) :
    packets.ComStmtClose.new stmt_id = ok ⟨stmt_id⟩ := by
  sorry

/-- `MySerialize for ComStmtClose`: appends the protocol's packet `stmtCloseEnc` (`0x19`, the
    statement id). -/
theorem packets.ComStmtClose.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComStmtClose) (buf : alloc.vec.Vec U8) (h : buf.length + 5 ≤ Usize.max) :
    packets.ComStmtClose.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ stmtCloseEnc self.stmt_id.val ⦄ := by
  sorry

end mysql_common
