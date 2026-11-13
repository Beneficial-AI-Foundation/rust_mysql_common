import Defs
import Proofs.Util.IntAndMisc

/-! Statements for `struct ComStmtClose and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ComStmtClose::new(stmt_id)`: the statement id. -/
theorem packets.ComStmtClose.new_eq (stmt_id : U32) :
    packets.ComStmtClose.new stmt_id = ok ⟨stmt_id⟩ := by
  rfl

/-- `MySerialize for ComStmtClose`: appends the protocol's packet `stmtCloseEnc` (`0x19`, the
    statement id). -/
theorem packets.ComStmtClose.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComStmtClose) (buf : alloc.vec.Vec U8) (h : buf.length + 5 ≤ Usize.max) :
    packets.ComStmtClose.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ stmtCloseEnc self.stmt_id.val ⦄ := by
  unfold packets.ComStmtClose.Insts.Mysql_commonProtoMySerialize.serialize
  step as ⟨ i, i_post ⟩
  step as ⟨ i1, i1_post ⟩
  have hi : i1 = byte 0x19 := by
    rw [i1_post]; apply UScalar.eq_of_val_eq; simp [byte, i_post]; rfl
  step as ⟨ buf1, buf1_post ⟩
  step as ⟨ buf', buf'_post ⟩
  · simp [alloc.vec.Vec.length, buf1_post] at *; scalar_tac
  simp [buf'_post, buf1_post, hi, stmtCloseEnc]

end mysql_common
