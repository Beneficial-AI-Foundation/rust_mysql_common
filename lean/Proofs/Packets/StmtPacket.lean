import Defs

/-! Statements for `struct StmtPacket and its impls` (spec file: `Specs/Packets/StmtBinlog.lean`).
Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MyDeserialize for StmtPacket`: `SIZE` is `Some(12)`. -/
theorem packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 12#usize := by
  sorry

/-- `MyDeserialize for StmtPacket`: total; `stmtOkRead` (12 bytes, status `0x00`). -/
theorem packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map StmtOk.of, rest.val) = stmtOkRead buf.val ⦄ := by
  sorry

/-- Round trip: a `COM_STMT_PREPARE_OK` in the protocol layout (`stmtOkEnc`) is read back. -/
theorem packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (p : packets.StmtPacket) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = stmtOkEnc (StmtOk.of p) ++ tail) :
    packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map StmtOk.of = some (StmtOk.of p) ∧ rest.val = tail ⦄ := by
  sorry

/-- `MySerialize for StmtPacket`: appends the 12 bytes `stmtOkEnc` (status and filler `0x00`). -/
theorem packets.StmtPacket.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.StmtPacket) (buf : alloc.vec.Vec U8) (h : buf.length + 12 ≤ Usize.max) :
    packets.StmtPacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ stmtOkEnc (StmtOk.of self) ⦄ := by
  sorry

/-- `statement_id`: the field. -/
theorem packets.StmtPacket.impl.statement_id_eq (self : packets.StmtPacket) :
    packets.StmtPacket.impl.statement_id self = ok self.statement_id.1 := by
  sorry

/-- `num_columns`: the field. -/
theorem packets.StmtPacket.impl.num_columns_eq (self : packets.StmtPacket) :
    packets.StmtPacket.impl.num_columns self = ok self.num_columns.1 := by
  sorry

/-- `num_params`: the field. -/
theorem packets.StmtPacket.impl.num_params_eq (self : packets.StmtPacket) :
    packets.StmtPacket.impl.num_params self = ok self.num_params.1 := by
  sorry

/-- `warning_count`: the field. -/
theorem packets.StmtPacket.impl.warning_count_eq (self : packets.StmtPacket) :
    packets.StmtPacket.impl.warning_count self = ok self.warning_count.1 := by
  sorry

end mysql_common
