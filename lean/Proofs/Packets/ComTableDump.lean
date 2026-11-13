import Defs

/-! Statements for `struct ComTableDump and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ComTableDump::new(database, table)`: the two names (`into()`, not truncated). -/
theorem packets.ComTableDump.new_spec {T1 T2 : Type}
    (into1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (into2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (database : T1) (table : T2) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h1 : into1.into database = ok c1) (h2 : into2.into table = ok c2) :
    packets.ComTableDump.new into1 into2 database table ⦃ t =>
      cowList t.database.1 = cowList c1 ∧ cowList t.table.1 = cowList c2 ⦄ := by
  sorry

/-- `database_raw`: the database's effective bytes (at most the first 255). -/
theorem packets.ComTableDump.database_raw_spec (self : packets.ComTableDump) :
    packets.ComTableDump.database_raw self ⦃ s => s.val = (cowList self.database.1).take 255 ⦄ := by
  sorry

/-- `database`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComTableDump.impl.database_spec (self : packets.ComTableDump) :
    packets.ComTableDump.impl.database self ⦃ c => LossyUtf8 ((cowList self.database.1).take 255) c ⦄ := by
  sorry

/-- `table_raw`: the table's effective bytes (at most the first 255). -/
theorem packets.ComTableDump.table_raw_spec (self : packets.ComTableDump) :
    packets.ComTableDump.table_raw self ⦃ s => s.val = (cowList self.table.1).take 255 ⦄ := by
  sorry

/-- `table`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComTableDump.impl.table_spec (self : packets.ComTableDump) :
    packets.ComTableDump.impl.table self ⦃ c => LossyUtf8 ((cowList self.table.1).take 255) c ⦄ := by
  sorry

/-- `MySerialize for ComTableDump`: appends `tableDumpEnc` (`0x13`, the two names with 1-byte
    lengths, truncated to 255 bytes: documented). -/
theorem packets.ComTableDump.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComTableDump) (buf : alloc.vec.Vec U8)
    (h : buf.length + (tableDumpEnc (cowList self.database.1) (cowList self.table.1)).length ≤ Usize.max) :
    packets.ComTableDump.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ tableDumpEnc (cowList self.database.1) (cowList self.table.1) ⦄ := by
  sorry

/-- `MyDeserialize for ComTableDump`: `SIZE` is `None`. -/
theorem packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for ComTableDump`: total; `tableDumpRead`. -/
theorem packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun t => (cowList t.database.1, cowList t.table.1)), rest.val) =
        tableDumpRead buf.val ⦄ := by
  sorry

/-- Round trip: names of at most 255 bytes, in the protocol layout, are read back. -/
theorem packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (db tbl : List U8) (hdb : db.length ≤ 255) (htbl : tbl.length ≤ 255) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = tableDumpEnc db tbl ++ tail) :
    packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun t => (cowList t.database.1, cowList t.table.1)) = some (db, tbl) ∧
      rest.val = tail ⦄ := by
  sorry

end mysql_common
