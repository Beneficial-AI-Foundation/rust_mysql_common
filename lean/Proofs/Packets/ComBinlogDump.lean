import Defs

/-! Statements for `struct ComBinlogDump and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ComBinlogDump::new(server_id)`: position 0, no flags, the server id, an empty file name. -/
theorem packets.ComBinlogDump.new_spec (server_id : U32) :
    packets.ComBinlogDump.new server_id ⦃ d => BinlogDump.of d = ⟨0, 0, server_id.val, []⟩ ⦄ := by
  sorry

/-- `with_pos`: sets the position; nothing else changes. -/
theorem packets.ComBinlogDump.with_pos_spec (self : packets.ComBinlogDump) (pos : U32) :
    packets.ComBinlogDump.with_pos self pos ⦃ d =>
      BinlogDump.of d = { BinlogDump.of self with pos := pos.val } ⦄ := by
  sorry

/-- `with_flags`: sets the flags; nothing else changes. -/
theorem packets.ComBinlogDump.with_flags_spec (self : packets.ComBinlogDump) (flags : packets.BinlogDumpFlags) :
    packets.ComBinlogDump.with_flags self flags ⦃ d =>
      BinlogDump.of d = { BinlogDump.of self with flags := flags.val } ⦄ := by
  sorry

/-- `with_filename`: sets the file name (`filename.into()`); nothing else changes. -/
theorem packets.ComBinlogDump.with_filename_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComBinlogDump) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComBinlogDump.with_filename into self x ⦃ d =>
      BinlogDump.of d = { BinlogDump.of self with filename := cowList c } ⦄ := by
  sorry

/-- `pos`: the field. -/
theorem packets.ComBinlogDump.impl.pos_eq (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.impl.pos self = ok self.pos.1 := by
  sorry

/-- `flags`: the field. -/
theorem packets.ComBinlogDump.impl.flags_eq (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.impl.flags self = ok self.flags.1 := by
  sorry

/-- `server_id`: the field. -/
theorem packets.ComBinlogDump.impl.server_id_eq (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.impl.server_id self = ok self.server_id.1 := by
  sorry

/-- `filename_raw`: the file name. -/
theorem packets.ComBinlogDump.filename_raw_spec (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.filename_raw self ⦃ s => s.val = cowList self.filename.1 ⦄ := by
  sorry

/-- `filename`: the file name as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComBinlogDump.impl.filename_spec (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.impl.filename self ⦃ c => LossyUtf8 (cowList self.filename.1) c ⦄ := by
  sorry

/-- `MySerialize for ComBinlogDump`: appends the protocol's packet `binlogDumpEnc`. -/
theorem packets.ComBinlogDump.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComBinlogDump) (buf : alloc.vec.Vec U8)
    (h : buf.length + (binlogDumpEnc (BinlogDump.of self)).length ≤ Usize.max) :
    packets.ComBinlogDump.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ binlogDumpEnc (BinlogDump.of self) ⦄ := by
  sorry

/-- `MyDeserialize for ComBinlogDump`: `SIZE` is `None`. -/
theorem packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for ComBinlogDump`: total; `binlogDumpRead` (11 bytes, then the file name is
    the rest of the input). -/
theorem packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map BinlogDump.of, rest.val) = binlogDumpRead buf.val ⦄ := by
  sorry

/-- Round trip: a packet with known flags, in the protocol layout, is read back (the file name
    takes the rest of the input). -/
theorem packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (d : packets.ComBinlogDump)
    (hf : (BinlogDump.of d).flags &&& binlogDumpFlagsAll = (BinlogDump.of d).flags)
    (buf : io.ParseBuf) (h : buf.val = binlogDumpEnc (BinlogDump.of d)) :
    packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map BinlogDump.of = some (BinlogDump.of d) ∧ rest.val = [] ⦄ := by
  sorry

end mysql_common
