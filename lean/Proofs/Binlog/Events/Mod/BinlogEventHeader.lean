import Defs

/-! Statements for `struct BinlogEventHeader and its impls` (spec file: `Specs/Binlog/Events.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `LEN`: 19. -/
theorem binlog.events.BinlogEventHeader.LEN_eq :
    binlog.events.BinlogEventHeader.LEN = 19#usize := by
  sorry

/-- `new`: those fields (the type as its code, the flags' bits). -/
theorem binlog.events.BinlogEventHeader.new_spec (ts : U32) (t : binlog.consts.EventType) (sid size pos : U32) (fl : binlog.consts.EventFlags) :
    binlog.events.BinlogEventHeader.new ts t sid size pos fl ⦃ h => h.timestamp.1 = ts ∧ h.event_type.1.val = evTypeCode t ∧
      h.server_id.1 = sid ∧ h.event_size.1 = size ∧ h.log_pos.1 = pos ∧ h.flags.1 = fl ⦄ := by
  sorry

/-- `timestamp`. -/
theorem binlog.events.BinlogEventHeader.impl.timestamp_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.timestamp h = ok h.timestamp.1 := by
  sorry

/-- `event_type_raw`: the type byte. -/
theorem binlog.events.BinlogEventHeader.event_type_raw_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.event_type_raw h = ok h.event_type.1 := by
  sorry

/-- `event_type`: the known type with that code, or the raw byte as an error. -/
theorem binlog.events.BinlogEventHeader.impl.event_type_spec (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.event_type h ⦃ r => match evTypeOfCode h.event_type.1.val with
      | some t => r = .Ok t
      | none => r = .Err h.event_type.1 ⦄ := by
  sorry

/-- `server_id`. -/
theorem binlog.events.BinlogEventHeader.impl.server_id_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.server_id h = ok h.server_id.1 := by
  sorry

/-- `event_size`. -/
theorem binlog.events.BinlogEventHeader.impl.event_size_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.event_size h = ok h.event_size.1 := by
  sorry

/-- `log_pos`. -/
theorem binlog.events.BinlogEventHeader.impl.log_pos_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.log_pos h = ok h.log_pos.1 := by
  sorry

/-- `flags`: the known flag bits (`from_bits_truncate`). -/
theorem binlog.events.BinlogEventHeader.impl.flags_spec (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.flags h ⦃ f => f.val = h.flags.1.val &&& eventFlagsAll ⦄ := by
  sorry

/-- `flags_raw`: all the flag bits. -/
theorem binlog.events.BinlogEventHeader.flags_raw_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.flags_raw h = ok h.flags.1 := by
  sorry

/-- `MyDeserialize::SIZE` is `Some(19)`. -/
theorem binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 19#usize := by
  sorry

/-- `MyDeserialize`: total; on at least 19 bytes the header whose layout is the first 19 (`evHeaderEnc` is injective, so this determines it), else an error with the buffer unchanged. -/
theorem binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      if 19 ≤ buf.length then (okPart r).map evHeaderEnc = some (buf.val.take 19) ∧ rest.val = buf.val.drop 19
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- `MySerialize`: appends the 19-byte header. -/
theorem binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMySerialize.serialize_spec (h : binlog.events.BinlogEventHeader) (buf : alloc.vec.Vec U8) (hb : buf.length + 19 ≤ Usize.max) :
    binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMySerialize.serialize h buf ⦃ buf' => buf'.val = buf.val ++ evHeaderEnc h ⦄ := by
  sorry

/-- Round trip: a written header reads back as itself. -/
theorem binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h : binlog.events.BinlogEventHeader) (tail : List U8) (buf : io.ParseBuf) (hb : buf.val = evHeaderEnc h ++ tail) :
    binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => okPart r = some h ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
