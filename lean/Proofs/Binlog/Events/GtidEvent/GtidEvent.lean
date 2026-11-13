import Defs

/-! Statements for `struct GtidEvent and its impls` (spec file: `Specs/Binlog/Events/GtidEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new(sid, gno)`: untagged, with the logical-clock part, everything else 0 (server versions 0, not `UNDEFINED_SERVER_VERSION`). -/
theorem binlog.events.gtid_event.GtidEvent.new_spec (sid : Array U8 16#usize) (gno : U64) :
    binlog.events.gtid_event.GtidEvent.new sid gno ⦃ e => gtidView e =
      { flags := 0, sid := sid.val, gno := gno.val, lc := true, lastCommitted := 0,
        sequenceNumber := 0, immediateCommitTs := 0, originalCommitTs := 0, txLength := 0,
        immediateServerVersion := 0, originalServerVersion := 0 } ∧
      e.tag = none ∧ e.serialization_version.val = 0 ∧ e.commit_group_ticket.val = 0 ⦄ := by
  sorry

/-- `new_tagged(sid, tag, gno)`: tagged (serialization version 2), no logical-clock part, server versions `UNDEFINED_SERVER_VERSION`. -/
theorem binlog.events.gtid_event.GtidEvent.new_tagged_spec (sid : Array U8 16#usize) (tag : packets.Tag) (gno : U64) :
    binlog.events.gtid_event.GtidEvent.new_tagged sid tag gno ⦃ e => gtidView e =
      { flags := 0, sid := sid.val, gno := gno.val, lc := false, lastCommitted := 0,
        sequenceNumber := 0, immediateCommitTs := 0, originalCommitTs := 0, txLength := 0,
        immediateServerVersion := undefinedServerVersion, originalServerVersion := undefinedServerVersion } ∧
      e.tag = some tag ∧ e.serialization_version.val = 2 ∧ e.commit_group_ticket.val = 0 ⦄ := by
  sorry

/-- `is_tagged`: whether there is a tag. -/
theorem binlog.events.gtid_event.GtidEvent.is_tagged_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.is_tagged e = ok e.tag.isSome := by
  sorry

/-- `event_type`: `GTID_TAGGED_LOG_EVENT` if tagged, else `GTID_EVENT`. -/
theorem binlog.events.gtid_event.GtidEvent.event_type_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.event_type e = ok (if e.tag.isSome then .GTID_TAGGED_LOG_EVENT else .GTID_EVENT) := by
  sorry

/-- `with_flags`. -/
theorem binlog.events.gtid_event.GtidEvent.with_flags_spec (e : binlog.events.gtid_event.GtidEvent) (f : binlog.consts.GtidFlags) :
    binlog.events.gtid_event.GtidEvent.with_flags e f = ok { e with flags := (f, ()) } := by
  sorry

/-- `flags_raw`: all the flag bits. -/
theorem binlog.events.gtid_event.GtidEvent.flags_raw_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.flags_raw e = ok e.flags.1 := by
  sorry

/-- `flags`: the known flag bits. -/
theorem binlog.events.gtid_event.GtidEvent.impl.flags_spec (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.flags e ⦃ f => f.val = e.flags.1.val &&& gtidFlagsAll ⦄ := by
  sorry

/-- `with_sid`. -/
theorem binlog.events.gtid_event.GtidEvent.with_sid_eq (e : binlog.events.gtid_event.GtidEvent) (s : Array U8 16#usize) :
    binlog.events.gtid_event.GtidEvent.with_sid e s = ok { e with sid := s } := by
  sorry

/-- `sid`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.sid_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.sid e = ok e.sid := by
  sorry

/-- `with_gno`. -/
theorem binlog.events.gtid_event.GtidEvent.with_gno_eq (e : binlog.events.gtid_event.GtidEvent) (g : U64) :
    binlog.events.gtid_event.GtidEvent.with_gno e g = ok { e with gno := (g, ()) } := by
  sorry

/-- `gno`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.gno_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.gno e = ok e.gno.1 := by
  sorry

/-- `tag`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.tag_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.tag e = ok e.tag := by
  sorry

/-- `with_tag`: the tag, and serialization version 2. -/
theorem binlog.events.gtid_event.GtidEvent.with_tag_eq (e : binlog.events.gtid_event.GtidEvent) (t : packets.Tag) :
    binlog.events.gtid_event.GtidEvent.with_tag e t = ok { e with tag := some t, serialization_version := 2#u8 } := by
  sorry

/-- `lc_typecode`: 2 iff the logical-clock part is present. -/
theorem binlog.events.gtid_event.GtidEvent.impl.lc_typecode_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.lc_typecode e = ok (if e.lc_typecode.isSome then some 2#u8 else none) := by
  sorry

/-- `with_lc_typecode`: adds the logical-clock part. -/
theorem binlog.events.gtid_event.GtidEvent.with_lc_typecode_spec (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.with_lc_typecode e ⦃ e' => gtidView e' = { gtidView e with lc := true } ∧ e'.tag = e.tag ⦄ := by
  sorry

/-- `with_last_committed`. -/
theorem binlog.events.gtid_event.GtidEvent.with_last_committed_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_last_committed e x = ok { e with last_committed := (x, ()) } := by
  sorry

/-- `last_committed`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.last_committed_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.last_committed e = ok e.last_committed.1 := by
  sorry

/-- `with_sequence_number`. -/
theorem binlog.events.gtid_event.GtidEvent.with_sequence_number_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_sequence_number e x = ok { e with sequence_number := (x, ()) } := by
  sorry

/-- `sequence_number`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.sequence_number_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.sequence_number e = ok e.sequence_number.1 := by
  sorry

/-- `with_immediate_commit_timestamp` (stored as given; 56 bits are written). -/
theorem binlog.events.gtid_event.GtidEvent.with_immediate_commit_timestamp_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_immediate_commit_timestamp e x = ok { e with immediate_commit_timestamp := (x, ()) } := by
  sorry

/-- `immediate_commit_timestamp`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.immediate_commit_timestamp_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.immediate_commit_timestamp e = ok e.immediate_commit_timestamp.1 := by
  sorry

/-- `with_original_commit_timestamp`. -/
theorem binlog.events.gtid_event.GtidEvent.with_original_commit_timestamp_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_original_commit_timestamp e x = ok { e with original_commit_timestamp := (x, ()) } := by
  sorry

/-- `original_commit_timestamp`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.original_commit_timestamp_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.original_commit_timestamp e = ok e.original_commit_timestamp.1 := by
  sorry

/-- `with_tx_length`. -/
theorem binlog.events.gtid_event.GtidEvent.with_tx_length_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_tx_length e x = ok { e with tx_length := (x, ()) } := by
  sorry

/-- `tx_length`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.tx_length_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.tx_length e = ok e.tx_length.1 := by
  sorry

/-- `with_original_server_version`. -/
theorem binlog.events.gtid_event.GtidEvent.with_original_server_version_eq (e : binlog.events.gtid_event.GtidEvent) (x : U32) :
    binlog.events.gtid_event.GtidEvent.with_original_server_version e x = ok { e with original_server_version := (x, ()) } := by
  sorry

/-- `original_server_version`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.original_server_version_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.original_server_version e = ok e.original_server_version.1 := by
  sorry

/-- `with_immediate_server_version`. -/
theorem binlog.events.gtid_event.GtidEvent.with_immediate_server_version_eq (e : binlog.events.gtid_event.GtidEvent) (x : U32) :
    binlog.events.gtid_event.GtidEvent.with_immediate_server_version e x = ok { e with immediate_server_version := (x, ()) } := by
  sorry

/-- `immediate_server_version`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.immediate_server_version_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.immediate_server_version e = ok e.immediate_server_version.1 := by
  sorry

/-- `commit_group_ticket`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.commit_group_ticket_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.commit_group_ticket e = ok e.commit_group_ticket := by
  sorry

/-- `with_commit_group_ticket`. -/
theorem binlog.events.gtid_event.GtidEvent.with_commit_group_ticket_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_commit_group_ticket e x = ok { e with commit_group_ticket := x } := by
  sorry

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  sorry

/-- `MyDeserialize` for `GTID_EVENT` (33) and `ANONYMOUS_GTID_EVENT` (34): total; `gtidRead`; untagged, serialization version 0, no commit group ticket. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_untagged (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val = 33 ∨ ctx.event_type_raw.val = 34) (buf : io.ParseBuf) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs gtidView (gtidRead buf.val) r rest ∧
      ∀ e, okPart r = some e → e.tag = none ∧ e.serialization_version.val = 0 ∧ e.commit_group_ticket.val = 0 ⦄ := by
  sorry

/-- `MyDeserialize` for `GTID_TAGGED_LOG_EVENT` (42): the (opaque) tagged reader. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_tagged (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val = 42) (buf : io.ParseBuf) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf = binlog.events.gtid_event.GtidEvent.deserialize_tagged buf := by
  sorry

/-- `MyDeserialize` with any other event type in the context: an error. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_other (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val ∉ [33, 34, 42]) (buf : io.ParseBuf) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r _ => okPart r = none ⦄ := by
  sorry

/-- `MySerialize` of an untagged event: appends `gtidEnc`. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag = none) (buf : alloc.vec.Vec U8)
    (h : buf.length + (gtidEnc e).length ≤ Usize.max) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ gtidEnc e ⦄ := by
  sorry

/-- `MySerialize` of a tagged event: the (opaque) tagged writer. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize_tagged (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag.isSome) (buf : alloc.vec.Vec U8) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf = binlog.events.gtid_event.GtidEvent.serialize_tagged e buf := by
  sorry

/-- Round trip (untagged, with the logical-clock part): the event reads back, for timestamps below `2^55` (immediate) and `2^56` (original) and an immediate server version below `2^31`; bytes after it are left. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag = none) (hlc : e.lc_typecode.isSome)
    (hi : e.immediate_commit_timestamp.1.val < 2 ^ 55) (ho : e.original_commit_timestamp.1.val < 2 ^ 56)
    (hs : e.immediate_server_version.1.val < 2 ^ 31)
    (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val = 33 ∨ ctx.event_type_raw.val = 34)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = gtidEnc e ++ tail) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map gtidView = some (gtidView e) ∧ rest.val = tail ⦄ := by
  sorry

/-- Round trip of an untagged event without the logical-clock part (pre-5.7): the 25-byte prefix reads back with the defaults (zeros, server versions `UNDEFINED_SERVER_VERSION`), provided the following bytes do not start with `2`. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip_no_lc (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag = none) (hlc : e.lc_typecode = none)
    (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val = 33 ∨ ctx.event_type_raw.val = 34)
    (tail : List U8) (hb : tail.head?.map (·.val) ≠ some 2) (buf : io.ParseBuf) (h : buf.val = gtidEnc e ++ tail) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map gtidView = some
      { gtidView e with
        lc := false, lastCommitted := 0, sequenceNumber := 0, immediateCommitTs := 0,
        originalCommitTs := 0, txLength := 0, immediateServerVersion := undefinedServerVersion,
        originalServerVersion := undefinedServerVersion } ∧ rest.val = tail ⦄ := by
  sorry

/-- `BinlogStruct::len` of an untagged event: `gtidLenCrate`, which always counts the logical-clock part. **Quirk:** without it (`lc_typecode` `None`) `serialize` writes 25 bytes but `len` is at least 54 (`Defs.gtidLenCrate_ne`); with it, `len` is the length of `gtidEnc` (`Defs.gtidLenCrate_eq`). -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag = none) (v : binlog.consts.BinlogVersion) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = gtidLenCrate e ⦄ := by
  sorry

/-- `BinlogStruct::len` of a tagged event: the (opaque) tagged length. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_tagged (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag.isSome) (v : binlog.consts.BinlogVersion) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = binlog.events.gtid_event.GtidEvent.len_tagged e := by
  sorry

/-- `BinlogEvent::EVENT_TYPE`: `GTID_EVENT` (33). -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .GTID_EVENT := by
  sorry

end mysql_common
