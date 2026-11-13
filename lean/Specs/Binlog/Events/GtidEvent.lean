import Proofs.Binlog.Events.GtidEvent.GtidEvent

/-!
# `src/binlog/events/gtid_event.rs`
    `GtidEvent` (`GTID_LOG_EVENT` 33, also `ANONYMOUS_GTID_LOG_EVENT` 34, and the tagged
    `GTID_TAGGED_LOG_EVENT` 42). Covered: `new`, `new_tagged`, `is_tagged`, `event_type`, every
    `with_*` and accessor, `SIZE`, `deserialize` (exact on any input for the untagged format, the
    tagged one as the opaque reader), `serialize` (exact untagged), the untagged round trip, `len`
    (exact, with the quirk below), `EVENT_TYPE`.

    **Configuration.** As in `Specs/Io.lean` (feature `binlog_core`; patches 140–155).
    **Caveats.** Allocation is infallible, overflow is a panic (debug semantics), the stack is not
    modelled. When a reader fails, what it leaves of the buffer is not stated.

    **Definitions used.** `Defs/BinlogEvents.lean` (`GtidView`, `gtidView`, `gtidEnc`, `gtidRead`,
    `gtidLenCrate`, `undefinedServerVersion`, `gtidFlagsAll`, `evLenCap`, `ReadsAs`, `optFst`),
    `Defs/LenEnc.lean` (`lenencInt`, `checkedLenencInt`), `Defs/Bytes.lean`.

    **Trusted axioms.** None of namespace `Trusted`. Opaque (nothing assumed): `io::Error`, and the
    tagged format (`GtidEvent::deserialize_tagged`, `serialize_tagged`, `len_tagged`, opaque in
    Cargo.toml): the statements for tagged events say only that these are called.

    **Not covered.** The tagged (MySQL 8.4) serialization format itself (opaque; it needs `Tag`'s
    validation and `format!`); `Tag` values (`packets::Tag`, other area); the private helpers
    (covered through `deserialize` / `serialize` / `len`); the derived impls.

    **Behaviour to note.**
    * **`len` always counts the logical-clock part**, also for an untagged event without it (one
      read from a pre-5.7 server, whose `lc_typecode` is `None`): `serialize` then writes only 25
      bytes, while `len` says at least 42 (`len_spec`, `gtidLenCrate`).
    * `serialize` drops `commit_group_ticket` (untagged format), and writes the low 56 bits of the
      commit timestamps and 31 bits of the immediate server version (the top bit is the flag).
    * The reader leaves bytes after the server versions unread (MySQL 8.0.33+ can append
      `commit_group_ticket`), which `Event::read_event` turns into an error.
    * `deserialize` with an event type other than 33, 34, 42 in the context is an error.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct GtidEvent and its impls` -/

/-- `new(sid, gno)`: untagged, with the logical-clock part, everything else 0 (server versions 0, not `UNDEFINED_SERVER_VERSION`). -/
recall binlog.events.gtid_event.GtidEvent.new_spec (sid : Array U8 16#usize) (gno : U64) :
    binlog.events.gtid_event.GtidEvent.new sid gno ⦃ e => gtidView e =
      { flags := 0, sid := sid.val, gno := gno.val, lc := true, lastCommitted := 0,
        sequenceNumber := 0, immediateCommitTs := 0, originalCommitTs := 0, txLength := 0,
        immediateServerVersion := 0, originalServerVersion := 0 } ∧
      e.tag = none ∧ e.serialization_version.val = 0 ∧ e.commit_group_ticket.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.new_spec`

/-- `new_tagged(sid, tag, gno)`: tagged (serialization version 2), no logical-clock part, server versions `UNDEFINED_SERVER_VERSION`. -/
recall binlog.events.gtid_event.GtidEvent.new_tagged_spec (sid : Array U8 16#usize) (tag : packets.Tag) (gno : U64) :
    binlog.events.gtid_event.GtidEvent.new_tagged sid tag gno ⦃ e => gtidView e =
      { flags := 0, sid := sid.val, gno := gno.val, lc := false, lastCommitted := 0,
        sequenceNumber := 0, immediateCommitTs := 0, originalCommitTs := 0, txLength := 0,
        immediateServerVersion := undefinedServerVersion, originalServerVersion := undefinedServerVersion } ∧
      e.tag = some tag ∧ e.serialization_version.val = 2 ∧ e.commit_group_ticket.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.new_tagged_spec`

/-- `is_tagged`: whether there is a tag. -/
recall binlog.events.gtid_event.GtidEvent.is_tagged_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.is_tagged e = ok e.tag.isSome

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.is_tagged_eq`

/-- `event_type`: `GTID_TAGGED_LOG_EVENT` if tagged, else `GTID_EVENT`. -/
recall binlog.events.gtid_event.GtidEvent.event_type_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.event_type e = ok (if e.tag.isSome then .GTID_TAGGED_LOG_EVENT else .GTID_EVENT)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.event_type_eq`

/-- `with_flags`. -/
recall binlog.events.gtid_event.GtidEvent.with_flags_spec (e : binlog.events.gtid_event.GtidEvent) (f : binlog.consts.GtidFlags) :
    binlog.events.gtid_event.GtidEvent.with_flags e f = ok { e with flags := (f, ()) }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.with_flags_spec`

/-- `flags_raw`: all the flag bits. -/
recall binlog.events.gtid_event.GtidEvent.flags_raw_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.flags_raw e = ok e.flags.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.flags_raw_eq`

/-- `flags`: the known flag bits. -/
recall binlog.events.gtid_event.GtidEvent.impl.flags_spec (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.flags e ⦃ f => f.val = e.flags.1.val &&& gtidFlagsAll ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.impl.flags_spec`

/-- `with_sid`. -/
recall binlog.events.gtid_event.GtidEvent.with_sid_eq (e : binlog.events.gtid_event.GtidEvent) (s : Array U8 16#usize) :
    binlog.events.gtid_event.GtidEvent.with_sid e s = ok { e with sid := s }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.with_sid_eq`

/-- `sid`. -/
recall binlog.events.gtid_event.GtidEvent.impl.sid_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.sid e = ok e.sid

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.impl.sid_eq`

/-- `with_gno`. -/
recall binlog.events.gtid_event.GtidEvent.with_gno_eq (e : binlog.events.gtid_event.GtidEvent) (g : U64) :
    binlog.events.gtid_event.GtidEvent.with_gno e g = ok { e with gno := (g, ()) }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.with_gno_eq`

/-- `gno`. -/
recall binlog.events.gtid_event.GtidEvent.impl.gno_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.gno e = ok e.gno.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.impl.gno_eq`

/-- `tag`. -/
recall binlog.events.gtid_event.GtidEvent.impl.tag_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.tag e = ok e.tag

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.impl.tag_eq`

/-- `with_tag`: the tag, and serialization version 2. -/
recall binlog.events.gtid_event.GtidEvent.with_tag_eq (e : binlog.events.gtid_event.GtidEvent) (t : packets.Tag) :
    binlog.events.gtid_event.GtidEvent.with_tag e t = ok { e with tag := some t, serialization_version := 2#u8 }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.with_tag_eq`

/-- `lc_typecode`: 2 iff the logical-clock part is present. -/
recall binlog.events.gtid_event.GtidEvent.impl.lc_typecode_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.lc_typecode e = ok (if e.lc_typecode.isSome then some 2#u8 else none)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.impl.lc_typecode_eq`

/-- `with_lc_typecode`: adds the logical-clock part. -/
recall binlog.events.gtid_event.GtidEvent.with_lc_typecode_spec (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.with_lc_typecode e ⦃ e' => gtidView e' = { gtidView e with lc := true } ∧ e'.tag = e.tag ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.with_lc_typecode_spec`

/-- `with_last_committed`. -/
recall binlog.events.gtid_event.GtidEvent.with_last_committed_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_last_committed e x = ok { e with last_committed := (x, ()) }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.with_last_committed_eq`

/-- `last_committed`. -/
recall binlog.events.gtid_event.GtidEvent.impl.last_committed_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.last_committed e = ok e.last_committed.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.impl.last_committed_eq`

/-- `with_sequence_number`. -/
recall binlog.events.gtid_event.GtidEvent.with_sequence_number_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_sequence_number e x = ok { e with sequence_number := (x, ()) }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.with_sequence_number_eq`

/-- `sequence_number`. -/
recall binlog.events.gtid_event.GtidEvent.impl.sequence_number_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.sequence_number e = ok e.sequence_number.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.impl.sequence_number_eq`

/-- `with_immediate_commit_timestamp` (stored as given; 56 bits are written). -/
recall binlog.events.gtid_event.GtidEvent.with_immediate_commit_timestamp_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_immediate_commit_timestamp e x = ok { e with immediate_commit_timestamp := (x, ()) }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.with_immediate_commit_timestamp_eq`

/-- `immediate_commit_timestamp`. -/
recall binlog.events.gtid_event.GtidEvent.impl.immediate_commit_timestamp_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.immediate_commit_timestamp e = ok e.immediate_commit_timestamp.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.impl.immediate_commit_timestamp_eq`

/-- `with_original_commit_timestamp`. -/
recall binlog.events.gtid_event.GtidEvent.with_original_commit_timestamp_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_original_commit_timestamp e x = ok { e with original_commit_timestamp := (x, ()) }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.with_original_commit_timestamp_eq`

/-- `original_commit_timestamp`. -/
recall binlog.events.gtid_event.GtidEvent.impl.original_commit_timestamp_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.original_commit_timestamp e = ok e.original_commit_timestamp.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.impl.original_commit_timestamp_eq`

/-- `with_tx_length`. -/
recall binlog.events.gtid_event.GtidEvent.with_tx_length_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_tx_length e x = ok { e with tx_length := (x, ()) }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.with_tx_length_eq`

/-- `tx_length`. -/
recall binlog.events.gtid_event.GtidEvent.impl.tx_length_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.tx_length e = ok e.tx_length.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.impl.tx_length_eq`

/-- `with_original_server_version`. -/
recall binlog.events.gtid_event.GtidEvent.with_original_server_version_eq (e : binlog.events.gtid_event.GtidEvent) (x : U32) :
    binlog.events.gtid_event.GtidEvent.with_original_server_version e x = ok { e with original_server_version := (x, ()) }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.with_original_server_version_eq`

/-- `original_server_version`. -/
recall binlog.events.gtid_event.GtidEvent.impl.original_server_version_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.original_server_version e = ok e.original_server_version.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.impl.original_server_version_eq`

/-- `with_immediate_server_version`. -/
recall binlog.events.gtid_event.GtidEvent.with_immediate_server_version_eq (e : binlog.events.gtid_event.GtidEvent) (x : U32) :
    binlog.events.gtid_event.GtidEvent.with_immediate_server_version e x = ok { e with immediate_server_version := (x, ()) }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.with_immediate_server_version_eq`

/-- `immediate_server_version`. -/
recall binlog.events.gtid_event.GtidEvent.impl.immediate_server_version_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.immediate_server_version e = ok e.immediate_server_version.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.impl.immediate_server_version_eq`

/-- `commit_group_ticket`. -/
recall binlog.events.gtid_event.GtidEvent.impl.commit_group_ticket_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.commit_group_ticket e = ok e.commit_group_ticket

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.impl.commit_group_ticket_eq`

/-- `with_commit_group_ticket`. -/
recall binlog.events.gtid_event.GtidEvent.with_commit_group_ticket_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_commit_group_ticket e x = ok { e with commit_group_ticket := x }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.with_commit_group_ticket_eq`

/-- `MyDeserialize::SIZE` is `None`. -/
recall binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq`

/-- `MyDeserialize` for `GTID_EVENT` (33) and `ANONYMOUS_GTID_EVENT` (34): total; `gtidRead`; untagged, serialization version 0, no commit group ticket. -/
recall binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_untagged (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val = 33 ∨ ctx.event_type_raw.val = 34) (buf : io.ParseBuf) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs gtidView (gtidRead buf.val) r rest ∧
      ∀ e, okPart r = some e → e.tag = none ∧ e.serialization_version.val = 0 ∧ e.commit_group_ticket.val = 0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_untagged`

/-- `MyDeserialize` for `GTID_TAGGED_LOG_EVENT` (42): the (opaque) tagged reader. -/
recall binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_tagged (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val = 42) (buf : io.ParseBuf) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf = binlog.events.gtid_event.GtidEvent.deserialize_tagged buf

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_tagged`

/-- `MyDeserialize` with any other event type in the context: an error. -/
recall binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_other (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val ∉ [33, 34, 42]) (buf : io.ParseBuf) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r _ => okPart r = none ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_other`

/-- `MySerialize` of an untagged event: appends `gtidEnc`. -/
recall binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag = none) (buf : alloc.vec.Vec U8)
    (h : buf.length + (gtidEnc e).length ≤ Usize.max) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ gtidEnc e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- `MySerialize` of a tagged event: the (opaque) tagged writer. -/
recall binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize_tagged (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag.isSome) (buf : alloc.vec.Vec U8) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf = binlog.events.gtid_event.GtidEvent.serialize_tagged e buf

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize_tagged`

/-- Round trip (untagged, with the logical-clock part): the event reads back, for timestamps below `2^55` (immediate) and `2^56` (original) and an immediate server version below `2^31`; bytes after it are left. -/
recall binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag = none) (hlc : e.lc_typecode.isSome)
    (hi : e.immediate_commit_timestamp.1.val < 2 ^ 55) (ho : e.original_commit_timestamp.1.val < 2 ^ 56)
    (hs : e.immediate_server_version.1.val < 2 ^ 31)
    (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val = 33 ∨ ctx.event_type_raw.val = 34)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = gtidEnc e ++ tail) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map gtidView = some (gtidView e) ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip`

/-- `BinlogStruct::len` of an untagged event: `gtidLenCrate`, which always counts the logical-clock part. **Quirk:** without it (`lc_typecode` `None`) `serialize` writes 25 bytes but `len` is at least 42 (`Defs.gtidLenCrate_ne`); with it, `len` is the length of `gtidEnc` (`Defs.gtidLenCrate_eq`). -/
recall binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag = none) (v : binlog.consts.BinlogVersion) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = gtidLenCrate e ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec`

/-- `BinlogStruct::len` of a tagged event: the (opaque) tagged length. -/
recall binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_tagged (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag.isSome) (v : binlog.consts.BinlogVersion) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = binlog.events.gtid_event.GtidEvent.len_tagged e

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_tagged`

/-- `BinlogEvent::EVENT_TYPE`: `GTID_EVENT` (33). -/
recall binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .GTID_EVENT

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq`

end mysql_common
