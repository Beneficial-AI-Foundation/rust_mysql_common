import Proofs.Binlog.Events.AnonymousGtidEvent.AnonymousGtidEvent

/-!
# `src/binlog/events/anonymous_gtid_event.rs`
    `AnonymousGtidEvent` (`ANONYMOUS_GTID_LOG_EVENT`, code 34): a `GtidEvent` (same layout).
    Covered: `SIZE`, `deserialize`, `serialize`, `len` (each the `GtidEvent` one, see
    `Specs/Binlog/Events/GtidEvent.lean`), `EVENT_TYPE`.

    **Configuration.** As in `Specs/Io.lean` (target `x86_64-unknown-linux-gnu`, feature
    `binlog_core`; patches 140–155). **Caveats.** Allocation is infallible, overflow is a panic
    (debug semantics), the stack is not modelled. A reader's statement says what it returns; when it
    fails, what it leaves of the buffer is not stated (`ReadsAs`; `Event::read_event` discards it).

    **Definitions used.** None beyond the `GtidEvent` statements. **Trusted axioms:** none
    beyond `io::Error`'s (and, through `GtidEvent` for the tagged format, the opaque
    `GtidEvent::{deserialize,serialize,len}_tagged`).

    **Not covered.** The derived impls.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct AnonymousGtidEvent and its impls` -/

/-- `SIZE`: `GtidEvent::SIZE`, `None`. -/
recall binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq`

/-- `MyDeserialize`: `GtidEvent::deserialize` (with the same context, so the event type in `ctx` selects the format). -/
recall binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_eq (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf = binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_eq`

/-- `MySerialize`: `GtidEvent::serialize`. -/
recall binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMySerialize.serialize_eq (e : binlog.events.anonymous_gtid_event.AnonymousGtidEvent) (buf : alloc.vec.Vec U8) :
    binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf = binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMySerialize.serialize_eq`

/-- `BinlogStruct::len`: `GtidEvent::len`. -/
recall binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq (e : binlog.events.anonymous_gtid_event.AnonymousGtidEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq`

/-- `BinlogEvent::EVENT_TYPE`: `ANONYMOUS_GTID_EVENT` (34). -/
recall binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .ANONYMOUS_GTID_EVENT

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq`

end mysql_common
