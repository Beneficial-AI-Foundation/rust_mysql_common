import Proofs.Binlog.Events.XidEvent.XidEvent

/-!
# `src/binlog/events/xid_event.rs`
    `XidEvent` (`XID_EVENT`, code 16): after the post-header (its length from the FDE, normally 0),
    the XID (8). Covered: `SIZE`, `deserialize` (exact on any input), `serialize`, the round trip,
    `EVENT_TYPE`, `len`.

    **Configuration.** As in `Specs/Io.lean` (target `x86_64-unknown-linux-gnu`, feature
    `binlog_core`; patches 140–155). **Caveats.** Allocation is infallible, overflow is a panic
    (debug semantics), the stack is not modelled. A reader's statement says what it returns; when it
    fails, what it leaves of the buffer is not stated (`ReadsAs`; `Event::read_event` discards it).

    **Definitions used.** `Defs/BinlogEvents.lean` (`xidRead`, `postHeaderLen`, `fdeLens`,
    `ReadsAs`). **Trusted axioms:** none beyond `io::Error`'s.

    **Not covered.** The derived `Debug`/`Clone`/`PartialEq`/`Hash`.

    **Behaviour to note.** `serialize` writes no post-header, so the round trip needs an FDE with a
    0-byte XID post-header (the default).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct XidEvent and its impls` -/

/-- `MyDeserialize::SIZE` is `None`. -/
recall binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq
/-- `MyDeserialize`: total; skips the post-header (length from `ctx.fde`), reads the XID (`xidRead`). -/
recall binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (x : binlog.events.xid_event.XidEvent) => x.xid.val) (xidRead (postHeaderLen (fdeLens ctx.fde) .XID_EVENT) buf.val) r rest ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec
/-- `MySerialize`: appends the XID (8). -/
recall binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.xid_event.XidEvent) (buf : alloc.vec.Vec U8) (h : buf.length + 8 ≤ Usize.max) :
    binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ leBytes 8 e.xid.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-- Round trip, with a 0-byte post-header. -/
recall binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.xid_event.XidEvent) (ctx : binlog.BinlogCtx) (hp : postHeaderLen (fdeLens ctx.fde) .XID_EVENT = 0) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 8 e.xid.val ++ tail) :
    binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => okPart r = some e ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip
/-- `BinlogEvent::EVENT_TYPE`: `XID_EVENT` (16). -/
recall binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .XID_EVENT

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq
/-- `BinlogStruct::len`: 8. -/
recall binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq (e : binlog.events.xid_event.XidEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = ok 8#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq
end mysql_common
