import Proofs.Binlog.Events.PreviousGtidsEvent.PreviousGtidsSid
import Proofs.Binlog.Events.PreviousGtidsEvent.PreviousGtidsEvent

/-!
# `src/binlog/events/previous_gtids_event.rs`
    `PreviousGtidsEvent` (`PREVIOUS_GTIDS_LOG_EVENT`, code 35) and `PreviousGtidsSid`. Covered:
    `PreviousGtidsSid::{new, uuid, tag, intervals, into_owned}`, `PreviousGtidsEvent::{new, sids,
    into_owned}`, `SIZE`, `deserialize` (exact on any input in the untagged format),
    `serialize`, the round trip and `len` (events without tags), `EVENT_TYPE`.

    **Configuration.** As in `Specs/Io.lean` (feature `binlog_core`; patches 140–155, in
    particular 148: the loops as recursions (stack proportional to the numbers of SIDs and
    intervals), tags through `binlog::trusted`).

    **Caveats.** Allocation is infallible, overflow is a panic (debug semantics), the stack is not
    modelled.

    **Caveat: real Rust aborts where the model returns `Err`.** Inputs: the untagged format with an
    SID count `n` (low 56 bits of the first 8 bytes) such that `n * size_of::<PreviousGtidsSid>()`
    exceeds `isize::MAX` (capacity-overflow panic) or the memory available (abort, e.g.
    "memory allocation of 70368744177600 bytes failed"), and any SID entry whose interval count
    `m` (bytes 16–23 of the entry) makes `16 * m` too large likewise; in each case with fewer
    bytes than the count announces. The statements describe the model (an error).
    **Unbounded allocation (upstream):** `deserialize` calls `Vec::with_capacity` with
    the SID count (up to `2^56`) and each SID's interval count (up to `2^64 - 1`) read from the
    wire, before checking that the data holds them. In real Rust a large count panics (capacity
    overflow) or aborts the process (allocation failure), from a 24-byte input; the model
    (infallible allocation) returns an error instead, and the statements describe the model.
    (As for `ComBinlogDumpGtid`.)

    **Definitions used.** `Defs/BinlogEvents.lean` (`gnoIntervalEnc`, `pgSidEnc`, `pgEnc`,
    `PgSidView`, `pgSidView`, `pgIntervalsRead`, `pgSidsRead`, `pgRead`, `evLenCap`, `ReadsAs`).

    **Trusted axioms.** None of namespace `Trusted`. Opaque (nothing assumed): `io::Error`, and
    `binlog::trusted::{previous_gtids_tag, tag_as_bytes, tag_into_owned}` (tags): the statements
    avoid them by covering the untagged format and events without tags.

    **Not covered.** The tagged format (MySQL 8.4: format byte `1`, a tag per SID) beyond what the
    untagged statements say, since tags go through the opaque `binlog::trusted`; the private
    helpers (through `deserialize` / `serialize`); the derived impls.

    **Behaviour to note.** The reader does not check the intervals (`start < end`, non-zero), and
    leaves bytes after the last SID unread (an error in `Event::read_event`). `len` serializes the
    event to measure it.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct PreviousGtidsSid and its impls` -/

/-- `new(uuid, tag, intervals)`. -/
recall binlog.events.previous_gtids_event.PreviousGtidsSid.new_eq (u : Array U8 16#usize) (t : Option packets.Tag) (is : alloc.vec.Vec packets.GnoInterval) :
    binlog.events.previous_gtids_event.PreviousGtidsSid.new u t is = ok { uuid := u, tag := t, intervals := is }

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsSid.new_eq
/-- `uuid`. -/
recall binlog.events.previous_gtids_event.PreviousGtidsSid.impl.uuid_eq (s : binlog.events.previous_gtids_event.PreviousGtidsSid) :
    binlog.events.previous_gtids_event.PreviousGtidsSid.impl.uuid s = ok s.uuid

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsSid.impl.uuid_eq
/-- `tag`. -/
recall binlog.events.previous_gtids_event.PreviousGtidsSid.impl.tag_eq (s : binlog.events.previous_gtids_event.PreviousGtidsSid) :
    binlog.events.previous_gtids_event.PreviousGtidsSid.impl.tag s = ok s.tag

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsSid.impl.tag_eq
/-- `intervals`. -/
recall binlog.events.previous_gtids_event.PreviousGtidsSid.impl.intervals_spec (x : binlog.events.previous_gtids_event.PreviousGtidsSid) :
    binlog.events.previous_gtids_event.PreviousGtidsSid.impl.intervals x ⦃ s => s.val = x.intervals.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsSid.impl.intervals_spec
/-- `into_owned` of an untagged SID: the same UUID and intervals. -/
recall binlog.events.previous_gtids_event.PreviousGtidsSid.into_owned_spec (s : binlog.events.previous_gtids_event.PreviousGtidsSid) (ht : s.tag = none) :
    binlog.events.previous_gtids_event.PreviousGtidsSid.into_owned s ⦃ s' => pgSidView s' = pgSidView s ∧ s'.tag = none ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.tagIntoOwned] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsSid.into_owned_spec
/-! ### `struct PreviousGtidsEvent and its impls` -/

/-- `new(sids)`. -/
recall binlog.events.previous_gtids_event.PreviousGtidsEvent.new_eq (ss : alloc.vec.Vec binlog.events.previous_gtids_event.PreviousGtidsSid) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.new ss = ok { sids := ss }

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsEvent.new_eq
/-- `sids`. -/
recall binlog.events.previous_gtids_event.PreviousGtidsEvent.impl.sids_spec (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.impl.sids e ⦃ s => s.val = e.sids.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsEvent.impl.sids_spec
/-- `into_owned` of an event without tags: the same SIDs. -/
recall binlog.events.previous_gtids_event.PreviousGtidsEvent.into_owned_spec (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hn : ∀ s ∈ e.sids.val, s.tag = none) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.into_owned e ⦃ e' => e'.sids.val.map pgSidView = e.sids.val.map pgSidView ∧ ∀ s ∈ e'.sids.val, s.tag = none ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.tagIntoOwned] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsEvent.into_owned_spec
/-- `MyDeserialize::SIZE` is `None`. -/
recall binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq
/-- `MyDeserialize` in the untagged format (byte 7 of the count is 0): total; `pgRead`; no SID has a tag. -/
recall binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (hu : ∀ b, buf.val[7]? = some b → b.val = 0) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) => e.sids.val.map pgSidView) (pgRead buf.val) r rest ∧
      ∀ e, okPart r = some e → ∀ s ∈ e.sids.val, s.tag = none ⦄

/-- [propext, Classical.choice, Quot.sound, binlog.trusted.previous_gtids_tag, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec
/-- `MyDeserialize` on fewer than 8 bytes: an error. -/
recall binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_short (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.length < 8) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r _ => okPart r = none ⦄

/-- [propext, Classical.choice, Quot.sound, binlog.trusted.previous_gtids_tag, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_short
/-- `MySerialize` of an event without tags: the untagged format (`pgEnc`). -/
recall binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hn : ∀ s ∈ e.sids.val, s.tag = none) (buf : alloc.vec.Vec U8) (h : buf.length + (pgEnc e).length ≤ Usize.max) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ pgEnc e ⦄

/-- [propext, Classical.choice, Quot.sound, binlog.trusted.tag_as_bytes, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-- Round trip, for an event without tags and fewer than `2^56` SIDs. -/
recall binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hn : ∀ s ∈ e.sids.val, s.tag = none) (hl : e.sids.length < 2 ^ 56) (ctx : binlog.BinlogCtx) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = pgEnc e ++ tail) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.previous_gtids_event.PreviousGtidsEvent) => x.sids.val.map pgSidView) = some (e.sids.val.map pgSidView) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, binlog.trusted.previous_gtids_tag, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip
/-- `BinlogStruct::len` of an event without tags: the length of `pgEnc`, capped. -/
recall binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hn : ∀ s ∈ e.sids.val, s.tag = none) (v : binlog.consts.BinlogVersion) (h : (pgEnc e).length ≤ Usize.max) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (pgEnc e).length evLenCap ⦄

/-- [propext, Classical.choice, Quot.sound, binlog.trusted.tag_as_bytes, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec
/-- `BinlogEvent::EVENT_TYPE`: `PREVIOUS_GTIDS_EVENT` (35). -/
recall binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .PREVIOUS_GTIDS_EVENT

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq
end mysql_common
