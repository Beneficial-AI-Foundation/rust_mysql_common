import Proofs.Binlog.Events.FormatDescriptionEvent.FormatDescriptionEvent

/-!
# `src/binlog/events/format_description_event.rs`
    `FormatDescriptionEvent` (`FORMAT_DESCRIPTION_EVENT`, code 15): `binlog_version` (2),
    `server_version` (50, `0`-padded), `create_timestamp` (4), `header_length` (1, always 19), the
    post-header lengths per event type (the rest; the footer is stripped by `Event::read`).
    Covered: `SERVER_VER_LEN`, `new`, the `with_*` builders, every accessor,
    `get_event_type_header_length` (exact: the array entry or the default), `into_owned`, `SIZE`,
    `deserialize` (exact on any input), `serialize`, the round trip (up to padding of the server
    version), `len`, `EVENT_TYPE`.

    **Configuration.** As in `Specs/Io.lean` (feature `binlog_core`; patches 140–155).
    **Caveats.** Allocation is infallible, overflow is a panic (debug semantics), the stack is not
    modelled. When a reader fails, what it leaves of the buffer is not stated (`ReadsAs`).

    **Definitions used.** `Defs/BinlogEvents.lean` (`FdeView`, `fdeView`, `fdeEnc`, `fdeRead`,
    `fdeLens`, `fixedText`, `binlogVersionCode`, `binlogVersionOfCode`, `postHeaderLen`,
    `defaultPostHeaderLen`, `eventTypeCode`, `footerAlg`, `evLenCap`, `ReadsAs`).
    **Trusted axioms:** none beyond `io::Error`'s.

    **Not covered.** `server_version` (lossy UTF-8) and `split_version` (iterator-based version
    parsing): excluded from the translation; `footer_mut` (crate-private); the derived impls.

    **Behaviour to note.** `deserialize` leaves the footer at its default (algorithm `OFF`);
    `Event::read_data` sets the event's footer. The server version is kept with its padding (all
    50 bytes), so a shorter one written by `serialize` reads back padded. The defaults of
    `get_event_type_header_length` for the pre-5.0 load events are 0 (see `defaultPostHeaderLen`).

    (Of these definitions, `eventTypeCode`, `binlogVersionCode`, `binlogVersionOfCode` are in `Defs/BinlogCore.lean`, shared with the
    other binlog spec files.)
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct FormatDescriptionEvent and its impls` -/

/-- `SERVER_VER_LEN`: 50. -/
recall binlog.events.format_description_event.SERVER_VER_LEN_eq :
    binlog.events.format_description_event.SERVER_VER_LEN = 50#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.SERVER_VER_LEN_eq
/-- `new(version)`: that version, an empty server version and post-header array, timestamp 0, the default footer. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.new_spec (v : binlog.consts.BinlogVersion) :
    binlog.events.format_description_event.FormatDescriptionEvent.new v ⦃ e => fdeView e = { version := v, serverVersion := [], createTimestamp := 0, lens := [] } ∧
      footerAlg e.footer = some 0 ∧ e.footer.checksum_enabled = true ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.new_spec
/-- `with_binlog_version`. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.with_binlog_version_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_binlog_version e v ⦃ e' => fdeView e' = { fdeView e with version := v } ∧ e'.footer = e.footer ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.with_binlog_version_spec
/-- `with_server_version` (stored as given; padded or truncated to 50 bytes only when written). -/
recall binlog.events.format_description_event.FormatDescriptionEvent.with_server_version_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.format_description_event.FormatDescriptionEvent) (sv : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into sv = ok c) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_server_version into e sv ⦃ e' => fdeView e' = { fdeView e with serverVersion := cowList c } ∧ e'.footer = e.footer ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.with_server_version_spec
/-- `with_create_timestamp`. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.with_create_timestamp_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (ts : U32) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_create_timestamp e ts ⦃ e' => fdeView e' = { fdeView e with createTimestamp := ts.val } ∧ e'.footer = e.footer ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.with_create_timestamp_spec
/-- `with_event_type_header_lengths`. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.with_event_type_header_lengths_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.format_description_event.FormatDescriptionEvent) (ls : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into ls = ok c) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_event_type_header_lengths into e ls ⦃ e' => fdeView e' = { fdeView e with lens := cowList c } ∧ e'.footer = e.footer ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.with_event_type_header_lengths_spec
/-- `with_footer`. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.with_footer_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) (f : binlog.events.BinlogEventFooter) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_footer e f = ok { e with footer := f }

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.with_footer_eq
/-- `binlog_version`. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.impl.binlog_version_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.binlog_version e = ok e.binlog_version.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.impl.binlog_version_eq
/-- `server_version_raw`: the stored server version, its first 50 bytes. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.server_version_raw_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.server_version_raw e ⦃ s => s.val = (cowList e.server_version.1).take 50 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.server_version_raw_spec
/-- `create_timestamp`. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.impl.create_timestamp_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.create_timestamp e = ok e.create_timestamp.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.impl.create_timestamp_eq
/-- `event_header_length`: always 19. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.impl.event_header_length_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.event_header_length e = ok 19#u8

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.impl.event_header_length_eq
/-- `event_type_header_lengths`: the post-header lengths array. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.impl.event_type_header_lengths_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.event_type_header_lengths e ⦃ s => s.val = fdeLens e ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.impl.event_type_header_lengths_spec
/-- `footer`. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.impl.footer_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.footer e = ok e.footer

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.impl.footer_eq
/-- `get_event_type_header_length(t)`: `postHeaderLen` (0 for `UNKNOWN_EVENT`; else the array entry `t - 1`, or the default if the array is shorter). -/
recall binlog.events.format_description_event.FormatDescriptionEvent.get_event_type_header_length_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (t : binlog.consts.EventType) :
    binlog.events.format_description_event.FormatDescriptionEvent.get_event_type_header_length e t ⦃ n => n.val = postHeaderLen (fdeLens e) t ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.get_event_type_header_length_spec
/-- `into_owned`: the same fields and footer. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.into_owned_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.into_owned e ⦃ e' => fdeView e' = fdeView e ∧ e'.footer = e.footer ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.into_owned_spec
/-- `MyDeserialize::SIZE` is `None`. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq
/-- `MyDeserialize`: total; `fdeRead` (a known version, header length 19, the rest as the post-header lengths); the footer is the default. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs fdeView (fdeRead buf.val) r rest ∧
      ∀ e, okPart r = some e → footerAlg e.footer = some 0 ∧ e.footer.checksum_enabled = true ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofError, core.io.error.Error.ofMsg, binlog.consts.UnknownBinlogVersion.Insts.CoreFmtDebug.fmt, binlog.consts.UnknownBinlogVersion.Insts.CoreFmtDisplay.fmt, binlog.events.format_description_event.InvalidEventHeaderLength.Insts.CoreFmtDebug.fmt, binlog.events.format_description_event.InvalidEventHeaderLength.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec
/-- `MySerialize`: appends the layout `fdeEnc`. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (fdeEnc e).length ≤ Usize.max) :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ fdeEnc e ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-- Round trip: the fields come back, the server version padded (or truncated) to 50 bytes. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.format_description_event.FormatDescriptionEvent) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = fdeEnc e) :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map fdeView = some { fdeView e with serverVersion := fixedText 50 (cowList e.server_version.1) } ∧ rest.val = [] ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofError, core.io.error.Error.ofMsg, binlog.consts.UnknownBinlogVersion.Insts.CoreFmtDebug.fmt, binlog.consts.UnknownBinlogVersion.Insts.CoreFmtDisplay.fmt, binlog.events.format_description_event.InvalidEventHeaderLength.Insts.CoreFmtDebug.fmt, binlog.events.format_description_event.InvalidEventHeaderLength.Insts.CoreFmtDisplay.fmt] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip
/-- `BinlogStruct::len`: the length of what `serialize` writes (`fdeEnc`), capped at `u32::MAX - 19`. -/
recall binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (fdeEnc e).length evLenCap ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec
/-- `BinlogEvent::EVENT_TYPE`: `FORMAT_DESCRIPTION_EVENT` (15). -/
recall binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .FORMAT_DESCRIPTION_EVENT

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq
end mysql_common
