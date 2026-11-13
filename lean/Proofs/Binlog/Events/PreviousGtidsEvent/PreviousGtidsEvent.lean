import Defs
import Proofs.Util.BinlogEvGtid

/-! Statements for `struct PreviousGtidsEvent and its impls` (spec file: `Specs/Binlog/Events/PreviousGtidsEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

/-- `new(sids)`. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.new_eq (ss : alloc.vec.Vec binlog.events.previous_gtids_event.PreviousGtidsSid) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.new ss = ok { sids := ss } := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsEvent.new; rfl

/-- `sids`. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.impl.sids_spec (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.impl.sids e ⦃ s => s.val = e.sids.val ⦄ := by
  sorry

/-- `into_owned` of an event without tags: the same SIDs. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.into_owned_spec (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hn : ∀ s ∈ e.sids.val, s.tag = none) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.into_owned e ⦃ e' => e'.sids.val.map pgSidView = e.sids.val.map pgSidView ∧ ∀ s ∈ e'.sids.val, s.tag = none ⦄ := by
  sorry

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MyDeserialize` in the untagged format (byte 7 of the count is 0): total; `pgRead`; no SID has a tag. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (hu : ∀ b, buf.val[7]? = some b → b.val = 0) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) => e.sids.val.map pgSidView) (pgRead buf.val) r rest ∧
      ∀ e, okPart r = some e → ∀ s ∈ e.sids.val, s.tag = none ⦄ := by
  sorry

/-- `MyDeserialize` on fewer than 8 bytes: an error. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_short (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.length < 8) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r _ => okPart r = none ⦄ := by
  sorry

/-- `MySerialize` of an event without tags: the untagged format (`pgEnc`). -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hn : ∀ s ∈ e.sids.val, s.tag = none) (buf : alloc.vec.Vec U8) (h : buf.length + (pgEnc e).length ≤ Usize.max) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ pgEnc e ⦄ := by
  sorry

/-- Round trip, for an event without tags and fewer than `2^56` SIDs. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hn : ∀ s ∈ e.sids.val, s.tag = none) (hl : e.sids.length < 2 ^ 56) (ctx : binlog.BinlogCtx) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = pgEnc e ++ tail) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.previous_gtids_event.PreviousGtidsEvent) => x.sids.val.map pgSidView) = some (e.sids.val.map pgSidView) ∧ rest.val = tail ⦄ := by
  sorry

/-- `BinlogStruct::len` of an event without tags: the length of `pgEnc`, capped. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.previous_gtids_event.PreviousGtidsEvent) (hn : ∀ s ∈ e.sids.val, s.tag = none) (v : binlog.consts.BinlogVersion) (h : (pgEnc e).length ≤ Usize.max) :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (pgEnc e).length evLenCap ⦄ := by
  sorry

/-- `BinlogEvent::EVENT_TYPE`: `PREVIOUS_GTIDS_EVENT` (35). -/
theorem binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .PREVIOUS_GTIDS_EVENT := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

end mysql_common
