import Defs
import Proofs.Util.BinlogEvGtid

/-! Statements for `struct AnonymousGtidEvent and its impls` (spec file: `Specs/Binlog/Events/AnonymousGtidEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

/-- `SIZE`: `GtidEvent::SIZE`, `None`. -/
theorem binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  sorry

/-- `MyDeserialize`: `GtidEvent::deserialize` (with the same context, so the event type in `ctx` selects the format). -/
theorem binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_eq (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf = binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf := by
  sorry

/-- `MySerialize`: `GtidEvent::serialize`. -/
theorem binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMySerialize.serialize_eq (e : binlog.events.anonymous_gtid_event.AnonymousGtidEvent) (buf : alloc.vec.Vec U8) :
    binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf = binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf := by
  unfold binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMySerialize.serialize; rfl

/-- `BinlogStruct::len`: `GtidEvent::len`. -/
theorem binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq (e : binlog.events.anonymous_gtid_event.AnonymousGtidEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v := by
  unfold binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len; rfl

/-- `BinlogEvent::EVENT_TYPE`: `ANONYMOUS_GTID_EVENT` (34). -/
theorem binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .ANONYMOUS_GTID_EVENT := by
  unfold binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

end mysql_common
