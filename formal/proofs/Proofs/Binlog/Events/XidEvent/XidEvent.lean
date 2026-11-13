import Defs
import Proofs.Util.BinlogEvGtid

/-! Statements for `struct XidEvent and its impls` (spec file: `Specs/Binlog/Events/XidEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MyDeserialize`: total; skips the post-header (length from `ctx.fde`), reads the XID (`xidRead`). -/
theorem binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (x : binlog.events.xid_event.XidEvent) => x.xid.val) (xidRead (postHeaderLen (fdeLens ctx.fde) .XID_EVENT) buf.val) r rest ⦄ := by
  unfold binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  step*
  all_goals
    have hi : i.val = postHeaderLen (fdeLens ctx.fde) .XID_EVENT := by
      unfold binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE at post_header_len_post
      rw [i_post, BinlogEvGtid.cast_u8_usize, post_header_len_post]
    simp only [ReadsAs, xidRead]
    split_ifs at * <;> simp_all [okPart, Slice.length]
    all_goals omega

/-- `MySerialize`: appends the XID (8). -/
theorem binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.xid_event.XidEvent) (buf : alloc.vec.Vec U8) (h : buf.length + 8 ≤ Usize.max) :
    binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ leBytes 8 e.xid.val ⦄ := by
  unfold binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMySerialize.serialize
  step*

/-- Round trip, with a 0-byte post-header. -/
theorem binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.xid_event.XidEvent) (ctx : binlog.BinlogCtx) (hp : postHeaderLen (fdeLens ctx.fde) .XID_EVENT = 0) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 8 e.xid.val ++ tail) :
    binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => okPart r = some e ∧ rest.val = tail ⦄ := by
  apply WP.spec_mono (deserialize_spec ctx buf)
  rintro ⟨r, rest⟩ hr
  have hs : xidRead (postHeaderLen (fdeLens ctx.fde) .XID_EVENT) buf.val = some (e.xid.val, tail) := by
    simp [xidRead, hp, h, PBUtil.length_leBytes,
      BinlogEvGtid.leNat_leBytes_u64]
  rw [hs] at hr
  obtain ⟨hm, hrest⟩ := hr
  obtain ⟨x, rfl, hx⟩ := BinlogEvGtid.okPart_map_eq_some hm
  refine ⟨?_, hrest⟩
  cases e; cases x
  simp only [okPart, Option.some.injEq]
  congr 1
  exact UScalar.eq_of_val_eq hx

/-- `BinlogEvent::EVENT_TYPE`: `XID_EVENT` (16). -/
theorem binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .XID_EVENT := by
  unfold binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

/-- `BinlogStruct::len`: 8. -/
theorem binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_eq (e : binlog.events.xid_event.XidEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = ok 8#usize := by
  rfl

end mysql_common
