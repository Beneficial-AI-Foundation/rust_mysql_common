import Defs
import Proofs.Util.BinlogEvGtid

/-! Statements for `struct RotateEvent and its impls` (spec file: `Specs/Binlog/Events/RotateEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

/-- `new(position, name)`: those fields (`name` converted with `into`). -/
theorem binlog.events.rotate_event.RotateEvent.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (position : U64) (nm : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into nm = ok c) :
    binlog.events.rotate_event.RotateEvent.new into position nm ⦃ e => rotateView e = (position.val, cowList c) ⦄ := by
  unfold binlog.events.rotate_event.RotateEvent.new
  step*
  simp_all [rotateView]

/-- `with_position`: replaces the position. -/
theorem binlog.events.rotate_event.RotateEvent.with_position_spec (e : binlog.events.rotate_event.RotateEvent) (position : U64) :
    binlog.events.rotate_event.RotateEvent.with_position e position ⦃ e' => rotateView e' = (position.val, cowList e.«name».1) ⦄ := by
  unfold binlog.events.rotate_event.RotateEvent.with_position
  step*
  simp_all [rotateView]

/-- `with_name`: replaces the name. -/
theorem binlog.events.rotate_event.RotateEvent.with_name_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (e : binlog.events.rotate_event.RotateEvent) (nm : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into nm = ok c) :
    binlog.events.rotate_event.RotateEvent.with_name into e nm ⦃ e' => rotateView e' = (e.position.1.val, cowList c) ⦄ := by
  unfold binlog.events.rotate_event.RotateEvent.with_name
  step*
  simp_all [rotateView]

/-- `position`: the position. -/
theorem binlog.events.rotate_event.RotateEvent.impl.position_eq (e : binlog.events.rotate_event.RotateEvent) :
    binlog.events.rotate_event.RotateEvent.impl.position e = ok e.position.1 := by
  rfl

/-- `name_raw`: the name bytes. -/
theorem binlog.events.rotate_event.RotateEvent.name_raw_spec (e : binlog.events.rotate_event.RotateEvent) :
    binlog.events.rotate_event.RotateEvent.name_raw e ⦃ s => s.val = cowList e.«name».1 ⦄ := by
  unfold binlog.events.rotate_event.RotateEvent.name_raw
  step*

/-- `is_fake`: whether the position is 0 (a fake rotate event, sent at the start of a dump). -/
theorem binlog.events.rotate_event.RotateEvent.is_fake_eq (e : binlog.events.rotate_event.RotateEvent) :
    binlog.events.rotate_event.RotateEvent.is_fake e = ok (decide (e.position.1.val = 0)) := by
  unfold binlog.events.rotate_event.RotateEvent.is_fake
  obtain ⟨⟨i, u⟩, n⟩ := e
  simp only [binlog.events.rotate_event.RotateEvent.impl.position]
  have : (i = 0#u64) ↔ i.val = 0 := ⟨fun h => by subst h; rfl, fun h => UScalar.eq_of_val_eq h⟩
  simp [this]

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.rotate_event.RotateEvent.into_owned_spec (e : binlog.events.rotate_event.RotateEvent) :
    binlog.events.rotate_event.RotateEvent.into_owned e ⦃ e' => rotateView e' = rotateView e ⦄ := by
  unfold binlog.events.rotate_event.RotateEvent.into_owned
  step*
  simp_all [rotateView]

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MyDeserialize`: total; `rotateRead` (8 bytes of position, the name as the rest). -/
theorem binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs rotateView (rotateRead buf.val) r rest ⦄ := by
  unfold binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  step*
  all_goals
    split_ifs at r_post with hl
    all_goals
      obtain ⟨_, rfl, _⟩ := r_post
      simp_all [ReadsAs, rotateRead, okPart, rotateView]
    all_goals rw [ite_eq_right (by omega)]; trivial

/-- `MySerialize`: appends the layout `rotateEnc`. -/
theorem binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.rotate_event.RotateEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (rotateEnc e).length ≤ Usize.max) :
    binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ rotateEnc e ⦄ := by
  unfold binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [rotateEnc, List.length_append, length_leBytes] at h
  step*
  · have : buf1.length = buf.length + 8 := by simp [alloc.vec.Vec.length, buf1_post, length_leBytes]
    omega
  · simp_all [rotateEnc]

/-- Round trip: the data `serialize` writes reads back as the same event. -/
theorem binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.rotate_event.RotateEvent) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = rotateEnc e) :
    binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map rotateView = some (rotateView e) ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec ctx buf)
  rintro ⟨r, rest⟩ hr
  have hs : rotateRead buf.val = some (rotateView e, []) := by
    simp [rotateRead, h, rotateEnc, length_leBytes, rotateView, BinlogEvGtid.leNat_leBytes_u64]
  rw [hs] at hr
  exact hr

/-- `BinlogEvent::EVENT_TYPE`: `ROTATE_EVENT` (4). -/
theorem binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .ROTATE_EVENT := by
  unfold binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

/-- `BinlogStruct::len`: the length of what `serialize` writes (`rotateEnc`), capped at `u32::MAX - 19`. -/
theorem binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.rotate_event.RotateEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (rotateEnc e).length evLenCap ⦄ := by
  unfold binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  obtain ⟨p, c, u⟩ := e
  simp only
  step*
  · rw [i1_post]; simp [BinlogEvGtid.header_len_val]
  · have := BinlogEvGtid.u32_max_le_usize
    have hs : s.len.val = (cowList c).length := by simp [s_post]
    have hh := BinlogEvGtid.header_len_val
    simp only [n_post, len1_post, i2_post, i1_post, len_post, hh, hs,
      rotateEnc, List.length_append, length_leBytes, evLenCap]
    omega

end mysql_common
