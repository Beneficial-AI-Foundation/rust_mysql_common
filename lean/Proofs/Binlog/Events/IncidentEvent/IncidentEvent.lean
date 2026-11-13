import Defs
import Proofs.Util.BinlogEvGtid

/-! Statements for `struct IncidentEvent and its impls` (spec file: `Specs/Binlog/Events/IncidentEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

/-- `new(type, message)`: those fields. -/
theorem binlog.events.incident_event.IncidentEvent.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (t : binlog.consts.IncidentType) (m : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into m = ok c) :
    binlog.events.incident_event.IncidentEvent.new into t m ⦃ e => (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e = (incidentTypeCode t, cowList c) ⦄ := by
  unfold binlog.events.incident_event.IncidentEvent.new
  cases t <;> step* <;> simp_all [incidentTypeCode, read_discriminant, binlog.consts.IncidentType.read_discriminant]

/-- `incident_type`: the known type with the stored code, or the raw code as an error. -/
theorem binlog.events.incident_event.IncidentEvent.impl.incident_type_spec (e : binlog.events.incident_event.IncidentEvent) :
    binlog.events.incident_event.IncidentEvent.impl.incident_type e ⦃ r => match incidentTypeOfCode e.incident_type.1.val with
      | some t => r = .Ok t
      | none => r = .Err e.incident_type.1 ⦄ := by
  unfold binlog.events.incident_event.IncidentEvent.impl.incident_type
  rw [misc.raw._const.RawConst.get_eq]
  show binlog.consts.IncidentType.Insts.CoreConvertTryFromU16UnknownIncidentType.try_from _ ⦃ _ ⦄
  rw [binlog.consts.IncidentType.Insts.CoreConvertTryFromU16UnknownIncidentType.try_from_spec]
  simp only [WP.spec_ok]
  cases incidentTypeOfCode e.incident_type.1.val <;> rfl

/-- `message_raw`: the message, its first 255 bytes (the effective bytes of a `U8Bytes`). -/
theorem binlog.events.incident_event.IncidentEvent.message_raw_spec (e : binlog.events.incident_event.IncidentEvent) :
    binlog.events.incident_event.IncidentEvent.message_raw e ⦃ s => s.val = (cowList e.message.1).take 255 ⦄ := by
  unfold binlog.events.incident_event.IncidentEvent.message_raw
  obtain ⟨m, hm, hmv⟩ := spec_eq_ok misc.raw.bytes.U8Bytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec
  apply WP.spec_mono (misc.raw.bytes.RawBytes.as_bytes_spec _ m hm e.message)
  intro s hs; rw [hs, hmv]

/-- `with_incident_type`: replaces the type. -/
theorem binlog.events.incident_event.IncidentEvent.with_incident_type_spec (e : binlog.events.incident_event.IncidentEvent) (t : binlog.consts.IncidentType) :
    binlog.events.incident_event.IncidentEvent.with_incident_type e t ⦃ e' => (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e' = (incidentTypeCode t, cowList e.message.1) ⦄ := by
  unfold binlog.events.incident_event.IncidentEvent.with_incident_type
  cases t <;> step* <;> simp_all [incidentTypeCode, read_discriminant, binlog.consts.IncidentType.read_discriminant]

/-- `with_message`: replaces the message. -/
theorem binlog.events.incident_event.IncidentEvent.with_message_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.incident_event.IncidentEvent) (m : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into m = ok c) :
    binlog.events.incident_event.IncidentEvent.with_message into e m ⦃ e' => (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e' = (e.incident_type.1.val, cowList c) ⦄ := by
  unfold binlog.events.incident_event.IncidentEvent.with_message
  step*

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.incident_event.IncidentEvent.into_owned_spec (e : binlog.events.incident_event.IncidentEvent) :
    binlog.events.incident_event.IncidentEvent.into_owned e ⦃ e' => (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e' = (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e ⦄ := by
  unfold binlog.events.incident_event.IncidentEvent.into_owned
  step*

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

/-- `MyDeserialize`: total; `incidentRead` (the raw type, then the length-prefixed message; the rest is left). -/
theorem binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) (incidentRead buf.val) r rest ⦄ := by
  unfold binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  step*
  all_goals
    split_ifs at r_post with hl
    · obtain ⟨_, rfl, hv, hb1⟩ := r_post
      first
        | (rw [hb1] at r1_post
           rw [BinlogEvGtid.incidentRead_eq _ hl _ _ r1_post.symm]
           cases r1 <;> simp_all [ReadsAs, okPart])
        | simp_all
    · obtain ⟨_, rfl⟩ := r_post
      have hl' : ¬ 2 ≤ buf.val.length := hl
      rw [show incidentRead buf.val = none by simp [incidentRead, takeExact, hl']]
      simp_all [ReadsAs, okPart]

/-- `MySerialize`: appends the layout `incidentEnc`. -/
theorem binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.incident_event.IncidentEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (incidentEnc e).length ≤ Usize.max) :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ incidentEnc e ⦄ := by
  unfold binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [incidentEnc, u8Str, List.length_append, List.length_cons, List.length_take, length_leBytes] at h
  step*
  · have : buf1.length = buf.length + 2 := by simp [alloc.vec.Vec.length, buf1_post, length_leBytes]
    omega
  · simp_all [incidentEnc, u8Str]

/-- Round trip, for a message of at most 255 bytes. -/
theorem binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.incident_event.IncidentEvent) (hm : (cowList e.message.1).length ≤ 255) (ctx : binlog.BinlogCtx) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = incidentEnc e ++ tail) :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map (fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) = some ((fun (x : binlog.events.incident_event.IncidentEvent) => (x.incident_type.1.val, cowList x.message.1)) e) ∧ rest.val = tail ⦄ := by
  apply WP.spec_mono (Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec ctx buf)
  rintro ⟨r, rest⟩ hr
  have h2 : 2 ≤ buf.val.length := by simp [h, incidentEnc, length_leBytes]
  have hc : checkedLenPrefixed 1 (buf.val.drop 2) = (some (cowList e.message.1), tail) := by
    rw [h, incidentEnc, List.append_assoc, BinlogEvGtid.drop_leBytes_append]
    exact BinlogEvGtid.checkedLenPrefixed_u8Str _ _ hm
  rw [BinlogEvGtid.incidentRead_eq _ h2 _ _ hc] at hr
  have ht : leNat (buf.val.take 2) = e.incident_type.1.val := by
    rw [h, incidentEnc, List.append_assoc, BinlogEvGtid.take_leBytes_append, BinlogEvGtid.leNat_leBytes_u16]
  rw [ht] at hr
  exact hr

/-- `BinlogEvent::EVENT_TYPE`: `INCIDENT_EVENT` (26). -/
theorem binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .INCIDENT_EVENT := by
  unfold binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

/-- `BinlogStruct::len`: the length of what `serialize` writes (`incidentEnc`), capped at `u32::MAX - 19`. -/
theorem binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.incident_event.IncidentEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (incidentEnc e).length evLenCap ⦄ := by
  unfold binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  obtain ⟨p, c, u⟩ := e
  simp only
  step*
  · rw [i3_post]; simp [BinlogEvGtid.header_len_val]
  · have := BinlogEvGtid.u32_max_le_usize
    have hs : s.len.val = (cowList c).length := by simp [s_post]
    have hi1 : i1.val = 255 := by rw [i1_post, BinlogEvGtid.cast_u8_usize]; simp [core.num.U8.MAX, U8.rMax]
    have hh := BinlogEvGtid.header_len_val
    simp only [n_post, len2_post, len1_post, i2_post, i4_post, i3_post, len_post, hh, hs, hi1,
      incidentEnc, u8Str, List.length_append, List.length_cons, List.length_take, length_leBytes, evLenCap]
    generalize (cowList c).length = L at *
    generalize Usize.max = M at *
    norm_num at this ⊢
    have h2 : min 2 M = 2 := by omega
    have h3 : min (2 + 1) M = 3 := by omega
    have h4 : min M 4294967276 = 4294967276 := by omega
    rw [h2, h3, h4]
    rcases Nat.le_total L 255 with hL | hL
    · rw [min_eq_left hL, min_eq_right hL, show 2 + (L + 1) = 3 + L by omega]
    · rw [min_eq_right hL, min_eq_left hL]

end mysql_common
