import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Binlog.Consts.EventType

/-! Statements for `struct BinlogEventHeader and its impls` (spec file: `Specs/Binlog/Events.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.EvHdrUtil

namespace mysql_common

/-- `LEN`: 19. -/
theorem binlog.events.BinlogEventHeader.LEN_eq :
    binlog.events.BinlogEventHeader.LEN = 19#usize := by
  unfold binlog.events.BinlogEventHeader.LEN; rfl

/-- `new`: those fields (the type as its code, the flags' bits). -/
theorem binlog.events.BinlogEventHeader.new_spec (ts : U32) (t : binlog.consts.EventType) (sid size pos : U32) (fl : binlog.consts.EventFlags) :
    binlog.events.BinlogEventHeader.new ts t sid size pos fl ⦃ h => h.timestamp.1 = ts ∧ h.event_type.1.val = eventTypeCode t ∧
      h.server_id.1 = sid ∧ h.event_size.1 = size ∧ h.log_pos.1 = pos ∧ h.flags.1 = fl ⦄ := by
  unfold binlog.events.BinlogEventHeader.new
  have e : (UScalar.cast .U8 (read_discriminant t)).val = eventTypeCode t := by
    cases t <;> simp [read_discriminant, binlog.consts.EventType.read_discriminant, eventTypeCode]
  simp only [binlog.consts.EventFlags.bits, bind_ok]
  step*

/-- `timestamp`. -/
theorem binlog.events.BinlogEventHeader.impl.timestamp_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.timestamp h = ok h.timestamp.1 := by
  obtain ⟨⟨_, _⟩⟩ := h; rfl

/-- `event_type_raw`: the type byte. -/
theorem binlog.events.BinlogEventHeader.event_type_raw_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.event_type_raw h = ok h.event_type.1 := by
  obtain ⟨_, ⟨_, _⟩⟩ := h; rfl

/-- `event_type`: the known type with that code, or the raw byte as an error. -/
theorem binlog.events.BinlogEventHeader.impl.event_type_spec (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.event_type h ⦃ r => match eventTypeOfCode h.event_type.1.val with
      | some t => r = .Ok t
      | none => r = .Err h.event_type.1 ⦄ := by
  obtain ⟨_, ⟨b, u⟩⟩ := h
  simp only [binlog.events.BinlogEventHeader.impl.event_type, misc.raw._const.RawConst.get,
    binlog.consts.EventType.Insts.CoreConvertTryFromU8UnknownEventType.try_from_spec]
  split <;> simp_all

/-- `server_id`. -/
theorem binlog.events.BinlogEventHeader.impl.server_id_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.server_id h = ok h.server_id.1 := by
  obtain ⟨_, _, ⟨_, _⟩⟩ := h; rfl

/-- `event_size`. -/
theorem binlog.events.BinlogEventHeader.impl.event_size_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.event_size h = ok h.event_size.1 := by
  obtain ⟨_, _, _, ⟨_, _⟩⟩ := h; rfl

/-- `log_pos`. -/
theorem binlog.events.BinlogEventHeader.impl.log_pos_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.log_pos h = ok h.log_pos.1 := by
  obtain ⟨_, _, _, _, ⟨_, _⟩⟩ := h; rfl

/-- `flags`: the known flag bits (`from_bits_truncate`). -/
theorem binlog.events.BinlogEventHeader.impl.flags_spec (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.impl.flags h ⦃ f => f.val = h.flags.1.val &&& eventFlagsAll ⦄ := by
  obtain ⟨_, _, _, _, _, ⟨b, u⟩⟩ := h
  have e : (1#u16 ||| 2#u16 ||| 4#u16 ||| 8#u16 ||| 16#u16 ||| 32#u16 ||| 64#u16 ||| 128#u16 ||| 256#u16 ||| 512#u16) = 1023#u16 := by decide
  simp [e, binlog.events.BinlogEventHeader.impl.flags, misc.raw.flags.RawFlags.get, binlog.consts.EventFlags.Insts.BitflagsTraitsFlagsU16.FLAGS, bitflags.traits.Flag.new, Array.to_slice, Array.make, U16.Insts.BitflagsTraitsBits.EMPTY, binlog.consts.EventFlags.Insts.BitflagsTraitsFlagsU16.bits, binlog.consts.EventFlags.bits, binlog.consts.EventFlags.Insts.BitflagsTraitsFlagsU16.from_bits_retain, binlog.consts.EventFlags.from_bits_retain, U16.Insts.CoreOpsBitBitOrU16U16.bitor, U16.Insts.CoreOpsBitBitAndU16U16.bitand, binlog.consts.EventFlags.LOG_EVENT_BINLOG_IN_USE_F, binlog.consts.EventFlags.LOG_EVENT_FORCED_ROTATE_F, binlog.consts.EventFlags.LOG_EVENT_THREAD_SPECIFIC_F, binlog.consts.EventFlags.LOG_EVENT_SUPPRESS_USE_F, binlog.consts.EventFlags.LOG_EVENT_UPDATE_TABLE_MAP_VERSION_F, binlog.consts.EventFlags.LOG_EVENT_ARTIFICIAL_F, binlog.consts.EventFlags.LOG_EVENT_RELAY_LOG_F, binlog.consts.EventFlags.LOG_EVENT_IGNORABLE_F, binlog.consts.EventFlags.LOG_EVENT_NO_FILTER_F, binlog.consts.EventFlags.LOG_EVENT_MTS_ISOLATE_F, eventFlagsAll]

/-- `flags_raw`: all the flag bits. -/
theorem binlog.events.BinlogEventHeader.flags_raw_eq (h : binlog.events.BinlogEventHeader) :
    binlog.events.BinlogEventHeader.flags_raw h = ok h.flags.1 := by
  obtain ⟨_, _, _, _, _, ⟨_, _⟩⟩ := h; rfl

/-- `MyDeserialize::SIZE` is `Some(19)`. -/
theorem binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 19#usize := by
  unfold binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE binlog.events.BinlogEventHeader.LEN; rfl

/-- `MyDeserialize`: total; on at least 19 bytes the header whose layout is the first 19 (`evHeaderEnc` is injective, so this determines it), else an error with the buffer unchanged. -/
theorem binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      if 19 ≤ buf.length then (okPart r).map evHeaderEnc = some (buf.val.take 19) ∧ rest.val = buf.val.drop 19
      else okPart r = none ∧ rest = buf ⦄ := by
  unfold binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with pu_usize as ⟨r, rest, hr⟩
  have hL : binlog.events.BinlogEventHeader.LEN.val = 19 := by unfold binlog.events.BinlogEventHeader.LEN; rfl
  rw [hL] at hr; split_ifs at hr ⊢ with hlen
  · obtain ⟨pb, rfl, hpb, hrest⟩ := hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have l0 : pb.val.length = 19 := by rw [hpb, List.length_take]; simp only [Slice.length] at hlen; omega
    step with pu_leu32 as ⟨r1, b1, v1, hr1, h1, hb1⟩
    subst hr1
    simp only [bind_ok]
    have l1 : b1.val.length = 15 := by simp [hb1, l0]
    step with pu_const_u8 as ⟨r2, b2, v2, hr2, h2, hb2⟩
    subst hr2
    simp only [bind_ok]
    have l2 : b2.val.length = 14 := by simp [hb2, l1]
    step with pu_leu32 as ⟨r3, b3, v3, hr3, h3, hb3⟩
    subst hr3
    simp only [bind_ok]
    have l3 : b3.val.length = 10 := by simp [hb3, l2]
    step with pu_leu32 as ⟨r4, b4, v4, hr4, h4, hb4⟩
    subst hr4
    simp only [bind_ok]
    have l4 : b4.val.length = 6 := by simp [hb4, l3]
    step with pu_leu32 as ⟨r5, b5, v5, hr5, h5, hb5⟩
    subst hr5
    simp only [bind_ok]
    have l5 : b5.val.length = 2 := by simp [hb5, l4]
    step with pu_flags_leu16 as ⟨r6, b6, v6, hr6, h6, hb6⟩
    subst hr6
    simp only [bind_ok]
    apply (WP.spec_ok _).mpr
    refine ⟨?_, hrest⟩
    have hb6' : b6.val = [] := by rw [← List.length_eq_zero_iff, hb6]; simp [l5]
    have d1 := take_append_of_drop 4 hb1
    have d2 := take_append_of_drop 1 hb2
    have d3 := take_append_of_drop 4 hb3
    have d4 := take_append_of_drop 4 hb4
    have d5 := take_append_of_drop 4 hb5
    have d6 := take_append_of_drop 2 hb6
    rw [hb6'] at d6
    simp only [okPart, Option.map, evHeaderEnc]
    rw [leBytes_of_val 4 _ _ h1 (by omega), singleton_of_val _ _ h2 (by omega), leBytes_of_val 4 _ _ h3 (by omega),
      leBytes_of_val 4 _ _ h4 (by omega), leBytes_of_val 4 _ _ h5 (by omega), leBytes_of_val 2 _ _ h6 (by omega)]
    conv_rhs => rw [← hpb, d1, d2, d3, d4, d5, d6]
    simp
  · cases r with
    | Ok pb => simp [okPart] at hr
    | Err e =>
      obtain ⟨-, rfl⟩ := hr
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart]

/-- `MySerialize`: appends the 19-byte header. -/
theorem binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMySerialize.serialize_spec (h : binlog.events.BinlogEventHeader) (buf : alloc.vec.Vec U8) (hb : buf.length + 19 ≤ Usize.max) :
    binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMySerialize.serialize h buf ⦃ buf' => buf'.val = buf.val ++ evHeaderEnc h ⦄ := by
  unfold binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [misc.raw.int.RawInt.serialize_eq, misc.raw._const.RawConst.Insts.Mysql_commonProtoMySerialize.serialize_eq,
    misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMySerialize.serialize_eq]
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec as ⟨b1, hb1⟩
  step with U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec as ⟨b2, hb2⟩
  · simp_all [alloc.vec.Vec.length]; omega
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec as ⟨b3, hb3⟩
  · simp_all [alloc.vec.Vec.length]; omega
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec as ⟨b4, hb4⟩
  · simp_all [alloc.vec.Vec.length]; omega
  step with misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec as ⟨b5, hb5⟩
  · simp_all [alloc.vec.Vec.length]; omega
  step with misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.serialize_spec as ⟨b6, hb6⟩
  · simp_all [alloc.vec.Vec.length]
  simp [hb6, hb5, hb4, hb3, hb2, hb1, evHeaderEnc]

/-- Round trip: a written header reads back as itself. -/
theorem binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h : binlog.events.BinlogEventHeader) (tail : List U8) (buf : io.ParseBuf) (hb : buf.val = evHeaderEnc h ++ tail) :
    binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => okPart r = some h ∧ rest.val = tail ⦄ := by
  apply WP.spec_mono (binlog.events.BinlogEventHeader.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  have hl : 19 ≤ buf.length := by simp [Slice.length, hb, evHeaderEnc_len]
  simp only [hl, ite_true] at hr
  obtain ⟨h1, h2⟩ := hr
  have e19 : buf.val.take 19 = evHeaderEnc h := by rw [hb]; exact List.take_left' (evHeaderEnc_len h)
  have d19 : buf.val.drop 19 = tail := by rw [hb]; exact List.drop_left' (evHeaderEnc_len h)
  refine ⟨?_, by rw [h2, d19]⟩
  cases r with
  | Ok x =>
    simp only [okPart, Option.map, e19, Option.some.injEq] at h1 ⊢
    exact evHeaderEnc_inj _ _ h1
  | Err e => simp [okPart] at h1

end mysql_common
