import Defs

/-! Statements for `struct FormatDescriptionEvent and its impls` (spec file: `Specs/Binlog/Events/FormatDescriptionEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `SERVER_VER_LEN`: 50. -/
theorem binlog.events.format_description_event.SERVER_VER_LEN_eq :
    binlog.events.format_description_event.SERVER_VER_LEN = 50#usize := by
  sorry

/-- `new(version)`: that version, an empty server version and post-header array, timestamp 0, the default footer. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.new_spec (v : binlog.consts.BinlogVersion) :
    binlog.events.format_description_event.FormatDescriptionEvent.new v ⦃ e => fdeView e = { version := v, serverVersion := [], createTimestamp := 0, lens := [] } ∧
      footerAlg e.footer = some 0 ∧ e.footer.checksum_enabled = true ⦄ := by
  sorry

/-- `with_binlog_version`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.with_binlog_version_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_binlog_version e v ⦃ e' => fdeView e' = { fdeView e with version := v } ∧ e'.footer = e.footer ⦄ := by
  sorry

/-- `with_server_version` (stored as given; padded or truncated to 50 bytes only when written). -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.with_server_version_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.format_description_event.FormatDescriptionEvent) (sv : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into sv = ok c) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_server_version into e sv ⦃ e' => fdeView e' = { fdeView e with serverVersion := cowList c } ∧ e'.footer = e.footer ⦄ := by
  sorry

/-- `with_create_timestamp`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.with_create_timestamp_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (ts : U32) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_create_timestamp e ts ⦃ e' => fdeView e' = { fdeView e with createTimestamp := ts.val } ∧ e'.footer = e.footer ⦄ := by
  sorry

/-- `with_event_type_header_lengths`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.with_event_type_header_lengths_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (e : binlog.events.format_description_event.FormatDescriptionEvent) (ls : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into ls = ok c) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_event_type_header_lengths into e ls ⦃ e' => fdeView e' = { fdeView e with lens := cowList c } ∧ e'.footer = e.footer ⦄ := by
  sorry

/-- `with_footer`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.with_footer_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) (f : binlog.events.BinlogEventFooter) :
    binlog.events.format_description_event.FormatDescriptionEvent.with_footer e f = ok { e with footer := f } := by
  sorry

/-- `binlog_version`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.impl.binlog_version_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.binlog_version e = ok e.binlog_version.1 := by
  sorry

/-- `server_version_raw`: the stored server version, its first 50 bytes. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.server_version_raw_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.server_version_raw e ⦃ s => s.val = (cowList e.server_version.1).take 50 ⦄ := by
  sorry

/-- `create_timestamp`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.impl.create_timestamp_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.create_timestamp e = ok e.create_timestamp.1 := by
  sorry

/-- `event_header_length`: always 19. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.impl.event_header_length_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.event_header_length e = ok 19#u8 := by
  sorry

/-- `event_type_header_lengths`: the post-header lengths array. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.impl.event_type_header_lengths_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.event_type_header_lengths e ⦃ s => s.val = fdeLens e ⦄ := by
  sorry

/-- `footer`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.impl.footer_eq (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.impl.footer e = ok e.footer := by
  sorry

/-- `get_event_type_header_length(t)`: `postHeaderLen` (0 for `UNKNOWN_EVENT`; else the array entry `t - 1`, or the default if the array is shorter). -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.get_event_type_header_length_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (t : binlog.consts.EventType) :
    binlog.events.format_description_event.FormatDescriptionEvent.get_event_type_header_length e t ⦃ n => n.val = postHeaderLen (fdeLens e) t ⦄ := by
  sorry

/-- `into_owned`: the same fields and footer. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.into_owned_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) :
    binlog.events.format_description_event.FormatDescriptionEvent.into_owned e ⦃ e' => fdeView e' = fdeView e ∧ e'.footer = e.footer ⦄ := by
  sorry

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  sorry

/-- `MyDeserialize`: total; `fdeRead` (a known version, header length 19, the rest as the post-header lengths); the footer is the default. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs fdeView (fdeRead buf.val) r rest ∧
      ∀ e, okPart r = some e → footerAlg e.footer = some 0 ∧ e.footer.checksum_enabled = true ⦄ := by
  sorry

/-- `MySerialize`: appends the layout `fdeEnc`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (buf : alloc.vec.Vec U8)
    (h : buf.length + (fdeEnc e).length ≤ Usize.max) :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ fdeEnc e ⦄ := by
  sorry

/-- Round trip: the fields come back, the server version padded (or truncated) to 50 bytes. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.format_description_event.FormatDescriptionEvent) (ctx : binlog.BinlogCtx) (buf : io.ParseBuf) (h : buf.val = fdeEnc e) :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map fdeView = some { fdeView e with serverVersion := fixedText 50 (cowList e.server_version.1) } ∧ rest.val = [] ⦄ := by
  sorry

/-- `BinlogStruct::len`: the length of what `serialize` writes (`fdeEnc`), capped at `u32::MAX - 19`. -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.format_description_event.FormatDescriptionEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = min (fdeEnc e).length evLenCap ⦄ := by
  sorry

/-- `BinlogEvent::EVENT_TYPE`: `FORMAT_DESCRIPTION_EVENT` (15). -/
theorem binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .FORMAT_DESCRIPTION_EVENT := by
  sorry

end mysql_common
