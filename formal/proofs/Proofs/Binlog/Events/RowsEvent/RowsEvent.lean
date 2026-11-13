import Defs
import Proofs.Util.BinlogEvRows

/-! Statements for `struct RowsEvent and its impls` (spec file: `Specs/Binlog/Events/RowsEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `event_type`. -/
theorem binlog.events.rows_event.RowsEvent.impl.event_type_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.event_type e = ok e.event_type := by
  rfl

/-- `table_id`. -/
theorem binlog.events.rows_event.RowsEvent.impl.table_id_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.table_id e = ok e.table_id.1 := by
  rfl

/-- `num_columns`. -/
theorem binlog.events.rows_event.RowsEvent.impl.num_columns_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.num_columns e = ok e.num_columns.1 := by
  rfl

/-- `rows_data`: the raw rows. -/
theorem binlog.events.rows_event.RowsEvent.impl.rows_data_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.rows_data e ⦃ s => s.val = cowList e.rows_data.1 ⦄ := by
  exact PKUtil.eof_as_bytes_spec _

/-- `flags`: the known flag bits. -/
theorem binlog.events.rows_event.RowsEvent.impl.flags_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.impl.flags e ⦃ f => f.val = e.flags.1.val &&& rowsEventFlagsAll ⦄ := by
  unfold binlog.events.rows_event.RowsEvent.impl.flags
  rw [misc.raw.flags.RawFlags.get_eq]
  exact BERUtil.rows_flags_truncate _

/-- `flags_raw`: all the flag bits. -/
theorem binlog.events.rows_event.RowsEvent.flags_raw_eq (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.flags_raw e = ok e.flags.1 := by
  rfl

/-- `len`: `rowsLenCrate`. (64-bit target, as configured). -/
theorem binlog.events.rows_event.RowsEvent.len_spec (h64 : Target64) (e : binlog.events.rows_event.RowsEvent) (v : binlog.consts.BinlogVersion) :
    binlog.events.rows_event.RowsEvent.len e v ⦃ n => n.val = rowsLenCrate e ⦄ := by
  exact BERUtil.rows_len64 h64 e v

/-- `len` of a consistent v2 event: the length `serialize` writes, capped. -/
theorem binlog.events.rows_event.RowsEvent.len_v2 (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (h2 : rowsIsV2 e.event_type = true) (v : binlog.consts.BinlogVersion) :
    binlog.events.rows_event.RowsEvent.len e v ⦃ n => n.val = min (rowsEnc e).length evLenCap ⦄ := by
  apply WP.spec_mono (BERUtil.rows_len_gen e v (BERUtil.rows_consistent_bm e hc).2.2)
  intro n hn
  rw [hn, BERUtil.rowsLenCrate_v2 e hc h2]

/-- **Quirk:** `len` of a consistent v1 event is 2 more than the length `serialize` writes (when under the cap). -/
theorem binlog.events.rows_event.RowsEvent.len_v1 (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (h1 : rowsIsV2 e.event_type = false) (v : binlog.consts.BinlogVersion)
    (hcap : (rowsEnc e).length + 2 ≤ evLenCap) :
    binlog.events.rows_event.RowsEvent.len e v ⦃ n => n.val = (rowsEnc e).length + 2 ⦄ := by
  apply WP.spec_mono (BERUtil.rows_len_gen e v (BERUtil.rows_consistent_bm e hc).2.2)
  intro n hn
  rw [hn, BERUtil.rowsLenCrate_v1' e hc h1 hcap]

/-- `rows(tme)`: an iterator over the raw rows, with that table map. -/
theorem binlog.events.rows_event.RowsEvent.rows_spec (e : binlog.events.rows_event.RowsEvent) (tme : binlog.events.table_map_event.TableMapEvent) :
    binlog.events.rows_event.RowsEvent.rows e tme ⦃ it => it.rows_event = e ∧ it.table_map_event = tme ∧ it.rows_data.val = cowList e.rows_data.1 ⦄ := by
  unfold binlog.events.rows_event.RowsEvent.rows
  step with PKUtil.eof_as_bytes_spec as ⟨ s, hs ⟩
  simp [hs]

/-- `into_owned`: the same fields (now owned). -/
theorem binlog.events.rows_event.RowsEvent.into_owned_spec (e : binlog.events.rows_event.RowsEvent) :
    binlog.events.rows_event.RowsEvent.into_owned e ⦃ e' => rowsView e' = rowsView e ⦄ := by
  unfold binlog.events.rows_event.RowsEvent.into_owned
  step with PKUtil.rawbytes_into_owned_spec as ⟨ rb, hrb ⟩
  rcases e with ⟨et, ti, fl, ex, nc, cb, ca, rd⟩
  cases cb <;> cases ca <;> simp only [] <;> step* <;> simp_all [rowsView]

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.SIZE_eq :
    binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.SIZE = none := by
  unfold binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.SIZE; rfl

/-- `MyDeserialize` with the context's event type and FDE: total; `rowsRead`. `RawFlags::SIZE` is `size_of::<u16>()`, which is 2 in Rust; the Lean `size_of` is deliberately unspecified (FunsExternal.lean), so this is a hypothesis, not an axiom. -/
theorem binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.deserialize_spec (h64 : Target64) (hsz : core.mem.size_of Std.U16 = ok 2#usize) (ctx : binlog.events.rows_event.RowsEventCtx) (buf : io.ParseBuf) :
    binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.deserialize ctx buf ⦃ r rest => ReadsAs rowsView (rowsRead ctx.event_type (postHeaderLen (fdeLens ctx.binlog_ctx.fde) ctx.event_type) (postHeaderLen (fdeLens ctx.binlog_ctx.fde) .WRITE_ROWS_EVENT) buf.val) r rest ⦄ := by
  exact BERUtil.rows_deser_ctx h64 hsz ctx buf

/-- `MySerialize`: appends `rowsEnc`. (64-bit target, as configured). -/
theorem binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (h64 : Target64) (e : binlog.events.rows_event.RowsEvent) (buf : alloc.vec.Vec U8) (h : buf.length + (rowsEnc e).length ≤ Usize.max) :
    binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ rowsEnc e ⦄ := by
  exact BERUtil.rows_serialize64 h64 e buf h

/-- Round trip, for a consistent event of the context's type with a table id below `2^48`, read with an FDE whose post-header lengths agree with the type (6 bytes excluded; equal to `WRITE_ROWS_EVENT`'s iff v2). `RawFlags::SIZE` is `size_of::<u16>()`, which is 2 in Rust; the Lean `size_of` is deliberately unspecified (FunsExternal.lean), so this is a hypothesis, not an axiom. -/
theorem binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.roundtrip (h64 : Target64) (hsz : core.mem.size_of Std.U16 = ok 2#usize) (e : binlog.events.rows_event.RowsEvent) (hc : RowsConsistent e) (ht : e.table_id.1.val < 2 ^ 48)
    (ctx : binlog.events.rows_event.RowsEventCtx) (he : eventTypeCode ctx.event_type = eventTypeCode e.event_type)
    (hp : postHeaderLen (fdeLens ctx.binlog_ctx.fde) ctx.event_type ≠ 6) (hv : postHeaderLen (fdeLens ctx.binlog_ctx.fde) ctx.event_type = postHeaderLen (fdeLens ctx.binlog_ctx.fde) .WRITE_ROWS_EVENT ↔ rowsIsV2 e.event_type = true)
    (buf : io.ParseBuf) (h : buf.val = rowsEnc e) :
    binlog.events.rows_event.RowsEvent.Insts.Mysql_commonProtoMyDeserializeDeRowsEventCtx.deserialize ctx buf ⦃ r rest => (okPart r).map rowsView = some (rowsView e) ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (BERUtil.rows_deser_ctx h64 hsz ctx buf)
  rintro ⟨r, rest⟩ hr
  simp only [WP.uncurry'] at hr ⊢
  rw [h, BERUtil.rowsRead_congr _ _ he, Defs.rowsRead_rowsEnc e hc ht _ _ hp hv] at hr
  exact hr

end mysql_common
