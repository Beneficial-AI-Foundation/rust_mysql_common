import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Binlog.Events.Mod.BinlogEventFooter
import Proofs.Binlog.Consts.EventType
import Proofs.Binlog.Events.QueryEvent.QueryEvent
import Proofs.Binlog.Events.RotateEvent.RotateEvent
import Proofs.Binlog.Events.FormatDescriptionEvent.FormatDescriptionEvent
import Proofs.Binlog.Events.TableMapEvent.TableMapEvent
import Proofs.Binlog.Events.GtidEvent.GtidEvent
import Proofs.Binlog.Events.WriteRowsEventV1.WriteRowsEventV1
import Proofs.Binlog.Events.UpdateRowsEventV1.UpdateRowsEventV1
import Proofs.Binlog.Events.DeleteRowsEventV1.DeleteRowsEventV1
import Proofs.Binlog.Events.WriteRowsEvent.WriteRowsEvent
import Proofs.Binlog.Events.UpdateRowsEvent.UpdateRowsEvent
import Proofs.Binlog.Events.DeleteRowsEvent.DeleteRowsEvent
import Proofs.Binlog.Events.PartialUpdateRowsEvent.PartialUpdateRowsEvent

/-! Statements for `struct Event and its impls` (spec file: `Specs/Binlog/Events.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.EvHdrUtil

namespace mysql_common

/-- `fde`: the format description event the event was read with. -/
theorem binlog.events.Event.impl.fde_eq (self : binlog.events.Event) :
    binlog.events.Event.impl.fde self = ok self.fde := by
  rfl

/-- `header`: the common header. -/
theorem binlog.events.Event.impl.header_eq (self : binlog.events.Event) :
    binlog.events.Event.impl.header self = ok self.header := by
  rfl

/-- `data`: the event data (footer stripped). -/
theorem binlog.events.Event.impl.data_spec (self : binlog.events.Event) :
    binlog.events.Event.impl.data self ⦃ s => s.val = self.data.val ⦄ := by
  simp [binlog.events.Event.impl.data, alloc.vec.Vec.deref]

/-- `footer`. -/
theorem binlog.events.Event.impl.footer_eq (self : binlog.events.Event) :
    binlog.events.Event.impl.footer self = ok self.footer := by
  rfl

/-- `checksum`: the stored checksum iff the event carries one (`evHasChecksum`). -/
theorem binlog.events.Event.impl.checksum_eq (self : binlog.events.Event) :
    binlog.events.Event.impl.checksum self = ok (if evHasChecksum self.footer self.header.event_type.1.val then some self.checksum else none) := by
  obtain ⟨fde, ⟨h1, ⟨t, u⟩, h3, h4, h5, h6⟩, data, ⟨ca, en⟩, cs⟩ := self
  cases ca with
  | none => simp [binlog.events.Event.impl.checksum, binlog.events.event_checksum, evHasChecksum, footerAlg]
  | some c =>
    obtain ⟨a, v⟩ := c
    have e15 : (15#u8 + 0#u8 : Result U8) = ok 15#u8 := by rfl
    have ec : UScalar.cast .U8 15#u8 = 15#u8 := by rfl
    simp only [binlog.events.Event.impl.checksum, binlog.events.event_checksum, evHasChecksum, footerAlg, e15, ec, bind_ok, lift,
      Option.map]
    by_cases ht : t = 15#u8
    · subst ht; simp
    · have ht' : t.val ≠ 15 := fun h => ht (UScalar.eq_of_val_eq (by simpa using h))
      by_cases ha : a = 0#u8
      · subst ha; simp [ht, ht']
      · have ha' : a.val ≠ 0 := fun h => ha (UScalar.eq_of_val_eq (by simpa using h))
        simp [ht, ht', ha, ha']

/-- `len` (private, used by `write`): `eventLen`. -/
theorem binlog.events.Event.len_spec (self : binlog.events.Event) (v : binlog.consts.BinlogVersion) :
    binlog.events.Event.len self v ⦃ n => n.val = eventLen self ⦄ := by
  obtain ⟨fde, ⟨h1, ⟨t, u⟩, h3, h4, h5, h6⟩, data, ft, cs⟩ := self
  have e15 : (15#u8 + 0#u8 : Result U8) = ok 15#u8 := by rfl
  have ec : UScalar.cast .U8 15#u8 = 15#u8 := by rfl
  have hL : binlog.events.BinlogEventHeader.LEN = 19#usize := by unfold binlog.events.BinlogEventHeader.LEN; rfl
  have hM : (UScalar.cast .Usize core.num.U32.MAX).val = 2 ^ 32 - 1 := by
    rw [IntAndMisc.cast_usize_small _ (by decide)]; rfl
  have hUM : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  simp only [binlog.events.Event.len, e15, ec, bind_ok, lift]
  apply WP.spec_bind (binlog.events.BinlogEventFooter.get_checksum_alg_spec ft)
  intro r hr
  unfold binlog.events.event_len
  simp only [lift, bind_ok, hL]
  have hD : binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_ALG_DESC_LEN = 1#usize := by
    unfold binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_ALG_DESC_LEN; rfl
  have hC : binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_LEN = 4#usize := by
    unfold binlog.events.BinlogEventFooter.BINLOG_CHECKSUM_LEN; rfl
  have hl : data.len.val = data.val.length := rfl
  obtain ⟨ca, en⟩ := ft
  have ht : (t = 15#u8) ↔ t.val = 15 := ⟨fun h => by subst h; rfl, fun h => UScalar.eq_of_val_eq (by simpa using h)⟩
  cases ca with
  | none =>
    simp only [footerAlg, Option.map] at hr
    subst hr
    simp only
    step*
    simp_all [sat_add_usize, eventLen, footerAlg, evLenCap, Option.map, Option.bind]
    omega
  | some c =>
    obtain ⟨a, w⟩ := c
    simp only [footerAlg, Option.map] at hr
    cases hca : checksumAlgOfCode a.val with
    | none =>
      rw [hca] at hr; subst hr
      simp only
      step*
      simp_all [sat_add_usize, eventLen, footerAlg, evLenCap, Option.map, Option.bind]
      omega
    | some alg =>
      rw [hca] at hr; subst hr
      simp only [hD, hC]
      by_cases h15 : t = 15#u8
      · simp only [h15, decide_true, ite_true, bind_ok]
        step*
        simp_all [sat_add_usize, eventLen, footerAlg, evLenCap, Option.map, Option.bind]
        omega
      · simp only [h15, decide_false, Bool.false_eq_true, ite_false, bind_ok]
        cases alg
        all_goals
          simp only [binlog.consts.BinlogChecksumAlg.Insts.CoreCmpPartialEqBinlogChecksumAlg.eq,
            binlog.consts.BinlogChecksumAlg.read_discriminant, bind_ok]
          simp_all [eventLen, footerAlg, checksumAlgCode, evLenCap, Option.map, Option.bind]
          step*
          simp_all [sat_add_usize]
          omega

/-- The `parse` call of `read_event`, as a function of the event. -/
private theorem read_event_unfold {T : Type} (inst : binlog.BinlogEvent T) (self : binlog.events.Event) (hlen : self.data.length + 19 ≤ Usize.max)
    (ctx : binlog.BinlogCtx) (hc : ctx.event_size.val = 19 + self.data.length ∧ ctx.fde = self.fde ∧
      ctx.event_type_raw = self.header.event_type.1) (buf : io.ParseBuf) (hb : buf.val = self.data.val) :
    binlog.events.Event.read_event inst self = (do
      let (r, event_data) ← io.ParseBuf.parse inst.BinlogStructInst.protoMyDeserializeASelfBinlogCtxInst buf ctx
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let b ← io.ParseBuf.is_empty event_data
        if b then ok (core.result.Result.Ok val)
        else
          let e ← binlog.trusted.bytes_remaining_error T
          ok (core.result.Result.Err e)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
          (core.convert.FromSame core.io.error.Error) residual) := by
  obtain ⟨fde, ⟨h1, ⟨t, u⟩, h3, h4, h5, h6⟩, data, ft, cs⟩ := self
  have hL : binlog.events.BinlogEventHeader.LEN = 19#usize := by unfold binlog.events.BinlogEventHeader.LEN; rfl
  obtain ⟨es, hes, hesv⟩ := PBUtil.spec_eq_ok (show (binlog.events.BinlogEventHeader.LEN + alloc.vec.Vec.len data)
      ⦃ z => z.val = 19 + data.length ⦄ by rw [hL]; step*)
  have hs : alloc.vec.Vec.deref data = buf := by
    apply Slice.ext; simp only [alloc.vec.Vec.deref, Slice.from_val]; exact hb.symm
  have hctx : ({ event_size := es, fde := fde, event_type_raw := t } : binlog.BinlogCtx) = ctx := by
    obtain ⟨c1, c2, c3⟩ := ctx
    simp only at hc
    obtain ⟨h1, rfl, rfl⟩ := hc
    have : es = c1 := UScalar.eq_of_val_eq (by rw [hesv, h1])
    rw [this]
  unfold binlog.events.Event.read_event
  simp only []
  rw [hes, bind_ok, hs]
  have het : binlog.events.BinlogEventHeader.event_type_raw
      { timestamp := h1, event_type := (t, u), server_id := h3, event_size := h4, log_pos := h5, flags := h6 } = ok t := rfl
  rw [het, bind_ok]
  simp only [binlog.BinlogCtx.new, bind_ok]
  rw [hctx]
  rfl

private theorem is_empty_eq (b : io.ParseBuf) : io.ParseBuf.is_empty b = ok (decide (b.val = [])) := by
  simp only [io.ParseBuf.is_empty, io.ParseBuf.len, bind_ok]
  congr 1
  simp only [decide_eq_decide]
  constructor
  · intro h; have := congrArg UScalar.val h; simpa [Slice.len] using this
  · intro h; apply UScalar.eq_of_val_eq; simp [Slice.len, h]

/-- `read_event::<T>`: `T` is parsed from the data with `parse` (so `T::SIZE` is checked) in the context (`19 + data.len()`, the FDE, the raw type); its error is passed on; a success is `Ok` iff no bytes are left, and otherwise the (opaque) `bytes_remaining_error`. -/
theorem binlog.events.Event.read_event_spec {T : Type} (inst : binlog.BinlogEvent T) (self : binlog.events.Event) (hlen : self.data.length + 19 ≤ Usize.max)
    (ctx : binlog.BinlogCtx) (hc : ctx.event_size.val = 19 + self.data.length ∧ ctx.fde = self.fde ∧
      ctx.event_type_raw = self.header.event_type.1) (buf : io.ParseBuf) (hb : buf.val = self.data.val)
    (r0 : core.result.Result T core.io.error.Error) (rest0 : io.ParseBuf)
    (hp : io.ParseBuf.parse inst.BinlogStructInst.protoMyDeserializeASelfBinlogCtxInst buf ctx = ok (r0, rest0)) :
    binlog.events.Event.read_event inst self = (match r0 with
      | .Err e => ok (.Err e)
      | .Ok x => if rest0.val = [] then ok (.Ok x) else do
          let e ← binlog.trusted.bytes_remaining_error T
          ok (.Err e)) := by
  rw [read_event_unfold inst self hlen ctx hc buf hb]
  cases r0 with
  | Ok x =>
    dsimp only
    rw [hp, bind_ok]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, is_empty_eq]
    by_cases h : rest0.val = [] <;> simp [h]
  | Err e =>
    dsimp only
    rw [hp, bind_ok]
    simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_event::<T>` fails (panics) exactly as `T`'s `parse` does. -/
theorem binlog.events.Event.read_event_fail {T : Type} (inst : binlog.BinlogEvent T) (self : binlog.events.Event) (hlen : self.data.length + 19 ≤ Usize.max)
    (ctx : binlog.BinlogCtx) (hc : ctx.event_size.val = 19 + self.data.length ∧ ctx.fde = self.fde ∧
      ctx.event_type_raw = self.header.event_type.1) (buf : io.ParseBuf) (hb : buf.val = self.data.val) (err : Error)
    (hp : io.ParseBuf.parse inst.BinlogStructInst.protoMyDeserializeASelfBinlogCtxInst buf ctx = fail err) :
    binlog.events.Event.read_event inst self = fail err := by
  rw [read_event_unfold inst self hlen ctx hc buf hb, hp]
  simp

private theorem read_data_get (self : binlog.events.Event) :
    misc.raw._const.RawConst.get U8.Insts.Mysql_commonMiscRawIntIntReprU8 core.marker.CopyU8
      binlog.consts.EventType.Insts.CoreConvertTryFromU8UnknownEventType self.header.event_type =
    ok (match eventTypeOfCode self.header.event_type.1.val with
        | some x => .Ok x
        | none => .Err self.header.event_type.1) := by
  rw [misc.raw._const.RawConst.get_eq]
  exact binlog.consts.EventType.Insts.CoreConvertTryFromU8UnknownEventType.try_from_spec _

/-- `read_data` on an unknown type code (41, ≥ 43): `Ok(None)`. -/
theorem binlog.events.Event.read_data_unknown (self : binlog.events.Event) (h : eventTypeOfCode self.header.event_type.1.val = none) :
    binlog.events.Event.read_data self = ok (.Ok none) := by
  unfold binlog.events.Event.read_data
  rw [read_data_get, h]
  simp only [bind_ok]

/-- `read_data` on a type it does not parse: the data-less variant of that type, or the variant holding the raw data. -/
theorem binlog.events.Event.read_data_unparsed (self : binlog.events.Event) (h : self.header.event_type.1.val ∈ edUnitCodes ++ edRawCodes) :
    binlog.events.Event.read_data self ⦃ r => ∃ d, r = .Ok (some d) ∧ edTypeCode d = self.header.event_type.1.val ∧
      (if self.header.event_type.1.val ∈ edUnitCodes then edUnit d = true else edRaw d = some self.data.val) ⦄ := by
  have hc := h
  simp only [edUnitCodes, edRawCodes, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  unfold binlog.events.Event.read_data
  rw [read_data_get]
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  · rw [hc, show eventTypeOfCode 0 = some .UNKNOWN_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edUnit, alloc.vec.Vec.deref]
  · rw [hc, show eventTypeOfCode 3 = some .STOP_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edUnit, alloc.vec.Vec.deref]
  · rw [hc, show eventTypeOfCode 7 = some .SLAVE_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edUnit, alloc.vec.Vec.deref]
  · rw [hc, show eventTypeOfCode 27 = some .HEARTBEAT_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edUnit, alloc.vec.Vec.deref]
  · rw [hc, show eventTypeOfCode 1 = some .START_EVENT_V3 from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]
  · rw [hc, show eventTypeOfCode 6 = some .LOAD_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]
  · rw [hc, show eventTypeOfCode 8 = some .CREATE_FILE_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]
  · rw [hc, show eventTypeOfCode 9 = some .APPEND_BLOCK_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]
  · rw [hc, show eventTypeOfCode 10 = some .EXEC_LOAD_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]
  · rw [hc, show eventTypeOfCode 11 = some .DELETE_FILE_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]
  · rw [hc, show eventTypeOfCode 12 = some .NEW_LOAD_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]
  · rw [hc, show eventTypeOfCode 20 = some .PRE_GA_WRITE_ROWS_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]
  · rw [hc, show eventTypeOfCode 21 = some .PRE_GA_UPDATE_ROWS_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]
  · rw [hc, show eventTypeOfCode 22 = some .PRE_GA_DELETE_ROWS_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]
  · rw [hc, show eventTypeOfCode 28 = some .IGNORABLE_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]
  · rw [hc, show eventTypeOfCode 36 = some .TRANSACTION_CONTEXT_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]
  · rw [hc, show eventTypeOfCode 37 = some .VIEW_CHANGE_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]
  · rw [hc, show eventTypeOfCode 38 = some .XA_PREPARE_LOG_EVENT from rfl]
    simp [edUnitCodes, edTypeCode, edRaw, alloc.vec.Vec.deref, cowList]

/-- `read_data` for type code 2: `read_event::<QueryEvent>`, wrapped in `EventData::QueryEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code2 (self : binlog.events.Event) (h : self.header.event_type.1.val = 2) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.query_event.QueryEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.QueryEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 2 = some .QUERY_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 4: `read_event::<RotateEvent>`, wrapped in `EventData::RotateEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code4 (self : binlog.events.Event) (h : self.header.event_type.1.val = 4) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RotateEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 4 = some .ROTATE_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 5: `read_event::<IntvarEvent>`, wrapped in `EventData::IntvarEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code5 (self : binlog.events.Event) (h : self.header.event_type.1.val = 5) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.IntvarEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 5 = some .INTVAR_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 13: `read_event::<RandEvent>`, wrapped in `EventData::RandEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code13 (self : binlog.events.Event) (h : self.header.event_type.1.val = 13) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.rand_event.RandEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RandEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 13 = some .RAND_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 14: `read_event::<UserVarEvent>`, wrapped in `EventData::UserVarEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code14 (self : binlog.events.Event) (h : self.header.event_type.1.val = 14) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.user_var_event.UserVarEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.UserVarEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 14 = some .USER_VAR_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 16: `read_event::<XidEvent>`, wrapped in `EventData::XidEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code16 (self : binlog.events.Event) (h : self.header.event_type.1.val = 16) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.xid_event.XidEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.XidEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 16 = some .XID_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 17: `read_event::<BeginLoadQueryEvent>`, wrapped in `EventData::BeginLoadQueryEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code17 (self : binlog.events.Event) (h : self.header.event_type.1.val = 17) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.BeginLoadQueryEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 17 = some .BEGIN_LOAD_QUERY_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 18: `read_event::<ExecuteLoadQueryEvent>`, wrapped in `EventData::ExecuteLoadQueryEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code18 (self : binlog.events.Event) (h : self.header.event_type.1.val = 18) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.ExecuteLoadQueryEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 18 = some .EXECUTE_LOAD_QUERY_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 19: `read_event::<TableMapEvent>`, wrapped in `EventData::TableMapEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code19 (self : binlog.events.Event) (h : self.header.event_type.1.val = 19) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.TableMapEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 19 = some .TABLE_MAP_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 23: `read_event::<WriteRowsEventV1>`, wrapped in `EventData::RowsEvent`(`RowsEventData::WriteRowsEventV1`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code23 (self : binlog.events.Event) (h : self.header.event_type.1.val = 23) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.WriteRowsEventV1 x)))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 23 = some .WRITE_ROWS_EVENT_V1 := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 24: `read_event::<UpdateRowsEventV1>`, wrapped in `EventData::RowsEvent`(`RowsEventData::UpdateRowsEventV1`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code24 (self : binlog.events.Event) (h : self.header.event_type.1.val = 24) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.update_rows_event_v1.UpdateRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.UpdateRowsEventV1 x)))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 24 = some .UPDATE_ROWS_EVENT_V1 := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 25: `read_event::<DeleteRowsEventV1>`, wrapped in `EventData::RowsEvent`(`RowsEventData::DeleteRowsEventV1`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code25 (self : binlog.events.Event) (h : self.header.event_type.1.val = 25) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.DeleteRowsEventV1 x)))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 25 = some .DELETE_ROWS_EVENT_V1 := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 26: `read_event::<IncidentEvent>`, wrapped in `EventData::IncidentEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code26 (self : binlog.events.Event) (h : self.header.event_type.1.val = 26) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.IncidentEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 26 = some .INCIDENT_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 29: `read_event::<RowsQueryEvent>`, wrapped in `EventData::RowsQueryEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code29 (self : binlog.events.Event) (h : self.header.event_type.1.val = 29) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsQueryEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 29 = some .ROWS_QUERY_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 30: `read_event::<WriteRowsEvent>`, wrapped in `EventData::RowsEvent`(`RowsEventData::WriteRowsEvent`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code30 (self : binlog.events.Event) (h : self.header.event_type.1.val = 30) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.write_rows_event.WriteRowsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.WriteRowsEvent x)))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 30 = some .WRITE_ROWS_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 31: `read_event::<UpdateRowsEvent>`, wrapped in `EventData::RowsEvent`(`RowsEventData::UpdateRowsEvent`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code31 (self : binlog.events.Event) (h : self.header.event_type.1.val = 31) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.UpdateRowsEvent x)))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 31 = some .UPDATE_ROWS_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 32: `read_event::<DeleteRowsEvent>`, wrapped in `EventData::RowsEvent`(`RowsEventData::DeleteRowsEvent`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code32 (self : binlog.events.Event) (h : self.header.event_type.1.val = 32) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.delete_rows_event.DeleteRowsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.DeleteRowsEvent x)))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 32 = some .DELETE_ROWS_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 33: `read_event::<GtidEvent>`, wrapped in `EventData::GtidEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code33 (self : binlog.events.Event) (h : self.header.event_type.1.val = 33) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.GtidEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 33 = some .GTID_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 34: `read_event::<AnonymousGtidEvent>`, wrapped in `EventData::AnonymousGtidEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code34 (self : binlog.events.Event) (h : self.header.event_type.1.val = 34) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.AnonymousGtidEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 34 = some .ANONYMOUS_GTID_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 35: `read_event::<PreviousGtidsEvent>`, wrapped in `EventData::PreviousGtidsEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code35 (self : binlog.events.Event) (h : self.header.event_type.1.val = 35) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.PreviousGtidsEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 35 = some .PREVIOUS_GTIDS_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 39: `read_event::<PartialUpdateRowsEvent>`, wrapped in `EventData::RowsEvent`(`RowsEventData::PartialUpdateRowsEvent`) (its errors passed on). -/
theorem binlog.events.Event.read_data_code39 (self : binlog.events.Event) (h : self.header.event_type.1.val = 39) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.partial_update_rows_event.PartialUpdateRowsEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.RowsEvent (.PartialUpdateRowsEvent x)))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 39 = some .PARTIAL_UPDATE_ROWS_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 40: `read_event::<TransactionPayloadEvent>`, wrapped in `EventData::TransactionPayloadEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code40 (self : binlog.events.Event) (h : self.header.event_type.1.val = 40) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.TransactionPayloadEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 40 = some .TRANSACTION_PAYLOAD_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for type code 42: `read_event::<GtidEvent>`, wrapped in `EventData::GtidEvent` (its errors passed on). -/
theorem binlog.events.Event.read_data_code42 (self : binlog.events.Event) (h : self.header.event_type.1.val = 42) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.GtidEvent x))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 42 = some .GTID_TAGGED_LOG_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `read_data` for a `FORMAT_DESCRIPTION_EVENT` (15): `read_event::<FormatDescriptionEvent>`, with this event's footer (`with_footer`). -/
theorem binlog.events.Event.read_data_code15 (self : binlog.events.Event) (h : self.header.event_type.1.val = 15) :
    binlog.events.Event.read_data self = (do
      let r ← binlog.events.Event.read_event binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonBinlogBinlogEvent self
      ok (match r with
        | .Ok x => .Ok (some (.FormatDescriptionEvent { x with footer := self.footer }))
        | .Err err => .Err err)) := by
  have e : eventTypeOfCode 15 = some .FORMAT_DESCRIPTION_EVENT := rfl
  unfold binlog.events.Event.read_data
  rw [read_data_get, h, e]
  simp only [bind_ok]
  congr 1; funext r; cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, binlog.events.format_description_event.FormatDescriptionEvent.with_footer]

/-- `read_event::<T>` composed with a specification of `T`'s `parse`: a reader `spec` that
    consumes the whole data gives `Ok` with that view (and any extra property `P` of the parsed
    value); a failing `spec` gives an error. -/
private theorem read_event_wire {T V : Type} (inst : binlog.BinlogEvent T) (self : binlog.events.Event)
    (hlen : self.data.length + 19 ≤ Usize.max) (view : T → V) (spec : Option (V × List U8)) (P : T → Prop)
    (hrest : ∀ v t, spec = some (v, t) → t = [])
    (hdes : ∀ (ctx : binlog.BinlogCtx) (buf : io.ParseBuf), ctx.fde = self.fde →
      ctx.event_type_raw = self.header.event_type.1 → buf.val = self.data.val →
      io.ParseBuf.parse inst.BinlogStructInst.protoMyDeserializeASelfBinlogCtxInst buf ctx ⦃ r rest =>
        ReadsAs view spec r rest ∧ ∀ e, okPart r = some e → P e ⦄) :
    binlog.events.Event.read_event inst self ⦃ r =>
      (∀ v t, spec = some (v, t) → ∃ x, r = .Ok x ∧ view x = v ∧ P x) ∧ (spec = none → okPart r = none) ⦄ := by
  have hL : binlog.events.BinlogEventHeader.LEN = 19#usize := by unfold binlog.events.BinlogEventHeader.LEN; rfl
  obtain ⟨es, -, hesv⟩ := PBUtil.spec_eq_ok (show (binlog.events.BinlogEventHeader.LEN + alloc.vec.Vec.len self.data)
      ⦃ z => z.val = 19 + self.data.length ⦄ by rw [hL]; step*)
  let ctx : binlog.BinlogCtx := { event_size := es, fde := self.fde, event_type_raw := self.header.event_type.1 }
  obtain ⟨⟨r0, rest0⟩, hp, hq⟩ := PBUtil.spec_eq_ok (hdes ctx (alloc.vec.Vec.deref self.data) rfl rfl (by simp only [alloc.vec.Vec.deref, Slice.from_val]))
  rw [binlog.events.Event.read_event_spec inst self hlen ctx ⟨hesv, rfl, rfl⟩ (alloc.vec.Vec.deref self.data) (by simp only [alloc.vec.Vec.deref, Slice.from_val]) r0 rest0 hp]
  obtain ⟨hr, hP⟩ := hq
  cases hs : spec with
  | none =>
    rw [hs] at hr
    simp only [ReadsAs] at hr
    cases r0 with
    | Ok x => simp [okPart] at hr
    | Err e => exact (WP.spec_ok _).mpr ⟨fun _ _ h => by simp at h, fun _ => rfl⟩
  | some vt =>
    obtain ⟨v, t⟩ := vt
    rw [hs] at hr
    have ht := hrest v t hs
    simp only [ReadsAs] at hr
    obtain ⟨h1, h2⟩ := hr
    cases r0 with
    | Ok x =>
      simp only [okPart, Option.map_some, Option.some.injEq] at h1
      simp only [h2, ht, ite_true]
      refine (WP.spec_ok _).mpr ⟨fun v' t' h => ?_, fun h => by simp at h⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨x, rfl, h1, hP x rfl⟩
    | Err e => simp [okPart] at h1

/-- End to end: the `EventData` of a query event (2) is the `queryRead` of its data (the post-header length from the event's FDE); an error iff that fails. -/
theorem binlog.events.Event.read_data_query_wire (self : binlog.events.Event) (h : self.header.event_type.1.val = 2) (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match queryRead (postHeaderLen (fdeLens self.fde) .QUERY_EVENT) self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.QueryEvent x)) ∧ queryView x = v
      | none => okPart r = none ⦄ := by
  rw [binlog.events.Event.read_data_code2 self h]
  apply WP.spec_bind (read_event_wire _ self hlen queryView (queryRead (postHeaderLen (fdeLens self.fde) .QUERY_EVENT) self.data.val) (fun _ => True) (by
      intro v t ht; exact queryRead_tail _ _ v t ht)
    (fun ctx buf hf _ hb => by
      rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq])]
      apply WP.spec_mono (binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec ctx buf)
      rintro ⟨r, rest⟩ hr
      simp only [hb] at hr
      rw [hf] at hr
      exact ⟨hr, fun _ _ => trivial⟩))
  intro r ⟨hs, hn⟩
  cases hsp : (queryRead (postHeaderLen (fdeLens self.fde) .QUERY_EVENT) self.data.val) with
  | none =>
    have := hn hsp
    cases r with
    | Ok x => simp [okPart] at this
    | Err e => exact (WP.spec_ok _).mpr rfl
  | some vt =>
    obtain ⟨v, t⟩ := vt
    obtain ⟨x, rfl, hx, -⟩ := hs v t hsp
    exact (WP.spec_ok _).mpr ⟨x, rfl, hx⟩

/-- End to end: the `EventData` of a rotate event (4): `rotateRead` of its data. -/
theorem binlog.events.Event.read_data_rotate_wire (self : binlog.events.Event) (h : self.header.event_type.1.val = 4) (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match rotateRead self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.RotateEvent x)) ∧ rotateView x = v
      | none => okPart r = none ⦄ := by
  rw [binlog.events.Event.read_data_code4 self h]
  apply WP.spec_bind (read_event_wire _ self hlen rotateView (rotateRead self.data.val) (fun _ => True) (by
      intro v t ht; exact rotateRead_tail _ v t ht)
    (fun ctx buf hf _ hb => by
      rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq])]
      apply WP.spec_mono (binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec ctx buf)
      rintro ⟨r, rest⟩ hr
      simp only [hb] at hr
      exact ⟨hr, fun _ _ => trivial⟩))
  intro r ⟨hs, hn⟩
  cases hsp : (rotateRead self.data.val) with
  | none =>
    have := hn hsp
    cases r with
    | Ok x => simp [okPart] at this
    | Err e => exact (WP.spec_ok _).mpr rfl
  | some vt =>
    obtain ⟨v, t⟩ := vt
    obtain ⟨x, rfl, hx, -⟩ := hs v t hsp
    exact (WP.spec_ok _).mpr ⟨x, rfl, hx⟩

/-- End to end: the `EventData` of a format description event (15): `fdeRead` of its data, with the event's footer. -/
theorem binlog.events.Event.read_data_fde_wire (self : binlog.events.Event) (h : self.header.event_type.1.val = 15) (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match fdeRead self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.FormatDescriptionEvent x)) ∧ fdeView x = v ∧ x.footer = self.footer
      | none => okPart r = none ⦄ := by
  rw [binlog.events.Event.read_data_code15 self h]
  apply WP.spec_bind (read_event_wire _ self hlen fdeView (fdeRead self.data.val) (fun _ => True) (by
      intro v t ht; exact fdeRead_tail _ v t ht)
    (fun ctx buf hf _ hb => by
      rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq])]
      apply WP.spec_mono (binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec ctx buf)
      rintro ⟨r, rest⟩ ⟨hr, -⟩
      simp only [hb] at hr
      exact ⟨hr, fun _ _ => trivial⟩))
  intro r ⟨hs, hn⟩
  cases hsp : fdeRead self.data.val with
  | none =>
    have := hn hsp
    cases r with
    | Ok x => simp [okPart] at this
    | Err e => exact (WP.spec_ok _).mpr rfl
  | some vt =>
    obtain ⟨v, t⟩ := vt
    obtain ⟨x, rfl, hx, -⟩ := hs v t hsp
    exact (WP.spec_ok _).mpr ⟨_, rfl, hx, rfl⟩

/-- End to end: the `EventData` of a table map event (19): `tmRead` of its data. -/
theorem binlog.events.Event.read_data_table_map_wire (h64 : Target64) (self : binlog.events.Event) (h : self.header.event_type.1.val = 19) (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match tmRead (postHeaderLen (fdeLens self.fde) .TABLE_MAP_EVENT) self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.TableMapEvent x)) ∧ tmView x = v
      | none => okPart r = none ⦄ := by
  rw [binlog.events.Event.read_data_code19 self h]
  apply WP.spec_bind (read_event_wire _ self hlen tmView (tmRead (postHeaderLen (fdeLens self.fde) .TABLE_MAP_EVENT) self.data.val) (fun _ => True) (by
      intro v t ht; exact tmRead_tail _ _ v t ht)
    (fun ctx buf hf _ hb => by
      rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq])]
      apply WP.spec_mono (binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec h64 ctx buf)
      rintro ⟨r, rest⟩ hr
      simp only [hb] at hr
      rw [hf] at hr
      exact ⟨hr, fun _ _ => trivial⟩))
  intro r ⟨hs, hn⟩
  cases hsp : (tmRead (postHeaderLen (fdeLens self.fde) .TABLE_MAP_EVENT) self.data.val) with
  | none =>
    have := hn hsp
    cases r with
    | Ok x => simp [okPart] at this
    | Err e => exact (WP.spec_ok _).mpr rfl
  | some vt =>
    obtain ⟨v, t⟩ := vt
    obtain ⟨x, rfl, hx, -⟩ := hs v t hsp
    exact (WP.spec_ok _).mpr ⟨x, rfl, hx⟩

/-- End to end: the `EventData` of a rows event (23–25, 30–32, 39): the `RowsEventData` variant of its type, with `rowsRead` of its data (post-header lengths from the event's FDE). -/
theorem binlog.events.Event.read_data_rows_wire (h64 : Target64) (hsz : core.mem.size_of Std.U16 = ok 2#usize) (self : binlog.events.Event) (t : binlog.consts.EventType)
    (ht : eventTypeOfCode self.header.event_type.1.val = some t) (hr : eventTypeCode t ∈ [23, 24, 25, 30, 31, 32, 39])
    (hlen : self.data.length + 19 ≤ Usize.max) :
    binlog.events.Event.read_data self ⦃ r => match rowsRead t (postHeaderLen (fdeLens self.fde) t) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.RowsEvent x)) ∧ rowsVariantCode x = eventTypeCode t ∧ rowsView (rowsInner x) = v
      | none => okPart r = none ⦄ := by
  have hcode : eventTypeCode t = self.header.event_type.1.val := by
    unfold eventTypeOfCode at ht
    simpa using List.find?_some ht
  cases t <;> simp [eventTypeCode] at hr
  · have h : self.header.event_type.1.val = 23 := hcode.symm
    rw [binlog.events.Event.read_data_code23 self h]
    apply WP.spec_bind (read_event_wire _ self hlen rowsView
      (rowsRead .WRITE_ROWS_EVENT_V1 (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT_V1) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val)
      (fun _ => True) (by intro v t ht; exact rowsRead_tail _ _ _ _ v t ht)
      (fun ctx buf hf _ hb => by
        rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq])]
        apply WP.spec_mono (binlog.events.write_rows_event_v1.WriteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec h64 hsz ctx buf)
        rintro ⟨r, rest⟩ hr
        rw [hb, hf] at hr
        exact ⟨hr, fun _ _ => trivial⟩))
    intro r ⟨hs, hn⟩
    cases hsp : rowsRead .WRITE_ROWS_EVENT_V1 (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT_V1) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val with
    | none =>
      have := hn hsp
      cases r with
      | Ok x => simp [okPart] at this
      | Err e => exact (WP.spec_ok _).mpr rfl
    | some vt =>
      obtain ⟨v, t⟩ := vt
      obtain ⟨x, rfl, hx, -⟩ := hs v t hsp
      exact (WP.spec_ok _).mpr ⟨_, rfl, rfl, hx⟩
  · have h : self.header.event_type.1.val = 24 := hcode.symm
    rw [binlog.events.Event.read_data_code24 self h]
    apply WP.spec_bind (read_event_wire _ self hlen rowsView
      (rowsRead .UPDATE_ROWS_EVENT_V1 (postHeaderLen (fdeLens self.fde) .UPDATE_ROWS_EVENT_V1) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val)
      (fun _ => True) (by intro v t ht; exact rowsRead_tail _ _ _ _ v t ht)
      (fun ctx buf hf _ hb => by
        rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [binlog.events.update_rows_event_v1.UpdateRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq])]
        apply WP.spec_mono (binlog.events.update_rows_event_v1.UpdateRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec h64 hsz ctx buf)
        rintro ⟨r, rest⟩ hr
        rw [hb, hf] at hr
        exact ⟨hr, fun _ _ => trivial⟩))
    intro r ⟨hs, hn⟩
    cases hsp : rowsRead .UPDATE_ROWS_EVENT_V1 (postHeaderLen (fdeLens self.fde) .UPDATE_ROWS_EVENT_V1) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val with
    | none =>
      have := hn hsp
      cases r with
      | Ok x => simp [okPart] at this
      | Err e => exact (WP.spec_ok _).mpr rfl
    | some vt =>
      obtain ⟨v, t⟩ := vt
      obtain ⟨x, rfl, hx, -⟩ := hs v t hsp
      exact (WP.spec_ok _).mpr ⟨_, rfl, rfl, hx⟩
  · have h : self.header.event_type.1.val = 25 := hcode.symm
    rw [binlog.events.Event.read_data_code25 self h]
    apply WP.spec_bind (read_event_wire _ self hlen rowsView
      (rowsRead .DELETE_ROWS_EVENT_V1 (postHeaderLen (fdeLens self.fde) .DELETE_ROWS_EVENT_V1) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val)
      (fun _ => True) (by intro v t ht; exact rowsRead_tail _ _ _ _ v t ht)
      (fun ctx buf hf _ hb => by
        rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq])]
        apply WP.spec_mono (binlog.events.delete_rows_event_v1.DeleteRowsEventV1.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec h64 hsz ctx buf)
        rintro ⟨r, rest⟩ hr
        rw [hb, hf] at hr
        exact ⟨hr, fun _ _ => trivial⟩))
    intro r ⟨hs, hn⟩
    cases hsp : rowsRead .DELETE_ROWS_EVENT_V1 (postHeaderLen (fdeLens self.fde) .DELETE_ROWS_EVENT_V1) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val with
    | none =>
      have := hn hsp
      cases r with
      | Ok x => simp [okPart] at this
      | Err e => exact (WP.spec_ok _).mpr rfl
    | some vt =>
      obtain ⟨v, t⟩ := vt
      obtain ⟨x, rfl, hx, -⟩ := hs v t hsp
      exact (WP.spec_ok _).mpr ⟨_, rfl, rfl, hx⟩
  · have h : self.header.event_type.1.val = 30 := hcode.symm
    rw [binlog.events.Event.read_data_code30 self h]
    apply WP.spec_bind (read_event_wire _ self hlen rowsView
      (rowsRead .WRITE_ROWS_EVENT (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val)
      (fun _ => True) (by intro v t ht; exact rowsRead_tail _ _ _ _ v t ht)
      (fun ctx buf hf _ hb => by
        rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [binlog.events.write_rows_event.WriteRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq])]
        apply WP.spec_mono (binlog.events.write_rows_event.WriteRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec h64 hsz ctx buf)
        rintro ⟨r, rest⟩ hr
        rw [hb, hf] at hr
        exact ⟨hr, fun _ _ => trivial⟩))
    intro r ⟨hs, hn⟩
    cases hsp : rowsRead .WRITE_ROWS_EVENT (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val with
    | none =>
      have := hn hsp
      cases r with
      | Ok x => simp [okPart] at this
      | Err e => exact (WP.spec_ok _).mpr rfl
    | some vt =>
      obtain ⟨v, t⟩ := vt
      obtain ⟨x, rfl, hx, -⟩ := hs v t hsp
      exact (WP.spec_ok _).mpr ⟨_, rfl, rfl, hx⟩
  · have h : self.header.event_type.1.val = 31 := hcode.symm
    rw [binlog.events.Event.read_data_code31 self h]
    apply WP.spec_bind (read_event_wire _ self hlen rowsView
      (rowsRead .UPDATE_ROWS_EVENT (postHeaderLen (fdeLens self.fde) .UPDATE_ROWS_EVENT) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val)
      (fun _ => True) (by intro v t ht; exact rowsRead_tail _ _ _ _ v t ht)
      (fun ctx buf hf _ hb => by
        rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq])]
        apply WP.spec_mono (binlog.events.update_rows_event.UpdateRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec h64 hsz ctx buf)
        rintro ⟨r, rest⟩ hr
        rw [hb, hf] at hr
        exact ⟨hr, fun _ _ => trivial⟩))
    intro r ⟨hs, hn⟩
    cases hsp : rowsRead .UPDATE_ROWS_EVENT (postHeaderLen (fdeLens self.fde) .UPDATE_ROWS_EVENT) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val with
    | none =>
      have := hn hsp
      cases r with
      | Ok x => simp [okPart] at this
      | Err e => exact (WP.spec_ok _).mpr rfl
    | some vt =>
      obtain ⟨v, t⟩ := vt
      obtain ⟨x, rfl, hx, -⟩ := hs v t hsp
      exact (WP.spec_ok _).mpr ⟨_, rfl, rfl, hx⟩
  · have h : self.header.event_type.1.val = 32 := hcode.symm
    rw [binlog.events.Event.read_data_code32 self h]
    apply WP.spec_bind (read_event_wire _ self hlen rowsView
      (rowsRead .DELETE_ROWS_EVENT (postHeaderLen (fdeLens self.fde) .DELETE_ROWS_EVENT) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val)
      (fun _ => True) (by intro v t ht; exact rowsRead_tail _ _ _ _ v t ht)
      (fun ctx buf hf _ hb => by
        rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [binlog.events.delete_rows_event.DeleteRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq])]
        apply WP.spec_mono (binlog.events.delete_rows_event.DeleteRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec h64 hsz ctx buf)
        rintro ⟨r, rest⟩ hr
        rw [hb, hf] at hr
        exact ⟨hr, fun _ _ => trivial⟩))
    intro r ⟨hs, hn⟩
    cases hsp : rowsRead .DELETE_ROWS_EVENT (postHeaderLen (fdeLens self.fde) .DELETE_ROWS_EVENT) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val with
    | none =>
      have := hn hsp
      cases r with
      | Ok x => simp [okPart] at this
      | Err e => exact (WP.spec_ok _).mpr rfl
    | some vt =>
      obtain ⟨v, t⟩ := vt
      obtain ⟨x, rfl, hx, -⟩ := hs v t hsp
      exact (WP.spec_ok _).mpr ⟨_, rfl, rfl, hx⟩
  · have h : self.header.event_type.1.val = 39 := hcode.symm
    rw [binlog.events.Event.read_data_code39 self h]
    apply WP.spec_bind (read_event_wire _ self hlen rowsView
      (rowsRead .PARTIAL_UPDATE_ROWS_EVENT (postHeaderLen (fdeLens self.fde) .PARTIAL_UPDATE_ROWS_EVENT) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val)
      (fun _ => True) (by intro v t ht; exact rowsRead_tail _ _ _ _ v t ht)
      (fun ctx buf hf _ hb => by
        rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [binlog.events.partial_update_rows_event.PartialUpdateRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq])]
        apply WP.spec_mono (binlog.events.partial_update_rows_event.PartialUpdateRowsEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_spec h64 hsz ctx buf)
        rintro ⟨r, rest⟩ hr
        rw [hb, hf] at hr
        exact ⟨hr, fun _ _ => trivial⟩))
    intro r ⟨hs, hn⟩
    cases hsp : rowsRead .PARTIAL_UPDATE_ROWS_EVENT (postHeaderLen (fdeLens self.fde) .PARTIAL_UPDATE_ROWS_EVENT) (postHeaderLen (fdeLens self.fde) .WRITE_ROWS_EVENT) self.data.val with
    | none =>
      have := hn hsp
      cases r with
      | Ok x => simp [okPart] at this
      | Err e => exact (WP.spec_ok _).mpr rfl
    | some vt =>
      obtain ⟨v, t⟩ := vt
      obtain ⟨x, rfl, hx, -⟩ := hs v t hsp
      exact (WP.spec_ok _).mpr ⟨_, rfl, rfl, hx⟩

/-- End to end: the `EventData` of a GTID event (33) whose data the untagged GTID reader consumes entirely: `gtidRead`; an error iff that fails. -/
theorem binlog.events.Event.read_data_gtid_wire (self : binlog.events.Event) (h : self.header.event_type.1.val = 33) (hlen : self.data.length + 19 ≤ Usize.max)
    (hg : ∀ v b bs, gtidRead self.data.val ≠ some (v, b :: bs)) :
    binlog.events.Event.read_data self ⦃ r => match gtidRead self.data.val with
      | some (v, _) => ∃ x, r = .Ok (some (.GtidEvent x)) ∧ gtidView x = v ∧ x.tag = none
      | none => okPart r = none ⦄ := by
  rw [binlog.events.Event.read_data_code33 self h]
  apply WP.spec_bind (read_event_wire _ self hlen gtidView (gtidRead self.data.val) (fun e => e.tag = none) (by
      intro v t ht
      cases t with
      | nil => rfl
      | cons b bs => exact absurd ht (hg v b bs))
    (fun ctx buf _ he hb => by
      rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq])]
      apply WP.spec_mono (binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_untagged ctx (Or.inl (by rw [he, h])) buf)
      rintro ⟨r, rest⟩ ⟨hr, hP⟩
      simp only [hb] at hr
      exact ⟨hr, fun e he => (hP e he).1⟩))
  intro r ⟨hs, hn⟩
  cases hsp : gtidRead self.data.val with
  | none =>
    have := hn hsp
    cases r with
    | Ok x => simp [okPart] at this
    | Err e => exact (WP.spec_ok _).mpr rfl
  | some vt =>
    obtain ⟨v, t⟩ := vt
    obtain ⟨x, rfl, hx, hP⟩ := hs v t hsp
    exact (WP.spec_ok _).mpr ⟨x, rfl, hx, hP⟩

/-- A GTID event (33) whose data has bytes after what the GTID reader reads (e.g. MySQL 8.0.33+'s `commit_group_ticket`): `read_data` is the (opaque) bytes-remaining error. -/
theorem binlog.events.Event.read_data_gtid_leftover (self : binlog.events.Event) (h : self.header.event_type.1.val = 33) (hlen : self.data.length + 19 ≤ Usize.max)
    (v : GtidView) (b : U8) (bs : List U8) (hg : gtidRead self.data.val = some (v, b :: bs)) :
    binlog.events.Event.read_data self = (do
      let e ← binlog.trusted.bytes_remaining_error binlog.events.gtid_event.GtidEvent
      ok (.Err e)) := by
  have hL : binlog.events.BinlogEventHeader.LEN = 19#usize := by unfold binlog.events.BinlogEventHeader.LEN; rfl
  obtain ⟨es, -, hesv⟩ := PBUtil.spec_eq_ok (show (binlog.events.BinlogEventHeader.LEN + alloc.vec.Vec.len self.data)
      ⦃ z => z.val = 19 + self.data.length ⦄ by rw [hL]; step*)
  let ctx : binlog.BinlogCtx := { event_size := es, fde := self.fde, event_type_raw := self.header.event_type.1 }
  have hbv : (alloc.vec.Vec.deref self.data).val = self.data.val := by simp only [alloc.vec.Vec.deref, Slice.from_val]
  have hpar : io.ParseBuf.parse binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent.BinlogStructInst.protoMyDeserializeASelfBinlogCtxInst
      (alloc.vec.Vec.deref self.data) ctx ⦃ r rest => ReadsAs gtidView (gtidRead self.data.val) r rest ⦄ := by
    rw [io.ParseBuf.parse_of_size_none _ _ _ (by simp [binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq])]
    apply WP.spec_mono (binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_untagged ctx (Or.inl h) _)
    rintro ⟨r, rest⟩ ⟨hr, -⟩
    rwa [hbv] at hr
  obtain ⟨⟨r0, rest0⟩, hp, hr⟩ := PBUtil.spec_eq_ok hpar
  rw [hg] at hr
  simp only [ReadsAs] at hr
  obtain ⟨h1, h2⟩ := hr
  cases r0 with
  | Err e => simp [okPart] at h1
  | Ok x =>
    rw [binlog.events.Event.read_data_code33 self h,
      binlog.events.Event.read_event_spec _ self hlen ctx ⟨hesv, rfl, rfl⟩ (alloc.vec.Vec.deref self.data) hbv _ rest0 hp]
    simp [h2]

end mysql_common
