import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Binlog.Events.Mod.RowsEventData
import Proofs.Binlog.Events.QueryEvent.QueryEvent
import Proofs.Binlog.Events.RotateEvent.RotateEvent
import Proofs.Binlog.Events.FormatDescriptionEvent.FormatDescriptionEvent
import Proofs.Binlog.Events.BeginLoadQueryEvent.BeginLoadQueryEvent
import Proofs.Binlog.Events.ExecuteLoadQueryEvent.ExecuteLoadQueryEvent
import Proofs.Binlog.Events.TableMapEvent.TableMapEvent
import Proofs.Binlog.Events.IncidentEvent.IncidentEvent
import Proofs.Binlog.Events.RowsQueryEvent.RowsQueryEvent
import Proofs.Binlog.Events.TransactionPayloadEvent.TransactionPayloadEvent

/-! Statements for `enum EventData and its impls` (spec file: `Specs/Binlog/Events.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

private theorem cow_into_owned_spec (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    alloc.borrow.Cow.into_owned (Slice.Insts.AllocBorrowToOwnedVec core.clone.CloneU8) c ⦃ v => v.val = cowList c ⦄ := by
  cases c with
  | Borrowed s =>
    simp only [alloc.borrow.Cow.into_owned, Slice.Insts.AllocBorrowToOwnedVec.to_owned]
    apply WP.spec_mono (alloc.slice.Slice.to_vec_spec _ s (by simp))
    intro v hv; simp [cowList, hv, alloc.vec.Vec.val]
  | Owned v => simp [alloc.borrow.Cow.into_owned, cowList]

private theorem sid_into_owned_ok (sd : binlog.events.previous_gtids_event.PreviousGtidsSid) :
    binlog.events.previous_gtids_event.PreviousGtidsSid.into_owned sd ⦃ _ => True ⦄ := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsSid.into_owned
  cases sd.tag <;> simp [binlog.trusted.tag_into_owned]

private theorem sids_into_owned_ok : ∀ (n : Nat) (v : alloc.vec.Vec binlog.events.previous_gtids_event.PreviousGtidsSid),
    v.val.length = n → binlog.events.previous_gtids_event.sids_into_owned v ⦃ w => w.val.length = n ⦄ := by
  intro n
  induction n with
  | zero =>
    intro v hv
    unfold binlog.events.previous_gtids_event.sids_into_owned
    have : v.val = [] := List.length_eq_zero_iff.mp hv
    simp [alloc.vec.Vec.pop, this, alloc.vec.Vec.new]
  | succ n ih =>
    intro v hv
    unfold binlog.events.previous_gtids_event.sids_into_owned
    obtain ⟨l, x, hlx⟩ : ∃ l x, v.val = l ++ [x] := by
      have hne : v.val ≠ [] := fun h => by simp [h] at hv
      exact ⟨v.val.dropLast, v.val.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    have hl : l.length = n := by rw [hlx] at hv; simpa using hv
    simp only [alloc.vec.Vec.pop, hlx, List.getLast?_append, List.getLast?_singleton, Option.some_or, bind_ok,
      List.dropLast_concat]
    apply WP.spec_bind (ih _ (by rw [alloc.vec.Vec.from_val]; exact hl))
    intro owned ho
    apply WP.spec_bind (sid_into_owned_ok x)
    intro x' _
    have hb : owned.val.length < Usize.max := by
      have := v.property; rw [hlx] at this; simp at this; omega
    apply WP.spec_mono (alloc.vec.Vec.push_spec owned x' hb)
    intro w hw; simp [hw, ho]

/-- `into_owned`: the same variant (type code), and the same raw data for the uninterpreted variants. -/
theorem binlog.events.EventData.into_owned_spec (d : binlog.events.EventData) :
    binlog.events.EventData.into_owned d ⦃ d' => edTypeCode d' = edTypeCode d ∧ edRaw d' = edRaw d ∧ edUnit d' = edUnit d ⦄ := by
  cases d with
  | UnknownEvent => simp [binlog.events.EventData.into_owned, edTypeCode, edRaw, edUnit]
  | StartEventV3 c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | QueryEvent x =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (binlog.events.query_event.QueryEvent.into_owned_spec x) (fun _ _ => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit]))
  | StopEvent => simp [binlog.events.EventData.into_owned, edTypeCode, edRaw, edUnit]
  | RotateEvent x =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (binlog.events.rotate_event.RotateEvent.into_owned_spec x) (fun _ _ => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit]))
  | IntvarEvent _ => simp [binlog.events.EventData.into_owned, edTypeCode, edRaw, edUnit]
  | LoadEvent c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | SlaveEvent => simp [binlog.events.EventData.into_owned, edTypeCode, edRaw, edUnit]
  | CreateFileEvent c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | AppendBlockEvent c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | ExecLoadEvent c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | DeleteFileEvent c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | NewLoadEvent c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | RandEvent _ => simp [binlog.events.EventData.into_owned, edTypeCode, edRaw, edUnit]
  | UserVarEvent x => simp [binlog.events.EventData.into_owned, binlog.events.user_var_event.UserVarEvent.into_owned, edTypeCode, edRaw, edUnit]
  | FormatDescriptionEvent x =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (binlog.events.format_description_event.FormatDescriptionEvent.into_owned_spec x) (fun _ _ => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit]))
  | XidEvent _ => simp [binlog.events.EventData.into_owned, edTypeCode, edRaw, edUnit]
  | BeginLoadQueryEvent x =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (binlog.events.begin_load_query_event.BeginLoadQueryEvent.into_owned_spec x) (fun _ _ => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit]))
  | ExecuteLoadQueryEvent x =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.into_owned_spec x) (fun _ _ => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit]))
  | TableMapEvent x =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (binlog.events.table_map_event.TableMapEvent.into_owned_spec x) (fun _ _ => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit]))
  | PreGaWriteRowsEvent c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | PreGaUpdateRowsEvent c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | PreGaDeleteRowsEvent c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | IncidentEvent x =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (binlog.events.incident_event.IncidentEvent.into_owned_spec x) (fun _ _ => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit]))
  | HeartbeatEvent => simp [binlog.events.EventData.into_owned, edTypeCode, edRaw, edUnit]
  | IgnorableEvent c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | RowsQueryEvent x =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (binlog.events.rows_query_event.RowsQueryEvent.into_owned_spec x) (fun _ _ => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit]))
  | GtidEvent _ => simp [binlog.events.EventData.into_owned, edTypeCode, edRaw, edUnit]
  | AnonymousGtidEvent _ => simp [binlog.events.EventData.into_owned, edTypeCode, edRaw, edUnit]
  | PreviousGtidsEvent x =>
    simp only [binlog.events.EventData.into_owned]
    have hp : binlog.events.previous_gtids_event.PreviousGtidsEvent.into_owned x ⦃ _ => True ⦄ := by
      unfold binlog.events.previous_gtids_event.PreviousGtidsEvent.into_owned
      exact WP.spec_bind (sids_into_owned_ok _ x.sids rfl) (fun _ _ => (WP.spec_ok _).mpr trivial)
    exact WP.spec_bind hp (fun _ _ => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit]))
  | TransactionContextEvent c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | ViewChangeEvent c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | XaPrepareLogEvent c =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (cow_into_owned_spec c) (fun v hv => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit, cowList, hv]))
  | RowsEvent r =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (binlog.events.RowsEventData.into_owned_spec r) (fun r' hr => (WP.spec_ok _).mpr (by
      have := congrArg RowsView.typeCode hr.2
      simp only [rowsView] at this
      simp [edTypeCode, edRaw, edUnit, this]))
  | TransactionPayloadEvent x =>
    simp only [binlog.events.EventData.into_owned]
    exact WP.spec_bind (binlog.events.transaction_payload_event.TransactionPayloadEvent.into_owned_spec x) (fun _ _ => (WP.spec_ok _).mpr (by simp [edTypeCode, edRaw, edUnit]))

/-- `MySerialize` of a data-less variant: writes nothing. -/
theorem binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize_unit (d : binlog.events.EventData) (h : edUnit d = true) (buf : alloc.vec.Vec U8) :
    binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize d buf = ok buf := by
  cases d <;> simp [edUnit] at h <;> rfl

/-- `MySerialize` of an uninterpreted variant: appends its raw data. -/
theorem binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize_raw (d : binlog.events.EventData) (bs : List U8) (h : edRaw d = some bs) (buf : alloc.vec.Vec U8) (hb : buf.length + bs.length ≤ Usize.max) :
    binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize d buf ⦃ buf' => buf'.val = buf.val ++ bs ⦄ := by
  cases d <;> simp only [edRaw, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp only [binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize] <;>
    exact WP.spec_bind (cow_deref_spec _ _) (fun s hs => by
      apply WP.spec_mono (IntAndMisc.put_slice_spec buf s (by simp [Slice.length, hs]; omega))
      intro b hb; rw [hb, hs])

/-- `MySerialize` of a parsed variant: the event's own `serialize`. -/
theorem binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize_parsed (buf : alloc.vec.Vec U8) :
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.QueryEvent x) buf = binlog.events.query_event.QueryEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.RotateEvent x) buf = binlog.events.rotate_event.RotateEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.IntvarEvent x) buf = binlog.events.intvar_event.IntvarEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.RandEvent x) buf = binlog.events.rand_event.RandEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.UserVarEvent x) buf = binlog.events.user_var_event.UserVarEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.FormatDescriptionEvent x) buf = binlog.events.format_description_event.FormatDescriptionEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.XidEvent x) buf = binlog.events.xid_event.XidEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.BeginLoadQueryEvent x) buf = binlog.events.begin_load_query_event.BeginLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.ExecuteLoadQueryEvent x) buf = binlog.events.execute_load_query_event.ExecuteLoadQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.TableMapEvent x) buf = binlog.events.table_map_event.TableMapEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.IncidentEvent x) buf = binlog.events.incident_event.IncidentEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.RowsQueryEvent x) buf = binlog.events.rows_query_event.RowsQueryEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.GtidEvent x) buf = binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.AnonymousGtidEvent x) buf = binlog.events.anonymous_gtid_event.AnonymousGtidEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.PreviousGtidsEvent x) buf = binlog.events.previous_gtids_event.PreviousGtidsEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.TransactionPayloadEvent x) buf = binlog.events.transaction_payload_event.TransactionPayloadEvent.Insts.Mysql_commonProtoMySerialize.serialize x buf) ∧
    (∀ x, binlog.events.EventData.Insts.Mysql_commonProtoMySerialize.serialize (.RowsEvent x) buf = binlog.events.RowsEventData.Insts.Mysql_commonProtoMySerialize.serialize x buf) := by
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

end mysql_common
