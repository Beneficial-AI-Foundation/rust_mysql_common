import Defs
import Proofs.Util.BinlogEvGtid

/-! Statements for `struct PreviousGtidsSid and its impls` (spec file: `Specs/Binlog/Events/PreviousGtidsEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

/-- `new(uuid, tag, intervals)`. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsSid.new_eq (u : Array U8 16#usize) (t : Option packets.Tag) (is : alloc.vec.Vec packets.GnoInterval) :
    binlog.events.previous_gtids_event.PreviousGtidsSid.new u t is = ok { uuid := u, tag := t, intervals := is } := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsSid.new; rfl

/-- `uuid`. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsSid.impl.uuid_eq (s : binlog.events.previous_gtids_event.PreviousGtidsSid) :
    binlog.events.previous_gtids_event.PreviousGtidsSid.impl.uuid s = ok s.uuid := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsSid.impl.uuid; rfl

/-- `tag`. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsSid.impl.tag_eq (s : binlog.events.previous_gtids_event.PreviousGtidsSid) :
    binlog.events.previous_gtids_event.PreviousGtidsSid.impl.tag s = ok s.tag := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsSid.impl.tag; rfl

/-- `intervals`. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsSid.impl.intervals_spec (x : binlog.events.previous_gtids_event.PreviousGtidsSid) :
    binlog.events.previous_gtids_event.PreviousGtidsSid.impl.intervals x ⦃ s => s.val = x.intervals.val ⦄ := by
  simp [binlog.events.previous_gtids_event.PreviousGtidsSid.impl.intervals, alloc.vec.Vec.deref]

/-- `into_owned` of an untagged SID: the same UUID and intervals. -/
theorem binlog.events.previous_gtids_event.PreviousGtidsSid.into_owned_spec (s : binlog.events.previous_gtids_event.PreviousGtidsSid) (ht : s.tag = none) :
    binlog.events.previous_gtids_event.PreviousGtidsSid.into_owned s ⦃ s' => pgSidView s' = pgSidView s ∧ s'.tag = none ⦄ := by
  unfold binlog.events.previous_gtids_event.PreviousGtidsSid.into_owned; step*

end mysql_common
