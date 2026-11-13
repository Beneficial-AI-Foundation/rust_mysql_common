import Defs

/-! Statements for `struct StatusVarsIterator and its impls` (spec file: `Specs/Binlog/Events/QueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new(bytes)`: at position 0. -/
theorem binlog.events.query_event.StatusVarsIterator.new_spec (s : Slice U8) :
    binlog.events.query_event.StatusVarsIterator.new s = ok { pos := 0#usize, status_vars := s } := by
  rfl

/-- `Iterator::next`: the next variable of the walk from the current position (`svStep`; nothing at or past the end), and the position after it; `None` at an unknown key, a truncated value, or the end (the position after a `None` is not stated: the iterator is not fused). -/
theorem binlog.events.query_event.StatusVarsIterator.Insts.CoreIterTraitsIteratorIteratorStatusVar.next_spec (it : binlog.events.query_event.StatusVarsIterator) :
    binlog.events.query_event.StatusVarsIterator.Insts.CoreIterTraitsIteratorIteratorStatusVar.next it ⦃ o it' =>
      match svStep it.status_vars.val it.pos.val with
      | some (kv, p) => o.map (fun x => (statusVarKeyCode x.key, x.value.val)) = some kv ∧ it'.pos.val = p ∧ it'.status_vars = it.status_vars
      | none => o = none ∧ it'.status_vars = it.status_vars ⦄ := by
  sorry

end mysql_common
