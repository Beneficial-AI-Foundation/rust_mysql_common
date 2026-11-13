import Defs

/-! Statements for `struct StatusVar and its impls` (spec file: `Specs/Binlog/Events/QueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `get_value`: the value decoded per its key (`svValRead`); the raw value as the error if it is too short. (`Q_UPDATED_DB_NAMES` and `Q_MICROSECONDS`: see below.) -/
theorem binlog.events.query_event.StatusVar.get_value_spec (v : binlog.events.query_event.StatusVar) (hk : svKeyCode v.key ≠ 12 ∧ svKeyCode v.key ≠ 13) :
    binlog.events.query_event.StatusVar.get_value v ⦃ r => match r with
      | .Ok x => svValRead (svKeyCode v.key) v.value.val = some (svValView x)
      | .Err e => svValRead (svKeyCode v.key) v.value.val = none ∧ e = v.value ⦄ := by
  sorry

/-- **Upstream bug:** `get_value` of `Q_UPDATED_DB_NAMES` gives `dbNamesCrate` (the first name, then empty names), not the names of the format (`dbNames`); the raw value as the error without a count or a terminated first name. -/
theorem binlog.events.query_event.StatusVar.get_value_updated_db_names (v : binlog.events.query_event.StatusVar) (hk : svKeyCode v.key = 12) :
    binlog.events.query_event.StatusVar.get_value v ⦃ r => match v.value.val with
      | [] => r = .Err v.value
      | c :: rest => match dbNamesCrate c.val rest with
        | some ns => ∃ x, r = .Ok x ∧ svValView x = (12, [], ns)
        | none => r = .Err v.value ⦄ := by
  sorry

/-- `get_value` of `Q_MICROSECONDS` reads a 4-byte integer (the format has 3). -/
theorem binlog.events.query_event.StatusVar.get_value_microseconds (v : binlog.events.query_event.StatusVar) (hk : svKeyCode v.key = 13) :
    binlog.events.query_event.StatusVar.get_value v ⦃ r => if 4 ≤ v.value.length then ∃ x, r = .Ok x ∧ svValView x = (13, [leNat (v.value.val.take 4)], [])
      else r = .Err v.value ⦄ := by
  sorry

/-- **Upstream bug:** every `Q_MICROSECONDS` variable the iterator yields (3 bytes) fails to decode. -/
theorem binlog.events.query_event.StatusVar.get_value_microseconds_bug (v : binlog.events.query_event.StatusVar) (hk : svKeyCode v.key = 13) (hl : v.value.length = 3) :
    binlog.events.query_event.StatusVar.get_value v = ok (.Err v.value) := by
  sorry

end mysql_common
