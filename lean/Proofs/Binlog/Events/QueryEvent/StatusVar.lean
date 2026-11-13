import Defs
import Proofs.Util.BinlogEvHdr
import Proofs.Util.PacketsOkErr
import Proofs.Io.ParseBuf

/-! Statements for `struct StatusVar and its impls` (spec file: `Specs/Binlog/Events/QueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.EvHdrUtil

namespace mysql_common

/-- `get_value`: the value decoded per its key (`svValRead`); the raw value as the error if it is too short. (`Q_UPDATED_DB_NAMES` and `Q_MICROSECONDS`: see below.) -/
theorem binlog.events.query_event.StatusVar.get_value_spec (v : binlog.events.query_event.StatusVar) (hk : statusVarKeyCode v.key ≠ 12 ∧ statusVarKeyCode v.key ≠ 13) :
    binlog.events.query_event.StatusVar.get_value v ⦃ r => match r with
      | .Ok x => svValRead (statusVarKeyCode v.key) v.value.val = some (svValView x)
      | .Err e => svValRead (statusVarKeyCode v.key) v.value.val = none ∧ e = v.value ⦄ := by
  sorry

/-- **Upstream bug:** `get_value` of `Q_UPDATED_DB_NAMES` gives `dbNamesCrate` (the first name, then empty names), not the names of the format (`dbNames`); the raw value as the error without a count or a terminated first name. -/
theorem binlog.events.query_event.StatusVar.get_value_updated_db_names (v : binlog.events.query_event.StatusVar) (hk : statusVarKeyCode v.key = 12) :
    binlog.events.query_event.StatusVar.get_value v ⦃ r => match v.value.val with
      | [] => r = .Err v.value
      | c :: rest => match dbNamesCrate c.val rest with
        | some ns => ∃ x, r = .Ok x ∧ svValView x = (12, [], ns)
        | none => r = .Err v.value ⦄ := by
  sorry

/-- `get_value` of `Q_MICROSECONDS` reads a 4-byte integer (the format has 3). -/
theorem binlog.events.query_event.StatusVar.get_value_microseconds (v : binlog.events.query_event.StatusVar) (hk : statusVarKeyCode v.key = 13) :
    binlog.events.query_event.StatusVar.get_value v ⦃ r => if 4 ≤ v.value.length then ∃ x, r = .Ok x ∧ svValView x = (13, [leNat (v.value.val.take 4)], [])
      else r = .Err v.value ⦄ := by
  obtain ⟨k, val⟩ := v
  cases k <;> simp only [statusVarKeyCode] at hk <;> try omega
  unfold binlog.events.query_event.StatusVar.get_value
  step with io.ParseBuf.checked_eat_u32_le_spec as ⟨o, rest, ho⟩
  split_ifs at ho ⊢ with hl
  · obtain ⟨h1, -⟩ := ho
    cases o with
    | none => simp at h1
    | some x =>
      simp only [Option.map_some, Option.some.injEq] at h1
      exact (WP.spec_ok _).mpr ⟨_, rfl, by simp [svValView, h1]⟩
  · obtain ⟨rfl, -⟩ := ho
    exact (WP.spec_ok _).mpr rfl

/-- **Upstream bug:** every `Q_MICROSECONDS` variable the iterator yields (3 bytes) fails to decode. -/
theorem binlog.events.query_event.StatusVar.get_value_microseconds_bug (v : binlog.events.query_event.StatusVar) (hk : statusVarKeyCode v.key = 13) (hl : v.value.length = 3) :
    binlog.events.query_event.StatusVar.get_value v = ok (.Err v.value) := by
  have h := binlog.events.query_event.StatusVar.get_value_microseconds v hk
  have hl' : ¬ 4 ≤ v.value.length := by omega
  simp only [hl', ite_false] at h
  obtain ⟨r, hr, hp⟩ := PBUtil.spec_eq_ok h
  rw [hr, hp]

end mysql_common
