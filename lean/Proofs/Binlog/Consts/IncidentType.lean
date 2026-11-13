import Defs

/-! Statements for `enum IncidentType and its impls` (spec file: `Specs/Binlog/Consts.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `TryFrom<u16> for IncidentType`: total; `INCIDENT_NONE` (0), `INCIDENT_LOST_EVENTS` (1), else the number back as the error. -/
theorem binlog.consts.IncidentType.Insts.CoreConvertTryFromU16UnknownIncidentType.try_from_spec (value : U16) :
    binlog.consts.IncidentType.Insts.CoreConvertTryFromU16UnknownIncidentType.try_from value =
      ok (match incidentTypeOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  sorry

end mysql_common
