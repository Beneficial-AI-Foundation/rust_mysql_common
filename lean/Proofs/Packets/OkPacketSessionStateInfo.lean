import Defs

/-! Statements for `OkPacket::session_state_info` (spec file: `Specs/Packets/StmtBinlog.lean`).
Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `OkPacket::session_state_info`: total; no entries without session state, otherwise the
    entries of the session state string read until it is exhausted (`ssInfos`), an error if one
    is malformed. -/
theorem packets.OkPacket.impl.session_state_info_spec (h64 : Target64) (self : packets.OkPacket) :
    packets.OkPacket.impl.session_state_info self ⦃ r =>
      (okPart r).map (fun v => v.val.map SsInfo.of) =
        match self.session_state_info with
        | none => some []
        | some rb => ssInfos (cowList rb.1) ⦄ := by
  sorry

end mysql_common
