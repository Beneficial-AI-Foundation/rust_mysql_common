import Defs

/-! Statements for `struct BinlogCtx and its impls` (spec file: `Specs/Binlog/Mod.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `BinlogCtx::new(event_size, fde, event_type_raw)`: the context with these fields. -/
theorem binlog.BinlogCtx.new_eq (event_size : Usize)
    (fde : binlog.events.format_description_event.FormatDescriptionEvent) (event_type_raw : U8) :
    binlog.BinlogCtx.new event_size fde event_type_raw = ok { event_size, fde, event_type_raw } := by
  sorry

end mysql_common
