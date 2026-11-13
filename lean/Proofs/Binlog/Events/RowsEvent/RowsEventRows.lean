import Defs

/-! Statements for `struct RowsEventRows and its impls` (spec file: `Specs/Binlog/Events/RowsEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new` (crate-private constructor). -/
theorem binlog.events.rows_event.RowsEventRows.new_eq (e : binlog.events.rows_event.RowsEvent) (tme : binlog.events.table_map_event.TableMapEvent) (d : io.ParseBuf) :
    binlog.events.rows_event.RowsEventRows.new e tme d = ok { rows_event := e, table_map_event := tme, rows_data := d } := by
  sorry

end mysql_common
