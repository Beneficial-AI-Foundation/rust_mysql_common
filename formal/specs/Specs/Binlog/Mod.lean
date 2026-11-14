import Proofs.Binlog.Mod.BinlogCtx

/-!
# `src/binlog/mod.rs`
    `BinlogCtx::new`, the deserialization context of binlog events.

    **Configuration.** As in `Specs/Io.lean`, with the feature `binlog_core` of the patched copy
    (formal/trusted/patches/140; see `formal/docs/STATUS.md`).

    **Definitions used.** None.

    **Trusted axioms.** None (the context holds a `FormatDescriptionEvent`, whose type is
    translated).

    **Not covered.** `BinlogFileHeader` (`read`/`write` use `std::io::Read`/`Write`), the
    `BinlogStruct`/`BinlogEvent` traits (no code; their impls are in the events half),
    `BinlogEventHeader`-level reading (events half).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct BinlogCtx and its impls` -/

/-- `BinlogCtx::new(event_size, fde, event_type_raw)`: the context with these fields. -/
recall binlog.BinlogCtx.new_eq (event_size : Usize)
    (fde : binlog.events.format_description_event.FormatDescriptionEvent) (event_type_raw : U8) :
    binlog.BinlogCtx.new event_size fde event_type_raw = ok { event_size, fde, event_type_raw }

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms binlog.BinlogCtx.new_eq
end mysql_common
