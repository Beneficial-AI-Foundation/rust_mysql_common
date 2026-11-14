import Defs
import Proofs.Util.BinlogConsts

/-! Statements for `enum EventType and its impls` (spec file: `Specs/Binlog/Consts.lean`). Helper lemmas: `Proofs/Util/BinlogConsts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.BinlogConstsUtil

namespace mysql_common

/-- `TryFrom<u8> for EventType`: total; the event type with that code (`Log_event_type`), or the byte back as the error. Unknown: `0x29` (MySQL's `HEARTBEAT_LOG_EVENT_V2`) and `0x2b`–`0xff` (in particular `ENUM_END_EVENT`, MySQL's end marker, is never returned). -/
theorem binlog.consts.EventType.Insts.CoreConvertTryFromU8UnknownEventType.try_from_spec (value : U8) :
    binlog.consts.EventType.Insts.CoreConvertTryFromU8UnknownEventType.try_from value =
      ok (match eventTypeOfCode value.val with
        | some x => .Ok x
        | none => .Err value) := by
  obtain ⟨⟨⟨n, hn⟩⟩⟩ := value
  change n < 256 at hn
  have h := hn
  repeat (obtain h | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h); swap; · rfl)
  exact absurd h (Nat.not_lt_zero _)

end mysql_common
