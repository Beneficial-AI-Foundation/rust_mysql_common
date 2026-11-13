import Defs

/-! Statements for `struct StatusVars and its impls` (spec file: `Specs/Binlog/Events/QueryEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `iter`: an iterator at position 0 over the block (its first 65535 bytes). -/
theorem binlog.events.query_event.StatusVars.iter_spec (s : binlog.events.query_event.StatusVars) :
    binlog.events.query_event.StatusVars.iter s ⦃ it => it.pos.val = 0 ∧ it.status_vars.val = (cowList s.1).take 65535 ⦄ := by
  sorry

/-- `get_status_var(key)`: the first variable with that key in the walk, if any. -/
theorem binlog.events.query_event.StatusVars.get_status_var_spec (s : binlog.events.query_event.StatusVars) (k : binlog.consts.StatusVarKey) :
    binlog.events.query_event.StatusVars.get_status_var s k ⦃ o => o.map (fun x => (svKeyCode x.key, x.value.val)) =
      (statusVarsOf ((cowList s.1).take 65535)).find? (fun kv => kv.1 = svKeyCode k) ⦄ := by
  sorry

/-- `into_owned`: the same bytes. -/
theorem binlog.events.query_event.StatusVars.into_owned_spec (s : binlog.events.query_event.StatusVars) :
    binlog.events.query_event.StatusVars.into_owned s ⦃ s' => cowList s'.1 = cowList s.1 ⦄ := by
  sorry

/-- `MyDeserialize` with the length `len`: total; that many bytes, an error with the buffer unchanged if fewer. -/
theorem binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.deserialize_spec (len : U16) (buf : io.ParseBuf) :
    binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMyDeserializeDeU16.deserialize len buf ⦃ r rest =>
      if len.val ≤ buf.length then (okPart r).map (fun s => cowList s.1) = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- `MySerialize`: the bytes, truncated to 65535. -/
theorem binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMySerialize.serialize_spec (s : binlog.events.query_event.StatusVars) (buf : alloc.vec.Vec U8) (h : buf.length + min (cowList s.1).length 65535 ≤ Usize.max) :
    binlog.events.query_event.StatusVars.Insts.Mysql_commonProtoMySerialize.serialize s buf ⦃ buf' => buf'.val = buf.val ++ (cowList s.1).take 65535 ⦄ := by
  sorry

end mysql_common
