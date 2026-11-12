import Defs

/-! Statements for `struct SqlState and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: the given state. -/
theorem packets.SqlState.new_eq (state : Array U8 5#usize) :
    packets.SqlState.new state = ok { __state_marker := (), state } := by
  sorry

/-- `as_bytes`: the state. -/
theorem packets.SqlState.as_bytes_eq (self : packets.SqlState) :
    packets.SqlState.as_bytes self = ok self.state := by
  sorry

/-- `MyDeserialize for SqlState`: `SIZE` is `Some(6)`. -/
theorem packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 6#usize := by
  sorry

/-- `MyDeserialize for SqlState`: total (each part is read with `parse`); `sqlStateRead` (`#`, then 5 bytes). -/
theorem packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun s => s.state.val), rest.val) = sqlStateRead buf.val ⦄ := by
  sorry

/-- `MySerialize for SqlState`: appends `#` and the state. -/
theorem packets.SqlState.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.SqlState) (buf : alloc.vec.Vec U8) (h : buf.length + 6 ≤ Usize.max) :
    packets.SqlState.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ byte 0x23 :: self.state.val ⦄ := by
  sorry

end mysql_common
