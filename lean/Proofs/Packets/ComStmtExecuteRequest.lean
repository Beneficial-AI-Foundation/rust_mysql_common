import Defs

/-! Statements for `struct ComStmtExecuteRequest and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `stmt_id`: the field. -/
theorem packets.ComStmtExecuteRequest.impl.stmt_id_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.stmt_id self = ok self.stmt_id.1 := by
  sorry

/-- `flags`: the field. -/
theorem packets.ComStmtExecuteRequest.impl.flags_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.flags self = ok self.flags.1 := by
  sorry

/-- `bitmap`: the bitmap bytes, at most 8192 (`BareBytes<8192>`). -/
theorem packets.ComStmtExecuteRequest.impl.bitmap_spec (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.bitmap self ⦃ s => s.val = (cowList self.bitmap.1).take 8192 ⦄ := by
  sorry

/-- `params_flags`: the field. -/
theorem packets.ComStmtExecuteRequest.impl.params_flags_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.params_flags self = ok self.params_flags.1 := by
  sorry

/-- `params`: the parameters (a slice of values: patch 28). -/
theorem packets.ComStmtExecuteRequest.impl.params_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.params self = ok self.params := by
  sorry

/-- `as_long_data`: the field. -/
theorem packets.ComStmtExecuteRequest.impl.as_long_data_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.as_long_data self = ok self.as_long_data := by
  sorry

/-- `MySerialize for ComStmtExecuteRequest`: appends `stmtExecuteBytes` of its fields: header, statement id, flags, iteration count; if there are parameters, the bitmap (truncated to 8192 bytes), the params flags, the parameter types and the values (`Bytes` left out if `as_long_data`). -/
theorem packets.ComStmtExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ComStmtExecuteRequest) (buf : alloc.vec.Vec U8)
    (h : buf.length + (stmtExecuteBytes self.stmt_id.1.val self.flags.1.val ((cowList self.bitmap.1).take 8192)
      self.params_flags.1.val (self.params.val.map Val.ofValue) self.as_long_data).length ≤ Usize.max) :
    packets.ComStmtExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ stmtExecuteBytes self.stmt_id.1.val self.flags.1.val ((cowList self.bitmap.1).take 8192)
        self.params_flags.1.val (self.params.val.map Val.ofValue) self.as_long_data ⦄ := by
  sorry

end mysql_common
