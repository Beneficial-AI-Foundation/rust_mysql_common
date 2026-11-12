import Defs

/-! Statements for `struct ServerError and its impls` (spec file: `Specs/Packets.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: the given fields (the message converted with `into`). -/
theorem packets.ServerError.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (code : U16) (state : Option packets.SqlState) (msg : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into msg = ok c) :
    packets.ServerError.new into code state msg ⦃ e =>
      e.code.1 = code ∧ e.state = state ∧ e.message.1 = c ⦄ := by
  sorry

/-- `error_code`: the field. -/
theorem packets.ServerError.error_code_eq (self : packets.ServerError) :
    packets.ServerError.error_code self = ok self.code.1 := by
  sorry

/-- `sql_state_ref`: the field. -/
theorem packets.ServerError.sql_state_ref_eq (self : packets.ServerError) :
    packets.ServerError.sql_state_ref self = ok self.state := by
  sorry

/-- `message_ref`: the message bytes. -/
theorem packets.ServerError.message_ref_spec (self : packets.ServerError) :
    packets.ServerError.message_ref self ⦃ s => s.val = cowList self.message.1 ⦄ := by
  sorry

/-- `into_owned`: the same fields. -/
theorem packets.ServerError.into_owned_spec (self : packets.ServerError) :
    packets.ServerError.into_owned self ⦃ e => ErrPkt.ofServerError e = ErrPkt.ofServerError self ⦄ := by
  sorry

/-- `MyDeserialize for ServerError`: `SIZE` is `None`. -/
theorem packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.SIZE_eq :
    packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.SIZE = none := by
  sorry

/-- `MyDeserialize for ServerError` with context `(code, protocol_41)`: total; `serverErrorRead`. -/
theorem packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.deserialize_spec (code : U16) (p41 : Bool) (buf : io.ParseBuf) :
    packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.deserialize (code, p41) buf ⦃ r rest =>
      ((okPart r).map ErrPkt.ofServerError, rest.val) = serverErrorRead code.val p41 buf.val ⦄ := by
  sorry

/-- `MySerialize for ServerError`: appends the SQL state (`#` and 5 bytes) if present, then the message (the code is written by `ErrPacket`). -/
theorem packets.ServerError.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ServerError) (buf : alloc.vec.Vec U8)
    (h : buf.length + 6 + (cowList self.message.1).length ≤ Usize.max) :
    packets.ServerError.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ (match self.state with | some s => byte 0x23 :: s.state.val | none => [])
        ++ cowList self.message.1 ⦄ := by
  sorry

end mysql_common
