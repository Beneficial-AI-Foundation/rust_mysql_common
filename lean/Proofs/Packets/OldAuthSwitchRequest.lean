import Defs

/-! Statements for `struct OldAuthSwitchRequest and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: the packet (it has no fields besides the header). -/
theorem packets.OldAuthSwitchRequest.new_eq :
    packets.OldAuthSwitchRequest.new = ok { __header := () } := by
  sorry

/-- `auth_plugin`: `mysql_old_password` (documented). -/
theorem packets.OldAuthSwitchRequest.auth_plugin_eq (self : packets.OldAuthSwitchRequest) :
    packets.OldAuthSwitchRequest.auth_plugin self = ok .MysqlOldPassword := by
  sorry

/-- `Default`: `new()`. -/
theorem packets.OldAuthSwitchRequest.Insts.CoreDefaultDefault.default_eq :
    packets.OldAuthSwitchRequest.Insts.CoreDefaultDefault.default = ok { __header := () } := by
  sorry

/-- `MyDeserialize for OldAuthSwitchRequest`: `SIZE` is `Some(1)`. -/
theorem packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 1#usize := by
  sorry

/-- `MyDeserialize for OldAuthSwitchRequest`: total; the header `0xFE` (`headerRead 0xFE`). Bytes after it are left unread, so an `AuthSwitchRequest` also parses as one: the caller must tell them apart by the packet length. -/
theorem packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun _ => ()), rest.val) = headerRead 0xFE buf.val ⦄ := by
  sorry

/-- `MySerialize for OldAuthSwitchRequest`: appends `0xFE`. -/
theorem packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.OldAuthSwitchRequest) (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ [byte 0xFE] ⦄ := by
  sorry

/-- Round trip. -/
theorem packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (tail : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0xFE :: tail) :
    packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => (okPart r).isSome ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
