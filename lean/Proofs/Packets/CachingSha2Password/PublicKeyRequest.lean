import Defs

/-! Statements for `struct PublicKeyRequest and its impls` (spec file: `Specs/Packets/CachingSha2Password.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: the packet (it has no fields besides the header). -/
theorem packets.caching_sha2_password.PublicKeyRequest.new_eq :
    packets.caching_sha2_password.PublicKeyRequest.new = ok { __header := () } := by
  sorry

/-- `Default`: `new()`. -/
theorem packets.caching_sha2_password.PublicKeyRequest.Insts.CoreDefaultDefault.default_eq :
    packets.caching_sha2_password.PublicKeyRequest.Insts.CoreDefaultDefault.default = ok { __header := () } := by
  sorry

/-- `MyDeserialize for PublicKeyRequest`: `SIZE` is `None`. -/
theorem packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for PublicKeyRequest`: total; the header `0x02` (`headerRead 0x02`); bytes after it are left unread. -/
theorem packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun _ => ()), rest.val) = headerRead 0x02 buf.val ⦄ := by
  sorry

/-- `MySerialize for PublicKeyRequest`: appends `0x02`. -/
theorem packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.caching_sha2_password.PublicKeyRequest) (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ [byte 0x02] ⦄ := by
  sorry

/-- Round trip. -/
theorem packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (tail : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0x02 :: tail) :
    packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => (okPart r).isSome ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
