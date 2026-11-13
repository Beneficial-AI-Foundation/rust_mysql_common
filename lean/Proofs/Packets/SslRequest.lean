import Defs

/-! Statements for `struct SslRequest and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: the given fields, MariaDB's capabilities empty. -/
theorem packets.SslRequest.new_spec (capabilities : constants.CapabilityFlags) (max_packet_size : U32) (character_set : U8) :
    packets.SslRequest.new capabilities max_packet_size character_set ⦃ p =>
      SslReq.of p = ⟨capabilities.val, max_packet_size.val, character_set.val, 0⟩ ⦄ := by
  sorry

/-- `with_mariadb_capabilities`: replaces MariaDB's capabilities. -/
theorem packets.SslRequest.with_mariadb_capabilities_spec (self : packets.SslRequest) (mariadb_capabilities : constants.MariadbCapabilities) :
    packets.SslRequest.with_mariadb_capabilities self mariadb_capabilities ⦃ p =>
      SslReq.of p = { SslReq.of self with mariadbCaps := mariadb_capabilities.val } ⦄ := by
  sorry

/-- `capabilities`: the field. -/
theorem packets.SslRequest.impl.capabilities_eq (self : packets.SslRequest) :
    packets.SslRequest.impl.capabilities self = ok self.capabilities.1 := by
  sorry

/-- `max_packet_size`: the field. -/
theorem packets.SslRequest.impl.max_packet_size_eq (self : packets.SslRequest) :
    packets.SslRequest.impl.max_packet_size self = ok self.max_packet_size.1 := by
  sorry

/-- `character_set`: the field. -/
theorem packets.SslRequest.impl.character_set_eq (self : packets.SslRequest) :
    packets.SslRequest.impl.character_set self = ok self.character_set.1 := by
  sorry

/-- `MyDeserialize for SslRequest`: `SIZE` is `Some(32)`. -/
theorem packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = ok (some 32#usize) := by
  sorry

/-- `MyDeserialize for SslRequest`: total; `sslRequestRead`. -/
theorem packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => ((okPart r).map SslReq.of, rest.val) = sslRequestRead buf.val ⦄ := by
  sorry

/-- `MySerialize for SslRequest`: appends `sslRequestEnc` of the fields. -/
theorem packets.SslRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.SslRequest) (buf : alloc.vec.Vec U8) (h : buf.length + 32 ≤ Usize.max) :
    packets.SslRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ sslRequestEnc (SslReq.of self) ⦄ := by
  sorry

/-- Round trip, for fields that fit and known MariaDB bits. -/
theorem packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (v : SslReq) (hv : v.caps < 2 ^ 32 ∧ v.maxPacket < 2 ^ 32 ∧ v.charset < 256 ∧
      v.mariadbCaps &&& mariadbCapabilitiesAll = v.mariadbCaps)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = sslRequestEnc v ++ tail) :
    packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => (okPart r).map SslReq.of = some v ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
