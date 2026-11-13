import Defs

/-! Statements for `struct PublicKeyResponse and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: the given key (converted with `into`). -/
theorem packets.PublicKeyResponse.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (rsa_key : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into rsa_key = ok c) :
    packets.PublicKeyResponse.new into rsa_key ⦃ p => p.rsa_key.1 = c ⦄ := by
  sorry

/-- `MyDeserialize for PublicKeyResponse`: `SIZE` is `None`. -/
theorem packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for PublicKeyResponse`: total; the header `0x01` (that of `AuthMoreData`) and the key as the rest of the packet. The key is not checked to be PEM. -/
theorem packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => cowList p.rsa_key.1), rest.val) = eofPayloadRead 0x01 buf.val ⦄ := by
  sorry

/-- `MySerialize for PublicKeyResponse`: appends `0x01` and the key. -/
theorem packets.PublicKeyResponse.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.PublicKeyResponse) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + (cowList self.rsa_key.1).length ≤ Usize.max) :
    packets.PublicKeyResponse.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ byte 0x01 :: cowList self.rsa_key.1 ⦄ := by
  sorry

/-- Round trip (the packet is the whole buffer). -/
theorem packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (key : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0x01 :: key) :
    packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun p => cowList p.rsa_key.1) = some key ∧ rest.val = [] ⦄ := by
  sorry

end mysql_common
