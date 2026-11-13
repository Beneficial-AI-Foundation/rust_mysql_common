import Defs

/-! Statements for `struct AuthMoreData and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: the given data (converted with `into`). -/
theorem packets.AuthMoreData.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (data : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into data = ok c) :
    packets.AuthMoreData.new into data ⦃ p => p.data.1 = c ⦄ := by
  sorry

/-- `data`: the data. -/
theorem packets.AuthMoreData.impl.data_spec (self : packets.AuthMoreData) :
    packets.AuthMoreData.impl.data self ⦃ s => s.val = cowList self.data.1 ⦄ := by
  sorry

/-- `into_owned`: the same data. -/
theorem packets.AuthMoreData.into_owned_spec (self : packets.AuthMoreData) :
    packets.AuthMoreData.into_owned self ⦃ p => cowList p.data.1 = cowList self.data.1 ⦄ := by
  sorry

/-- `MyDeserialize for AuthMoreData`: `SIZE` is `None`. -/
theorem packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for AuthMoreData`: total; the header `0x01` and the data as the rest of the packet. -/
theorem packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => cowList p.data.1), rest.val) = eofPayloadRead 0x01 buf.val ⦄ := by
  sorry

/-- `MySerialize for AuthMoreData`: appends `0x01` and the data. -/
theorem packets.AuthMoreData.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.AuthMoreData) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + (cowList self.data.1).length ≤ Usize.max) :
    packets.AuthMoreData.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ byte 0x01 :: cowList self.data.1 ⦄ := by
  sorry

/-- Round trip (the packet is the whole buffer). -/
theorem packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (data : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0x01 :: data) :
    packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun p => cowList p.data.1) = some data ∧ rest.val = [] ⦄ := by
  sorry

end mysql_common
