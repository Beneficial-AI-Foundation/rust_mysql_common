import Defs

/-! Statements for `struct LocalInfilePacket and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: the given file name (converted with `into`). -/
theorem packets.LocalInfilePacket.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (file_name : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into file_name = ok c) :
    packets.LocalInfilePacket.new into file_name ⦃ p => p.file_name.1 = c ⦄ := by
  sorry

/-- `file_name_ref`: the file name. -/
theorem packets.LocalInfilePacket.file_name_ref_spec (self : packets.LocalInfilePacket) :
    packets.LocalInfilePacket.file_name_ref self ⦃ s => s.val = cowList self.file_name.1 ⦄ := by
  sorry

/-- `into_owned`: the same file name. -/
theorem packets.LocalInfilePacket.into_owned_spec (self : packets.LocalInfilePacket) :
    packets.LocalInfilePacket.into_owned self ⦃ p => cowList p.file_name.1 = cowList self.file_name.1 ⦄ := by
  sorry

/-- `MyDeserialize for LocalInfilePacket`: `SIZE` is `None`. -/
theorem packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for LocalInfilePacket`: total; the header `0xFB` and the file name as the rest of the packet (`eofPayloadRead 0xFB`). -/
theorem packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => cowList p.file_name.1), rest.val) = eofPayloadRead 0xFB buf.val ⦄ := by
  sorry

/-- `MySerialize for LocalInfilePacket`: appends `0xFB` and the file name. -/
theorem packets.LocalInfilePacket.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.LocalInfilePacket) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + (cowList self.file_name.1).length ≤ Usize.max) :
    packets.LocalInfilePacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ byte 0xFB :: cowList self.file_name.1 ⦄ := by
  sorry

/-- Round trip: a `LOCAL INFILE` request (the whole packet) reads back with its file name. -/
theorem packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (nm : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0xFB :: nm) :
    packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun p => cowList p.file_name.1) = some nm ∧ rest.val = [] ⦄ := by
  sorry

end mysql_common
