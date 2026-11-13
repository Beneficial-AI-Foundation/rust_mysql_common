import Defs

/-! Statements for `struct SemiSyncAckPacket and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `SemiSyncAckPacket::new(position, filename)`: the position and the file name
    (`filename.into()`). -/
theorem packets.SemiSyncAckPacket.new_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (position : U64) (filename : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into filename = ok c) :
    packets.SemiSyncAckPacket.new into position filename ⦃ p =>
      p.position.1 = position ∧ p.filename.1 = c ⦄ := by
  sorry

/-- `with_position`: sets the position; nothing else changes. -/
theorem packets.SemiSyncAckPacket.with_position_spec (self : packets.SemiSyncAckPacket) (position : U64) :
    packets.SemiSyncAckPacket.with_position self position ⦃ p =>
      p.position.1 = position ∧ p.filename = self.filename ⦄ := by
  sorry

/-- `with_filename`: sets the file name; nothing else changes. -/
theorem packets.SemiSyncAckPacket.with_filename_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.SemiSyncAckPacket) (filename : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into filename = ok c) :
    packets.SemiSyncAckPacket.with_filename into self filename ⦃ p =>
      p.position = self.position ∧ p.filename.1 = c ⦄ := by
  sorry

/-- `position`: the field. -/
theorem packets.SemiSyncAckPacket.impl.position_eq (self : packets.SemiSyncAckPacket) :
    packets.SemiSyncAckPacket.impl.position self = ok self.position.1 := by
  sorry

/-- `filename_raw`: the file name. -/
theorem packets.SemiSyncAckPacket.filename_raw_spec (self : packets.SemiSyncAckPacket) :
    packets.SemiSyncAckPacket.filename_raw self ⦃ s => s.val = cowList self.filename.1 ⦄ := by
  sorry

/-- `filename`: the file name as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.SemiSyncAckPacket.impl.filename_spec (self : packets.SemiSyncAckPacket) :
    packets.SemiSyncAckPacket.impl.filename self ⦃ c => LossyUtf8Valid (cowList self.filename.1) c ⦄ := by
  sorry

/-- `MySerialize for SemiSyncAckPacket`: appends `semiSyncAckEnc` (`0xEF`, the position, the
    file name). -/
theorem packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.SemiSyncAckPacket) (buf : alloc.vec.Vec U8)
    (h : buf.length + 9 + (cowList self.filename.1).length ≤ Usize.max) :
    packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ semiSyncAckEnc self.position.1.val (cowList self.filename.1) ⦄ := by
  sorry

/-- `MyDeserialize for SemiSyncAckPacket`: `SIZE` is `None`. -/
theorem packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for SemiSyncAckPacket`: total; `semiSyncAckRead` (9 bytes, then the file name
    is the rest of the input). -/
theorem packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => (p.position.1.val, cowList p.filename.1)), rest.val) =
        semiSyncAckRead buf.val ⦄ := by
  sorry

/-- Round trip: `semiSyncAckEnc` is read back (the file name takes the rest of the input). -/
theorem packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (p : packets.SemiSyncAckPacket) (buf : io.ParseBuf)
    (h : buf.val = semiSyncAckEnc p.position.1.val (cowList p.filename.1)) :
    packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun q => (q.position.1.val, cowList q.filename.1)) =
        some (p.position.1.val, cowList p.filename.1) ∧ rest.val = [] ⦄ := by
  sorry

end mysql_common
