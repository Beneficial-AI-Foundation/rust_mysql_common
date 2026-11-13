import Defs
import Proofs.Util.ConnAuth

/-! Statements for `struct LocalInfilePacket and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.CAUtil

namespace mysql_common

/-- `new`: the given file name (converted with `into`). -/
theorem packets.LocalInfilePacket.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (file_name : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into file_name = ok c) :
    packets.LocalInfilePacket.new into file_name ⦃ p => p.file_name.1 = c ⦄ := by
  unfold packets.LocalInfilePacket.new misc.raw.int.ConstU8.new
  step*

/-- `file_name_ref`: the file name. -/
theorem packets.LocalInfilePacket.file_name_ref_spec (self : packets.LocalInfilePacket) :
    packets.LocalInfilePacket.file_name_ref self ⦃ s => s.val = cowList self.file_name.1 ⦄ := by
  exact eof_as_bytes_spec _

/-- `into_owned`: the same file name. -/
theorem packets.LocalInfilePacket.into_owned_spec (self : packets.LocalInfilePacket) :
    packets.LocalInfilePacket.into_owned self ⦃ p => cowList p.file_name.1 = cowList self.file_name.1 ⦄ := by
  unfold packets.LocalInfilePacket.into_owned
  step*

/-- `MyDeserialize for LocalInfilePacket`: `SIZE` is `None`. -/
theorem packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  simp [packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for LocalInfilePacket`: total; the header `0xFB` and the file name as the rest of the packet (`eofPayloadRead 0xFB`). -/
theorem packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => cowList p.file_name.1), rest.val) = eofPayloadRead 0xFB buf.val ⦄ := by
  unfold packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with header_parse_spec 251#u8 packets.InvalidLocalInfileHeader.Insts.CoreErrorError
    packets.InvalidLocalInfileHeader.Insts.CoreDefaultDefault ((WP.spec_ok _).mpr trivial) as ⟨r, buf1, h1⟩
  cases hb : (↑buf : List U8) with
  | nil =>
    rw [hb] at h1
    obtain ⟨hr, rfl⟩ := h1
    cases r with
    | Ok _ => simp at hr
    | Err e => simp [eofPayloadRead, hb]
  | cons b t =>
    rw [hb] at h1
    obtain ⟨hr, hb1⟩ := h1
    cases r with
    | Err e =>
      have : b.val ≠ 251 := by simpa using hr
      simp [eofPayloadRead, this, hb1]
    | Ok v =>
      have : b.val = 251 := by simpa using hr
      simp only [branch_ok]
      step with parse_eof_bytes_spec as ⟨r2, buf2, h2a, h2b⟩
      cases r2 with
      | Err e => simp at h2a
      | Ok rb =>
        simp at h2a
        simp [eofPayloadRead, this, h2a, h2b, hb1]

/-- `MySerialize for LocalInfilePacket`: appends `0xFB` and the file name. -/
theorem packets.LocalInfilePacket.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.LocalInfilePacket) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + (cowList self.file_name.1).length ≤ Usize.max) :
    packets.LocalInfilePacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ byte 0xFB :: cowList self.file_name.1 ⦄ := by
  unfold packets.LocalInfilePacket.Insts.Mysql_commonProtoMySerialize.serialize
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨buf1, h1⟩
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  apply WP.spec_mono (misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf1 ?_)
  · intro b hb; simp [hb, h1, hs, byte]; rfl
  · simp [alloc.vec.Vec.length, Slice.length, h1, hs] at *; omega

/-- Round trip: a `LOCAL INFILE` request (the whole packet) reads back with its file name. -/
theorem packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (nm : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0xFB :: nm) :
    packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun p => cowList p.file_name.1) = some nm ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (packets.LocalInfilePacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  simp only [h, eofPayloadRead, byte_val] at hr
  simpa using hr

end mysql_common
