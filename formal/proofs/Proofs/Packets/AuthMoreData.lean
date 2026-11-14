import Defs
import Proofs.Util.ConnAuth

/-! Statements for `struct AuthMoreData and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.CAUtil

namespace mysql_common

/-- `new`: the given data (converted with `into`). -/
theorem packets.AuthMoreData.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (data : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into data = ok c) :
    packets.AuthMoreData.new into data ⦃ p => p.data.1 = c ⦄ := by
  unfold packets.AuthMoreData.new misc.raw.int.ConstU8.new
  step*

/-- `data`: the data. -/
theorem packets.AuthMoreData.impl.data_spec (self : packets.AuthMoreData) :
    packets.AuthMoreData.impl.data self ⦃ s => s.val = cowList self.data.1 ⦄ := by
  exact eof_as_bytes_spec _

/-- `into_owned`: the same data. -/
theorem packets.AuthMoreData.into_owned_spec (self : packets.AuthMoreData) :
    packets.AuthMoreData.into_owned self ⦃ p => cowList p.data.1 = cowList self.data.1 ⦄ := by
  unfold packets.AuthMoreData.into_owned
  step*

/-- `MyDeserialize for AuthMoreData`: `SIZE` is `None`. -/
theorem packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  simp [packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for AuthMoreData`: total; the header `0x01` and the data as the rest of the packet. -/
theorem packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => cowList p.data.1), rest.val) = eofPayloadRead 0x01 buf.val ⦄ := by
  unfold packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with header_parse_spec 1#u8 packets.InvalidAuthMoreDataHeader.Insts.CoreErrorError
    packets.InvalidAuthMoreDataHeader.Insts.CoreDefaultDefault ((WP.spec_ok _).mpr trivial) as ⟨r, buf1, h1⟩
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
      have : b.val ≠ 1 := by simpa using hr
      simp [eofPayloadRead, this, hb1]
    | Ok v =>
      have : b.val = 1 := by simpa using hr
      simp only [branch_ok]
      step with parse_eof_bytes_spec as ⟨r2, buf2, h2a, h2b⟩
      cases r2 with
      | Err e => simp at h2a
      | Ok rb =>
        simp at h2a
        simp [eofPayloadRead, this, h2a, h2b, hb1]

/-- `MySerialize for AuthMoreData`: appends `0x01` and the data. -/
theorem packets.AuthMoreData.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.AuthMoreData) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + (cowList self.data.1).length ≤ Usize.max) :
    packets.AuthMoreData.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ byte 0x01 :: cowList self.data.1 ⦄ := by
  unfold packets.AuthMoreData.Insts.Mysql_commonProtoMySerialize.serialize
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨buf1, h1⟩
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  apply WP.spec_mono (misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf1 ?_)
  · intro b hb; simp [hb, h1, hs, byte]; rfl
  · simp [alloc.vec.Vec.length, Slice.length, h1, hs] at *; omega

/-- Round trip (the packet is the whole buffer). -/
theorem packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (data : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0x01 :: data) :
    packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun p => cowList p.data.1) = some data ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (packets.AuthMoreData.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  simp only [h, eofPayloadRead, byte_val] at hr
  simpa using hr

end mysql_common
