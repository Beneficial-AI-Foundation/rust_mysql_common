import Defs
import Proofs.Util.ConnAuth

/-! Statements for `struct PublicKeyResponse and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.CAUtil

namespace mysql_common

/-- `new`: the given key (converted with `into`). -/
theorem packets.PublicKeyResponse.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (rsa_key : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into rsa_key = ok c) :
    packets.PublicKeyResponse.new into rsa_key ⦃ p => p.rsa_key.1 = c ⦄ := by
  unfold packets.PublicKeyResponse.new misc.raw.int.ConstU8.new
  step*

/-- `MyDeserialize for PublicKeyResponse`: `SIZE` is `None`. -/
theorem packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  simp [packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for PublicKeyResponse`: total; the header `0x01` (that of `AuthMoreData`) and the key as the rest of the packet. The key is not checked to be PEM. -/
theorem packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => cowList p.rsa_key.1), rest.val) = eofPayloadRead 0x01 buf.val ⦄ := by
  unfold packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with header_parse_spec 1#u8 packets.InvalidPublicKeyResponse.Insts.CoreErrorError
    packets.InvalidPublicKeyResponse.Insts.CoreDefaultDefault ((WP.spec_ok _).mpr trivial) as ⟨r, buf1, h1⟩
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

/-- `MySerialize for PublicKeyResponse`: appends `0x01` and the key. -/
theorem packets.PublicKeyResponse.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.PublicKeyResponse) (buf : alloc.vec.Vec U8)
    (h : buf.length + 1 + (cowList self.rsa_key.1).length ≤ Usize.max) :
    packets.PublicKeyResponse.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ byte 0x01 :: cowList self.rsa_key.1 ⦄ := by
  unfold packets.PublicKeyResponse.Insts.Mysql_commonProtoMySerialize.serialize
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨buf1, h1⟩
  apply misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec
  intro s hs
  apply WP.spec_mono (misc.raw.bytes.EofBytes.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec s buf1 ?_)
  · intro b hb; simp [hb, h1, hs, byte]; rfl
  · simp [alloc.vec.Vec.length, Slice.length, h1, hs] at *; omega

/-- Round trip (the packet is the whole buffer). -/
theorem packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (key : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0x01 :: key) :
    packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun p => cowList p.rsa_key.1) = some key ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (packets.PublicKeyResponse.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  simp only [h, eofPayloadRead, byte_val] at hr
  simpa using hr

end mysql_common
