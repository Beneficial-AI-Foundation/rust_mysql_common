import Defs
import Proofs.Util.ConnAuth

/-! Statements for `struct PublicKeyRequest and its impls` (spec file: `Specs/Packets/CachingSha2Password.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.CAUtil

namespace mysql_common

/-- `new`: the packet (it has no fields besides the header). -/
theorem packets.caching_sha2_password.PublicKeyRequest.new_eq :
    packets.caching_sha2_password.PublicKeyRequest.new = ok { __header := () } := by
  simp [packets.caching_sha2_password.PublicKeyRequest.new, misc.raw.int.ConstU8.new]

/-- `Default`: `new()`. -/
theorem packets.caching_sha2_password.PublicKeyRequest.Insts.CoreDefaultDefault.default_eq :
    packets.caching_sha2_password.PublicKeyRequest.Insts.CoreDefaultDefault.default = ok { __header := () } := by
  simp [packets.caching_sha2_password.PublicKeyRequest.Insts.CoreDefaultDefault.default, packets.caching_sha2_password.PublicKeyRequest.new, misc.raw.int.ConstU8.new]

/-- `MyDeserialize for PublicKeyRequest`: `SIZE` is `None`. -/
theorem packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  simp [packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for PublicKeyRequest`: total; the header `0x02` (`headerRead 0x02`); bytes after it are left unread. -/
theorem packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun _ => ()), rest.val) = headerRead 0x02 buf.val ⦄ := by
  unfold packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with header_parse_spec 2#u8 packets.caching_sha2_password.InvalidPublicKeyRequest.Insts.CoreErrorError
    packets.caching_sha2_password.InvalidPublicKeyRequest.Insts.CoreDefaultDefault ((WP.spec_ok _).mpr trivial) as ⟨r, buf1, h1⟩
  cases hb : (↑buf : List U8) with
  | nil =>
    rw [hb] at h1
    obtain ⟨hr, rfl⟩ := h1
    cases r with
    | Ok _ => simp at hr
    | Err e => simp [headerRead, hb]
  | cons b t =>
    rw [hb] at h1
    obtain ⟨hr, hb1⟩ := h1
    cases r with
    | Err e =>
      have : b.val ≠ 2 := by simpa using hr
      simp [headerRead, this, hb1]
    | Ok v =>
      have : b.val = 2 := by simpa using hr
      simp [headerRead, this, hb1]
      exact ⟨⟨()⟩⟩

/-- `MySerialize for PublicKeyRequest`: appends `0x02`. -/
theorem packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.caching_sha2_password.PublicKeyRequest) (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ [byte 0x02] ⦄ := by
  unfold packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMySerialize.serialize
  apply WP.spec_mono (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec _ buf h)
  intro b hb; simp [hb, byte]; rfl

/-- Round trip. -/
theorem packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (tail : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0x02 :: tail) :
    packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => (okPart r).isSome ∧ rest.val = tail ⦄ := by
  apply WP.spec_mono (packets.caching_sha2_password.PublicKeyRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  simp only [h, headerRead, byte_val] at hr
  cases r <;> simp_all

end mysql_common
