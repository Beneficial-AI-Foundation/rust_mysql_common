import Defs
import Proofs.Util.ConnAuth

/-! Statements for `struct OldAuthSwitchRequest and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.CAUtil

namespace mysql_common

/-- `new`: the packet (it has no fields besides the header). -/
theorem packets.OldAuthSwitchRequest.new_eq :
    packets.OldAuthSwitchRequest.new = ok { __header := () } := by
  simp [packets.OldAuthSwitchRequest.new, misc.raw.int.ConstU8.new]

/-- `auth_plugin`: `mysql_old_password` (documented). -/
theorem packets.OldAuthSwitchRequest.auth_plugin_eq (self : packets.OldAuthSwitchRequest) :
    packets.OldAuthSwitchRequest.auth_plugin self = ok .MysqlOldPassword := by
  simp [packets.OldAuthSwitchRequest.auth_plugin]

/-- `Default`: `new()`. -/
theorem packets.OldAuthSwitchRequest.Insts.CoreDefaultDefault.default_eq :
    packets.OldAuthSwitchRequest.Insts.CoreDefaultDefault.default = ok { __header := () } := by
  simp [packets.OldAuthSwitchRequest.Insts.CoreDefaultDefault.default, packets.OldAuthSwitchRequest.new, misc.raw.int.ConstU8.new]

/-- `MyDeserialize for OldAuthSwitchRequest`: `SIZE` is `Some(1)`. -/
theorem packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 1#usize := by
  simp [packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for OldAuthSwitchRequest`: total; the header `0xFE` (`headerRead 0xFE`). Bytes after it are left unread, so an `AuthSwitchRequest` also parses as one: the caller must tell them apart by the packet length. -/
theorem packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun _ => ()), rest.val) = headerRead 0xFE buf.val ⦄ := by
  unfold packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with header_parse_spec 254#u8 packets.InvalidAuthSwitchRequestHeader.Insts.CoreErrorError
    packets.InvalidAuthSwitchRequestHeader.Insts.CoreDefaultDefault ((WP.spec_ok _).mpr trivial) as ⟨r, buf1, h1⟩
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
      have : b.val ≠ 254 := by simpa using hr
      simp [headerRead, this, hb1]
    | Ok v =>
      have : b.val = 254 := by simpa using hr
      simp [headerRead, this, hb1]
      exact ⟨⟨()⟩⟩

/-- `MySerialize for OldAuthSwitchRequest`: appends `0xFE`. -/
theorem packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.OldAuthSwitchRequest) (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ [byte 0xFE] ⦄ := by
  unfold packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize
  apply WP.spec_mono (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec _ buf h)
  intro b hb; simp [hb, byte]; rfl

/-- Round trip. -/
theorem packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (tail : List U8) (buf : io.ParseBuf) (h : buf.val = byte 0xFE :: tail) :
    packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => (okPart r).isSome ∧ rest.val = tail ⦄ := by
  apply WP.spec_mono (packets.OldAuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  simp only [h, headerRead, byte_val] at hr
  cases r <;> simp_all

end mysql_common
