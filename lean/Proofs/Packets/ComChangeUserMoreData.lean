import Defs

/-! Statements for `struct ComChangeUserMoreData and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: the character set, no plugin, no attributes. -/
theorem packets.ComChangeUserMoreData.new_spec (character_set : U16) :
    packets.ComChangeUserMoreData.new character_set ⦃ m =>
      ChangeUserMore.of m = ⟨character_set.val, none⟩ ∧ m.connect_attributes = none ⦄ := by
  sorry

/-- `with_auth_plugin`: replaces the plugin. -/
theorem packets.ComChangeUserMoreData.with_auth_plugin_eq (self : packets.ComChangeUserMoreData) (auth_plugin : Option packets.AuthPlugin) :
    packets.ComChangeUserMoreData.with_auth_plugin self auth_plugin = ok { self with auth_plugin := auth_plugin } := by
  sorry

/-- `with_connect_attributes`: replaces the attributes by the map converted from the given one (`Trusted.connectAttrsFromStrings`). -/
theorem packets.ComChangeUserMoreData.with_connect_attributes_eq (self : packets.ComChangeUserMoreData) (connect_attributes : Option Trusted.StringMap) :
    packets.ComChangeUserMoreData.with_connect_attributes self connect_attributes =
      ok { self with connect_attributes := connect_attributes.map Trusted.connectAttrsFromStrings } := by
  sorry

/-- `into_owned`: the same fields; the plugin stays known or `Other`, the map becomes `connectAttrsIntoOwned` of itself. -/
theorem packets.ComChangeUserMoreData.into_owned_spec (self : packets.ComChangeUserMoreData) :
    packets.ComChangeUserMoreData.into_owned self ⦃ m =>
      ChangeUserMore.of m = ChangeUserMore.of self ∧
        m.auth_plugin.map isOtherPlugin = self.auth_plugin.map isOtherPlugin ∧
        m.connect_attributes = self.connect_attributes.map Trusted.connectAttrsIntoOwned ⦄ := by
  sorry

/-- `MyDeserialize for ComChangeUserMoreData`: `SIZE` is `None`. -/
theorem packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq :
    packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE = none := by
  sorry

/-- `MyDeserialize for ComChangeUserMoreData`: total; `changeUserMoreRead` with the capability flags. (The plugin name is re-parsed as an `AuthPlugin` from the borrowed bytes; the `unreachable!()` for owned bytes is indeed unreachable.) -/
theorem packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      optMatch (fun m vk => ChangeUserMore.Matches m vk.1 vk.2) (okPart r) (changeUserMoreRead caps.val buf.val).1 ∧
        rest.val = (changeUserMoreRead caps.val buf.val).2 ⦄ := by
  sorry

/-- `MySerialize for ComChangeUserMoreData`: appends `changeUserMoreEnc`: **the attributes are always written** (the single byte `0` if there are none, by `Trusted.connectAttrsEntries_new`), whatever the flags. -/
theorem packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ComChangeUserMoreData) (buf : alloc.vec.Vec U8)
    (h : buf.length + (changeUserMoreEnc (ChangeUserMore.of self) ((self.connect_attributes.map attrsEntries).getD [])).length ≤ Usize.max) :
    packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ changeUserMoreEnc (ChangeUserMore.of self) ((self.connect_attributes.map attrsEntries).getD []) ⦄ := by
  sorry

/-- Round trip, with `ChangeUserMore.Compatible` flags (in particular `CLIENT_CONNECT_ATTRS`: otherwise the always-written attributes are left unread). -/
theorem packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip (h64 : Target64) (caps : constants.CapabilityFlags) (m : ChangeUserMore) (kvs : List (List U8 × List U8))
    (hc : ChangeUserMore.Compatible caps.val m) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = changeUserMoreEnc m kvs ++ tail) :
    packets.ComChangeUserMoreData.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      (∃ md, okPart r = some md ∧ ChangeUserMore.Matches md m (some kvs)) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
