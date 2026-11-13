import Defs

/-! Statements for `struct AuthSwitchRequest and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: the given plugin name and data (converted with `into`). -/
theorem packets.AuthSwitchRequest.new_spec {T1 T2 : Type} (into1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (into2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (auth_plugin : T1) (plugin_data : T2) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h1 : into1.into auth_plugin = ok c1) (h2 : into2.into plugin_data = ok c2) :
    packets.AuthSwitchRequest.new into1 into2 auth_plugin plugin_data ⦃ p => p.auth_plugin.1 = c1 ∧ p.plugin_data.1 = c2 ⦄ := by
  sorry

/-- `auth_plugin`: `AuthPlugin::from_bytes` of the name. -/
theorem packets.AuthSwitchRequest.impl.auth_plugin_spec (self : packets.AuthSwitchRequest) :
    packets.AuthSwitchRequest.impl.auth_plugin self ⦃ r => PluginFromBytes (cowList self.auth_plugin.1) r ⦄ := by
  sorry

/-- `plugin_data`: the data, without its last byte if that is `0` and the plugin is one whose scramble MySQL sends as a C string (`usesCStringScramble`; documented: other servers may not add the `0`). -/
theorem packets.AuthSwitchRequest.impl.plugin_data_spec (self : packets.AuthSwitchRequest) :
    packets.AuthSwitchRequest.impl.plugin_data self ⦃ s =>
      s.val = if usesCStringScramble (cowList self.auth_plugin.1) then dropTrailingNul (cowList self.plugin_data.1)
        else cowList self.plugin_data.1 ⦄ := by
  sorry

/-- `into_owned`: the same name and data. -/
theorem packets.AuthSwitchRequest.into_owned_spec (self : packets.AuthSwitchRequest) :
    packets.AuthSwitchRequest.into_owned self ⦃ p =>
      cowList p.auth_plugin.1 = cowList self.auth_plugin.1 ∧ cowList p.plugin_data.1 = cowList self.plugin_data.1 ⦄ := by
  sorry

/-- `MyDeserialize for AuthSwitchRequest`: `SIZE` is `None`. -/
theorem packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for AuthSwitchRequest`: total; `authSwitchRead` (header `0xFE`, `string<NUL>` plugin name, `string<EOF>` data). -/
theorem packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => (cowList p.auth_plugin.1, cowList p.plugin_data.1)), rest.val) = authSwitchRead buf.val ⦄ := by
  sorry

/-- `MySerialize for AuthSwitchRequest`: appends `authSwitchEnc` of the name (cut at its first `0`) and data. -/
theorem packets.AuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.AuthSwitchRequest) (buf : alloc.vec.Vec U8)
    (h : buf.length + (authSwitchEnc (cowList self.auth_plugin.1) (cowList self.plugin_data.1)).length ≤ Usize.max) :
    packets.AuthSwitchRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ authSwitchEnc (cowList self.auth_plugin.1) (cowList self.plugin_data.1) ⦄ := by
  sorry

/-- Round trip, for a plugin name without `0` (the packet is the whole buffer). -/
theorem packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (nm data : List U8) (hn : NoNul nm) (buf : io.ParseBuf) (h : buf.val = authSwitchEnc nm data) :
    packets.AuthSwitchRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun p => (cowList p.auth_plugin.1, cowList p.plugin_data.1)) = some (nm, data) ∧ rest.val = [] ⦄ := by
  sorry

end mysql_common
