import Defs

/-! Statements for `enum AuthPlugin and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MyDeserialize for AuthPlugin`: `SIZE` is `None`. -/
theorem packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for AuthPlugin`: never an error; the plugin named by the whole buffer (without one trailing `0`), which is consumed. -/
theorem packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (∃ p, okPart r = some p ∧ PluginFromBytes buf.val p) ∧ rest.val = [] ⦄ := by
  sorry

/-- `MySerialize for AuthPlugin`: appends the name and `0` (a `string<NUL>`; the name is not cut at an inner `0`). -/
theorem packets.AuthPlugin.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.AuthPlugin) (buf : alloc.vec.Vec U8)
    (h : buf.length + (authPluginName self).length + 1 ≤ Usize.max) :
    packets.AuthPlugin.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ authPluginName self ++ [byte 0] ⦄ := by
  sorry

/-- Round trip: a serialized plugin reads back as the plugin of the same name, in normal form (`Other` holding a known name comes back as that known plugin). -/
theorem packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (p : packets.AuthPlugin) (buf : io.ParseBuf) (h : buf.val = authPluginName p ++ [byte 0]) :
    packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (∃ q, okPart r = some q ∧ IsPluginNamed (authPluginName p) q) ∧ rest.val = [] ⦄ := by
  sorry

/-- `from_bytes`: the known plugin with that name (one trailing `0` removed first), else `Other` borrowing the name. -/
theorem packets.AuthPlugin.from_bytes_spec (nm : Slice U8) :
    packets.AuthPlugin.from_bytes nm ⦃ r => PluginFromBytes nm.val r ⦄ := by
  sorry

/-- `as_bytes`: the plugin's name. -/
theorem packets.AuthPlugin.as_bytes_spec (self : packets.AuthPlugin) :
    packets.AuthPlugin.as_bytes self ⦃ s => s.val = authPluginName self ⦄ := by
  sorry

/-- `into_owned`: the same plugin; `Other` with an owned copy of its name. -/
theorem packets.AuthPlugin.into_owned_spec (self : packets.AuthPlugin) :
    packets.AuthPlugin.into_owned self ⦃ r =>
      match self with
      | .Other c => ∃ v : alloc.vec.Vec U8, r = .Other (.Owned v) ∧ v.val = cowList c
      | p => r = p ⦄ := by
  sorry

/-- `borrow`: the same plugin; `Other` borrowing its name. -/
theorem packets.AuthPlugin.borrow_spec (self : packets.AuthPlugin) :
    packets.AuthPlugin.borrow self ⦃ r =>
      match self with
      | .Other c => ∃ s : Slice U8, r = .Other (.Borrowed s) ∧ s.val = cowList c
      | p => r = p ⦄ := by
  sorry

/-- `supports_password_hash`: `mysql_native_password`, `client_ed25519` and `parsec` (documented: deterministic password hashing). -/
theorem packets.AuthPlugin.supports_password_hash_spec (self : packets.AuthPlugin) :
    packets.AuthPlugin.supports_password_hash self ⦃ b =>
      b = (match self with | .MysqlNativePassword | .Ed25519 | .Parsec => true | _ => false) ⦄ := by
  sorry

end mysql_common
