import Defs
import Proofs.Util.ConnAuth

/-! Statements for `enum AuthPlugin and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.CAUtil

namespace mysql_common

/-- `MyDeserialize for AuthPlugin`: `SIZE` is `None`. -/
theorem packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  simp [packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for AuthPlugin`: never an error; the plugin named by the whole buffer (without one trailing `0`), which is consumed. -/
theorem packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (∃ p, okPart r = some p ∧ PluginFromBytes buf.val p) ∧ rest.val = [] ⦄ := by
  exact authplugin_deserialize_spec' buf

/-- `MySerialize for AuthPlugin`: appends the name and `0` (a `string<NUL>`; the name is not cut at an inner `0`). -/
theorem packets.AuthPlugin.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.AuthPlugin) (buf : alloc.vec.Vec U8)
    (h : buf.length + (authPluginName self).length + 1 ≤ Usize.max) :
    packets.AuthPlugin.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ authPluginName self ++ [byte 0] ⦄ := by
  unfold packets.AuthPlugin.Insts.Mysql_commonProtoMySerialize.serialize
  step with as_bytes_spec' as ⟨s, hs⟩
  step with IntAndMisc.put_slice_spec as ⟨buf1, h1⟩
  step with PKUtil.put_u8_spec as ⟨buf2, h2⟩
  simp [h2, h1, hs, byte]; rfl

/-- Round trip: a serialized plugin reads back as the plugin of the same name, in normal form (`Other` holding a known name comes back as that known plugin). -/
theorem packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (p : packets.AuthPlugin) (buf : io.ParseBuf) (h : buf.val = authPluginName p ++ [byte 0]) :
    packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (∃ q, okPart r = some q ∧ IsPluginNamed (authPluginName p) q) ∧ rest.val = [] ⦄ := by
  apply WP.spec_mono (packets.AuthPlugin.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ ⟨⟨q, hq, hp⟩, hr⟩
  refine ⟨⟨q, hq, ?_⟩, hr⟩
  have := CAUtil.PluginFromBytes.isPluginNamed hp
  rwa [h, dropTrailingNul_append_zero] at this

/-- `from_bytes`: the known plugin with that name (one trailing `0` removed first), else `Other` borrowing the name. -/
theorem packets.AuthPlugin.from_bytes_spec (nm : Slice U8) :
    packets.AuthPlugin.from_bytes nm ⦃ r => PluginFromBytes nm.val r ⦄ := by
  exact from_bytes_spec' nm

/-- `as_bytes`: the plugin's name. -/
theorem packets.AuthPlugin.as_bytes_spec (self : packets.AuthPlugin) :
    packets.AuthPlugin.as_bytes self ⦃ s => s.val = authPluginName self ⦄ := by
  exact as_bytes_spec' self

/-- `into_owned`: the same plugin; `Other` with an owned copy of its name. -/
theorem packets.AuthPlugin.into_owned_spec (self : packets.AuthPlugin) :
    packets.AuthPlugin.into_owned self ⦃ r =>
      match self with
      | .Other c => ∃ v : alloc.vec.Vec U8, r = .Other (.Owned v) ∧ v.val = cowList c
      | p => r = p ⦄ := by
  unfold packets.AuthPlugin.into_owned
  cases self <;> simp
  step with cow_into_vec_spec as ⟨v, hv⟩
  simp [hv]

/-- `borrow`: the same plugin; `Other` borrowing its name. -/
theorem packets.AuthPlugin.borrow_spec (self : packets.AuthPlugin) :
    packets.AuthPlugin.borrow self ⦃ r =>
      match self with
      | .Other c => ∃ s : Slice U8, r = .Other (.Borrowed s) ∧ s.val = cowList c
      | p => r = p ⦄ := by
  unfold packets.AuthPlugin.borrow
  cases self <;> simp
  step with cow_as_ref_spec as ⟨s, hs⟩
  simp [hs]

/-- `supports_password_hash`: `mysql_native_password`, `client_ed25519` and `parsec` (documented: deterministic password hashing). -/
theorem packets.AuthPlugin.supports_password_hash_spec (self : packets.AuthPlugin) :
    packets.AuthPlugin.supports_password_hash self ⦃ b =>
      b = (match self with | .MysqlNativePassword | .Ed25519 | .Parsec => true | _ => false) ⦄ := by
  cases self <;> simp [packets.AuthPlugin.supports_password_hash]

end mysql_common
