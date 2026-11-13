import Defs

/-! Statements for `struct ComChangeUser and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `new`: empty user, auth data and database, no tail. -/
theorem packets.ComChangeUser.new_spec :
    packets.ComChangeUser.new ⦃ p => ChangeUser.of p = ⟨[], [], [], none⟩ ⦄ := by
  sorry

/-- `with_user`: the given user (converted with `into`), or empty for `None`. -/
theorem packets.ComChangeUser.with_user_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (self : packets.ComChangeUser) (user : Option T1)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : ∀ x, user = some x → into.into x = ok c) :
    packets.ComChangeUser.with_user into self user ⦃ p =>
      ChangeUser.of p = { ChangeUser.of self with user := (user.map (fun _ => cowList c)).getD [] } ∧
        p.more_data = self.more_data ⦄ := by
  sorry

/-- `with_database`: the given database (converted with `into`), or empty for `None`. -/
theorem packets.ComChangeUser.with_database_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (self : packets.ComChangeUser) (database : Option T1)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : ∀ x, database = some x → into.into x = ok c) :
    packets.ComChangeUser.with_database into self database ⦃ p =>
      ChangeUser.of p = { ChangeUser.of self with database := (database.map (fun _ => cowList c)).getD [] } ∧
        p.more_data = self.more_data ⦄ := by
  sorry

/-- `with_auth_plugin_data`: the given auth data (converted with `into`), or empty for `None`. -/
theorem packets.ComChangeUser.with_auth_plugin_data_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (self : packets.ComChangeUser) (auth_plugin_data : Option T1)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : ∀ x, auth_plugin_data = some x → into.into x = ok c) :
    packets.ComChangeUser.with_auth_plugin_data into self auth_plugin_data ⦃ p =>
      ChangeUser.of p = { ChangeUser.of self with authData := (auth_plugin_data.map (fun _ => cowList c)).getD [] } ∧
        p.more_data = self.more_data ⦄ := by
  sorry

/-- `with_more_data`: replaces the tail. -/
theorem packets.ComChangeUser.with_more_data_eq (self : packets.ComChangeUser) (more_data : Option packets.ComChangeUserMoreData) :
    packets.ComChangeUser.with_more_data self more_data = ok { self with more_data := more_data } := by
  sorry

/-- `into_owned`: the same fields; plugins stay known or `Other`, maps become `connectAttrsIntoOwned` of themselves. -/
theorem packets.ComChangeUser.into_owned_spec (self : packets.ComChangeUser) :
    packets.ComChangeUser.into_owned self ⦃ p =>
      ChangeUser.of p = ChangeUser.of self ∧
        p.more_data.map (fun m => (m.auth_plugin.map isOtherPlugin, m.connect_attributes)) =
          self.more_data.map (fun m => (m.auth_plugin.map isOtherPlugin,
            m.connect_attributes.map Trusted.connectAttrsIntoOwned)) ⦄ := by
  sorry

/-- `Default`: `new()`. -/
theorem packets.ComChangeUser.Insts.CoreDefaultDefault.default_spec :
    packets.ComChangeUser.Insts.CoreDefaultDefault.default ⦃ p => ChangeUser.of p = ⟨[], [], [], none⟩ ⦄ := by
  sorry

/-- `MyDeserialize for ComChangeUser`: `SIZE` is `None`. -/
theorem packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq :
    packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE = none := by
  sorry

/-- `MyDeserialize for ComChangeUser`: total; `changeUserRead` with the capability flags (the fields, the tail's plugin in normal form and its map built from the wire entries; errors; what is left). -/
theorem packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      optMatch (fun p vk => ChangeUser.Matches p vk.1 vk.2) (okPart r) (changeUserRead caps.val buf.val).1 ∧
        rest.val = (changeUserRead caps.val buf.val).2 ⦄ := by
  sorry

/-- `MySerialize for ComChangeUser`: appends `changeUserEnc` of the fields, with the entries of the tail's map in its iteration order (none if it has no map: the crate writes an empty map, whose attributes are the single byte `0` by `Trusted.connectAttrsEntries_new`). -/
theorem packets.ComChangeUser.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ComChangeUser) (buf : alloc.vec.Vec U8)
    (h : buf.length + (changeUserEnc (ChangeUser.of self) (((self.more_data.bind (·.connect_attributes)).map attrsEntries).getD [])).length ≤ Usize.max) :
    packets.ComChangeUser.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ changeUserEnc (ChangeUser.of self) (((self.more_data.bind (·.connect_attributes)).map attrsEntries).getD []) ⦄ := by
  sorry

/-- Round trip: a `ChangeUser.Compatible` request written by `changeUserEnc` reads back with the same fields, its tail's map built from the written entries. Without a tail nothing may follow (any byte would be read as a tail). -/
theorem packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip (h64 : Target64) (caps : constants.CapabilityFlags) (v : ChangeUser) (kvs : List (List U8 × List U8))
    (hc : ChangeUser.Compatible caps.val v) (tail : List U8) (ht : v.moreData = none → tail = [])
    (buf : io.ParseBuf) (h : buf.val = changeUserEnc v kvs ++ tail) :
    packets.ComChangeUser.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      (∃ p, okPart r = some p ∧ ChangeUser.Matches p v (v.moreData.map (fun _ => kvs))) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
