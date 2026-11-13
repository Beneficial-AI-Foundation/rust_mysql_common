import Defs

/-! Statements for `struct ComRegisterSlave and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ComRegisterSlave::new(server_id)`: the server id; the strings empty, the numbers 0. -/
theorem packets.ComRegisterSlave.new_spec (server_id : U32) :
    packets.ComRegisterSlave.new server_id ⦃ p =>
      RegSlave.of p = ⟨server_id.val, [], [], [], 0, 0, 0⟩ ⦄ := by
  sorry

/-- `with_hostname`: sets the host name (`hostname.into()`, not truncated: serialization
    truncates); nothing else changes. -/
theorem packets.ComRegisterSlave.with_hostname_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComRegisterSlave) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComRegisterSlave.with_hostname into self x ⦃ p =>
      RegSlave.of p = { RegSlave.of self with hostname := cowList c } ⦄ := by
  sorry

/-- `with_user`: sets the user; nothing else changes. -/
theorem packets.ComRegisterSlave.with_user_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComRegisterSlave) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComRegisterSlave.with_user into self x ⦃ p =>
      RegSlave.of p = { RegSlave.of self with user := cowList c } ⦄ := by
  sorry

/-- `with_password`: sets the password; nothing else changes. -/
theorem packets.ComRegisterSlave.with_password_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComRegisterSlave) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComRegisterSlave.with_password into self x ⦃ p =>
      RegSlave.of p = { RegSlave.of self with password := cowList c } ⦄ := by
  sorry

/-- `with_port`: sets the port; nothing else changes. -/
theorem packets.ComRegisterSlave.with_port_spec (self : packets.ComRegisterSlave) (port : U16) :
    packets.ComRegisterSlave.with_port self port ⦃ p =>
      RegSlave.of p = { RegSlave.of self with port := port.val } ⦄ := by
  sorry

/-- `with_replication_rank`: sets the replication rank; nothing else changes. -/
theorem packets.ComRegisterSlave.with_replication_rank_spec (self : packets.ComRegisterSlave)
    (replication_rank : U32) :
    packets.ComRegisterSlave.with_replication_rank self replication_rank ⦃ p =>
      RegSlave.of p = { RegSlave.of self with rank := replication_rank.val } ⦄ := by
  sorry

/-- `with_master_id`: sets the master id; nothing else changes. -/
theorem packets.ComRegisterSlave.with_master_id_spec (self : packets.ComRegisterSlave) (master_id : U32) :
    packets.ComRegisterSlave.with_master_id self master_id ⦃ p =>
      RegSlave.of p = { RegSlave.of self with masterId := master_id.val } ⦄ := by
  sorry

/-- `server_id`: the field. -/
theorem packets.ComRegisterSlave.impl.server_id_eq (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.server_id self = ok self.server_id.1 := by
  sorry

/-- `hostname_raw`: the host name's effective bytes (at most the first 255). -/
theorem packets.ComRegisterSlave.hostname_raw_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.hostname_raw self ⦃ s => s.val = (cowList self.hostname.1).take 255 ⦄ := by
  sorry

/-- `hostname`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComRegisterSlave.impl.hostname_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.hostname self ⦃ c => LossyUtf8Valid ((cowList self.hostname.1).take 255) c ⦄ := by
  sorry

/-- `user_raw`: the user's effective bytes (at most the first 255). -/
theorem packets.ComRegisterSlave.user_raw_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.user_raw self ⦃ s => s.val = (cowList self.user.1).take 255 ⦄ := by
  sorry

/-- `user`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComRegisterSlave.impl.user_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.user self ⦃ c => LossyUtf8Valid ((cowList self.user.1).take 255) c ⦄ := by
  sorry

/-- `password_raw`: the password's effective bytes (at most the first 255). -/
theorem packets.ComRegisterSlave.password_raw_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.password_raw self ⦃ s => s.val = (cowList self.password.1).take 255 ⦄ := by
  sorry

/-- `password`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComRegisterSlave.impl.password_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.password self ⦃ c => LossyUtf8Valid ((cowList self.password.1).take 255) c ⦄ := by
  sorry

/-- `port`: the field. -/
theorem packets.ComRegisterSlave.impl.port_eq (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.port self = ok self.port.1 := by
  sorry

/-- `replication_rank`: the field. -/
theorem packets.ComRegisterSlave.impl.replication_rank_eq (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.replication_rank self = ok self.replication_rank.1 := by
  sorry

/-- `master_id`: the field. -/
theorem packets.ComRegisterSlave.impl.master_id_eq (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.master_id self = ok self.master_id.1 := by
  sorry

/-- `MySerialize for ComRegisterSlave`: appends the protocol's packet `regSlaveEnc`, the strings
    truncated to 255 bytes (documented). -/
theorem packets.ComRegisterSlave.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComRegisterSlave) (buf : alloc.vec.Vec U8)
    (h : buf.length + (regSlaveEnc (RegSlave.of self)).length ≤ Usize.max) :
    packets.ComRegisterSlave.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ regSlaveEnc (RegSlave.of self) ⦄ := by
  sorry

/-- `MyDeserialize for ComRegisterSlave`: `SIZE` is `None`. -/
theorem packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for ComRegisterSlave`: total; `regSlaveRead`. -/
theorem packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map RegSlave.of, rest.val) = regSlaveRead buf.val ⦄ := by
  sorry

/-- Round trip: a packet with strings of at most 255 bytes, in the protocol layout, is read
    back. -/
theorem packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (p : packets.ComRegisterSlave)
    (h255 : (RegSlave.of p).hostname.length ≤ 255 ∧ (RegSlave.of p).user.length ≤ 255 ∧
      (RegSlave.of p).password.length ≤ 255)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = regSlaveEnc (RegSlave.of p) ++ tail) :
    packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map RegSlave.of = some (RegSlave.of p) ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
