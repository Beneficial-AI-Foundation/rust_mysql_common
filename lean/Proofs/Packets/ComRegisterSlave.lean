import Defs
import Proofs.Util.PacketsOkErr
import Proofs.Util.PacketsColStmt
import Proofs.Misc.Raw.Bytes.U8Bytes
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Defs.LemmasG
import Proofs.Util.Shared
import Proofs.Util.Replication

/-! Statements for `struct ComRegisterSlave and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts mysql_common.PCSUtil mysql_common.Shared

namespace mysql_common

attribute [local step] constu8_default_spec rawint_u16_default_spec rawint_u32_default_spec

private theorem parse_unchecked_hdr_spec (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple
        21#u8 packets.InvalidComRegisterSlaveHeader.Insts.CoreErrorError
        packets.InvalidComRegisterSlaveHeader.Insts.CoreDefaultDefault) buf () ⦃ r rest =>
      ((okPart r).isSome ↔ leNat (buf.val.take 1) = 21) ∧ rest.val = buf.val.drop 1 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  exact misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec 21#u8
    packets.InvalidComRegisterSlaveHeader.Insts.CoreErrorError
    packets.InvalidComRegisterSlaveHeader.Insts.CoreDefaultDefault
    ((WP.spec_ok _).mpr trivial) buf h

/-- `ComRegisterSlave::new(server_id)`: the server id; the strings empty, the numbers 0. -/
theorem packets.ComRegisterSlave.new_spec (server_id : U32) :
    packets.ComRegisterSlave.new server_id ⦃ p =>
      RegSlave.of p = ⟨server_id.val, [], [], [], 0, 0, 0⟩ ⦄ := by
  unfold packets.ComRegisterSlave.new
  step*
  simp_all [RegSlave.of]

/-- `with_hostname`: sets the host name (`hostname.into()`, not truncated: serialization
    truncates); nothing else changes. -/
theorem packets.ComRegisterSlave.with_hostname_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComRegisterSlave) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComRegisterSlave.with_hostname into self x ⦃ p =>
      RegSlave.of p = { RegSlave.of self with hostname := cowList c } ⦄ := by
  unfold packets.ComRegisterSlave.with_hostname
  step*
  simp_all [RegSlave.of]

/-- `with_user`: sets the user; nothing else changes. -/
theorem packets.ComRegisterSlave.with_user_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComRegisterSlave) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComRegisterSlave.with_user into self x ⦃ p =>
      RegSlave.of p = { RegSlave.of self with user := cowList c } ⦄ := by
  unfold packets.ComRegisterSlave.with_user
  step*
  simp_all [RegSlave.of]

/-- `with_password`: sets the password; nothing else changes. -/
theorem packets.ComRegisterSlave.with_password_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComRegisterSlave) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComRegisterSlave.with_password into self x ⦃ p =>
      RegSlave.of p = { RegSlave.of self with password := cowList c } ⦄ := by
  unfold packets.ComRegisterSlave.with_password
  step*
  simp_all [RegSlave.of]

/-- `with_port`: sets the port; nothing else changes. -/
theorem packets.ComRegisterSlave.with_port_spec (self : packets.ComRegisterSlave) (port : U16) :
    packets.ComRegisterSlave.with_port self port ⦃ p =>
      RegSlave.of p = { RegSlave.of self with port := port.val } ⦄ := by
  unfold packets.ComRegisterSlave.with_port
  step*
  simp_all [RegSlave.of]

/-- `with_replication_rank`: sets the replication rank; nothing else changes. -/
theorem packets.ComRegisterSlave.with_replication_rank_spec (self : packets.ComRegisterSlave)
    (replication_rank : U32) :
    packets.ComRegisterSlave.with_replication_rank self replication_rank ⦃ p =>
      RegSlave.of p = { RegSlave.of self with rank := replication_rank.val } ⦄ := by
  unfold packets.ComRegisterSlave.with_replication_rank
  step*
  simp_all [RegSlave.of]

/-- `with_master_id`: sets the master id; nothing else changes. -/
theorem packets.ComRegisterSlave.with_master_id_spec (self : packets.ComRegisterSlave) (master_id : U32) :
    packets.ComRegisterSlave.with_master_id self master_id ⦃ p =>
      RegSlave.of p = { RegSlave.of self with masterId := master_id.val } ⦄ := by
  unfold packets.ComRegisterSlave.with_master_id
  step*
  simp_all [RegSlave.of]

/-- `server_id`: the field. -/
theorem packets.ComRegisterSlave.impl.server_id_eq (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.server_id self = ok self.server_id.1 := by
  rfl

/-- `hostname_raw`: the host name's effective bytes (at most the first 255). -/
theorem packets.ComRegisterSlave.hostname_raw_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.hostname_raw self ⦃ s => s.val = (cowList self.hostname.1).take 255 ⦄ :=
  u8bytes_as_bytes_spec _

/-- `hostname`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComRegisterSlave.impl.hostname_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.hostname self ⦃ c => LossyUtf8Valid ((cowList self.hostname.1).take 255) c ⦄ :=
  u8bytes_as_str_spec _

/-- `user_raw`: the user's effective bytes (at most the first 255). -/
theorem packets.ComRegisterSlave.user_raw_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.user_raw self ⦃ s => s.val = (cowList self.user.1).take 255 ⦄ :=
  u8bytes_as_bytes_spec _

/-- `user`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComRegisterSlave.impl.user_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.user self ⦃ c => LossyUtf8Valid ((cowList self.user.1).take 255) c ⦄ :=
  u8bytes_as_str_spec _

/-- `password_raw`: the password's effective bytes (at most the first 255). -/
theorem packets.ComRegisterSlave.password_raw_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.password_raw self ⦃ s => s.val = (cowList self.password.1).take 255 ⦄ :=
  u8bytes_as_bytes_spec _

/-- `password`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.ComRegisterSlave.impl.password_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.password self ⦃ c => LossyUtf8Valid ((cowList self.password.1).take 255) c ⦄ :=
  u8bytes_as_str_spec _

/-- `port`: the field. -/
theorem packets.ComRegisterSlave.impl.port_eq (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.port self = ok self.port.1 := by
  rfl

/-- `replication_rank`: the field. -/
theorem packets.ComRegisterSlave.impl.replication_rank_eq (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.replication_rank self = ok self.replication_rank.1 := by
  rfl

/-- `master_id`: the field. -/
theorem packets.ComRegisterSlave.impl.master_id_eq (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.master_id self = ok self.master_id.1 := by
  rfl

/-- `MySerialize for ComRegisterSlave`: appends the protocol's packet `regSlaveEnc`, the strings
    truncated to 255 bytes (documented). -/
theorem packets.ComRegisterSlave.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComRegisterSlave) (buf : alloc.vec.Vec U8)
    (h : buf.length + (regSlaveEnc (RegSlave.of self)).length ≤ Usize.max) :
    packets.ComRegisterSlave.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ regSlaveEnc (RegSlave.of self) ⦄ := by
  unfold packets.ComRegisterSlave.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [regSlaveEnc, RegSlave.of, List.length_cons, List.length_append, PBUtil.length_leBytes, vec_len] at h
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨b1, h1⟩
  step with rawint_u32_serialize as ⟨b2, h2⟩
  · simp [alloc.vec.Vec.length, h1] at *; omega
  step with u8bytes_ser as ⟨b3, h3⟩
  · simp [alloc.vec.Vec.length, h1, h2] at *; omega
  step with u8bytes_ser as ⟨b4, h4⟩
  · simp [alloc.vec.Vec.length, h1, h2, h3] at *; omega
  step with u8bytes_ser as ⟨b5, h5⟩
  · simp [alloc.vec.Vec.length, h1, h2, h3, h4] at *; omega
  step with rawint_u16_serialize as ⟨b6, h6⟩
  · simp [alloc.vec.Vec.length, h1, h2, h3, h4, h5] at *; omega
  step with rawint_u32_serialize as ⟨b7, h7⟩
  · simp [alloc.vec.Vec.length, h1, h2, h3, h4, h5, h6] at *; omega
  apply WP.spec_mono (rawint_u32_serialize _ _ (by
    simp [alloc.vec.Vec.length, h1, h2, h3, h4, h5, h6, h7] at *; omega))
  intro b hb
  rw [hb, h7, h6, h5, h4, h3, h2, h1]
  simp [regSlaveEnc, RegSlave.of]
  rfl

/-- `MyDeserialize for ComRegisterSlave`: `SIZE` is `None`. -/
theorem packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  simp [packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for ComRegisterSlave`: total; `regSlaveRead`. -/
theorem packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map RegSlave.of, rest.val) = regSlaveRead buf.val ⦄ := by
  unfold packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize regSlaveRead
  step with parse_usize_spec as ⟨r, buf1, h1⟩
  split_ifs at h1 with hl
  · obtain ⟨h1a, h1b⟩ := h1
    have hl' : (↑buf : List U8).length ≥ 5 := hl
    rw [ite_eq_right (by omega)]
    obtain ⟨a0, a1, a2, a3, a4, rest, hbuf⟩ :
        ∃ a0 a1 a2 a3 a4 rest, (↑buf : List U8) = a0 :: a1 :: a2 :: a3 :: a4 :: rest := by
      match h : (↑buf : List U8), hl' with
      | a0 :: a1 :: a2 :: a3 :: a4 :: rest, _ => exact ⟨a0, a1, a2, a3, a4, rest, rfl⟩
    rw [hbuf] at h1a h1b ⊢
    cases r with
    | Err e => simp at h1a
    | Ok pb =>
      simp at h1a h1b
      simp only [CoreOpsTry.branch, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
        List.take_zero, List.getD_cons_zero]
      step with parse_unchecked_hdr_spec as ⟨r1, sbuf, h2a, h2b⟩
      rw [h1a] at h2a h2b
      simp [leNat] at h2a h2b
      cases r1 with
      | Err e =>
        have ha : a0.val ≠ 0x15 := by intro h; simp [h] at h2a
        rw [ite_eq_left ha, ← h1b]
        simp [CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok hd =>
        have ha : a0.val = 0x15 := by simpa using h2a
        rw [ite_eq_right (by simp [ha])]
        simp only
        step with parse_unchecked_leu32_spec as ⟨r2, sbuf2, h3a, h3b⟩
        · simp [Slice.length, h2b]
        cases r2 with
        | Err e => simp at h3a
        | Ok sidv =>
        simp only [okPart_Ok, Option.map_some, Option.some.injEq, h2b] at h3a
        simp only
        step with parse_u8bytes_spec as ⟨r3, buf2, h4⟩
        rw [h1b] at h4
        rw [← h4]
        cases r3 with
        | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok rb =>
        simp only [okPart_Ok, Option.map_some]
        step with parse_u8bytes_spec as ⟨r4, buf3, h5⟩
        rw [← h5]
        cases r4 with
        | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok rb1 =>
        simp only [okPart_Ok, Option.map_some]
        step with parse_u8bytes_spec as ⟨r5, buf4, h6⟩
        rw [← h6]
        cases r5 with
        | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok rb2 =>
        simp only [okPart_Ok, Option.map_some]
        step with parse_usize_spec as ⟨r6, buf5, h7⟩
        split_ifs at h7 with hl2
        · obtain ⟨h7a, h7b⟩ := h7
          rw [ite_eq_right (by simp only [Slice.length] at hl2; omega)]
          cases r6 with
          | Err e => simp at h7a
          | Ok pb1 =>
          simp only [okPart_Ok, Option.map_some, Option.some.injEq] at h7a
          step with parse_unchecked_leu16_spec as ⟨r7, sbuf3, h8a, h8b⟩
          cases r7 with
          | Err e => simp at h8a
          | Ok portv =>
          simp only
          step with parse_unchecked_leu32_spec as ⟨r8, sbuf4, h9a, h9b⟩
          · simp only [Slice.length] at hl2 ⊢; simp [h8b, h7a]; omega
          cases r8 with
          | Err e => simp at h9a
          | Ok rankv =>
          simp only
          step with parse_unchecked_leu32_spec as ⟨r9, sbuf5, h10a, h10b⟩
          · simp only [Slice.length] at hl2 ⊢; simp [h9b, h8b, h7a]; omega
          cases r9 with
          | Err e => simp at h10a
          | Ok midv =>
          simp only [okPart_Ok, Option.map_some, Option.some.injEq, h9b, h8b, h7a] at h8a h9a h10a
          simp [RegSlave.of, h3a, h8a, h9a, h10a, h7b, leNat, List.take_take, List.drop_take]
        · obtain ⟨h7a, rfl⟩ := h7
          rw [ite_eq_left (by simp only [Slice.length] at hl2; omega)]
          cases r6 with
          | Ok _ => simp at h7a
          | Err e => simp [CoreOpsTry_traitFromResidualResult.from_residual]
  · obtain ⟨h1a, rfl⟩ := h1
    rw [ite_eq_left (by simp only [Slice.length] at hl; omega)]
    cases r with
    | Ok _ => simp at h1a
    | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]

/-- Round trip: a packet with strings of at most 255 bytes, in the protocol layout, is read
    back. -/
theorem packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (p : packets.ComRegisterSlave)
    (h255 : (RegSlave.of p).hostname.length ≤ 255 ∧ (RegSlave.of p).user.length ≤ 255 ∧
      (RegSlave.of p).password.length ≤ 255)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = regSlaveEnc (RegSlave.of p) ++ tail) :
    packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map RegSlave.of = some (RegSlave.of p) ∧ rest.val = tail ⦄ := by
  apply WP.spec_mono (packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  rw [h, Replication.regSlaveRead_regSlaveEnc _ ⟨by simp [RegSlave.of]; scalar_tac, h255.1, h255.2.1, h255.2.2,
    by simp [RegSlave.of]; scalar_tac, by simp [RegSlave.of]; scalar_tac, by simp [RegSlave.of]; scalar_tac⟩] at hr
  simpa only [Prod.mk.injEq] using hr

end mysql_common
