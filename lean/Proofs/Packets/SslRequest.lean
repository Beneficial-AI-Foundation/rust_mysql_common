import Defs
import Proofs.Util.ConnHandshake

/-! Statements for `struct SslRequest and its impls` (spec file: `Specs/Packets/Connection.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil mysql_common.ConnHSUtil
open core.result.Result.Insts

namespace mysql_common

/-- `new`: the given fields, MariaDB's capabilities empty. -/
theorem packets.SslRequest.new_spec (capabilities : constants.CapabilityFlags) (max_packet_size : U32) (character_set : U8) :
    packets.SslRequest.new capabilities max_packet_size character_set ⦃ p =>
      SslReq.of p = ⟨capabilities.val, max_packet_size.val, character_set.val, 0⟩ ⦄ := by
  unfold packets.SslRequest.new
  simp only [constants.MariadbCapabilities.empty, bind_ok]
  step*
  simp_all [SslReq.of]

/-- `with_mariadb_capabilities`: replaces MariaDB's capabilities. -/
theorem packets.SslRequest.with_mariadb_capabilities_spec (self : packets.SslRequest) (mariadb_capabilities : constants.MariadbCapabilities) :
    packets.SslRequest.with_mariadb_capabilities self mariadb_capabilities ⦃ p =>
      SslReq.of p = { SslReq.of self with mariadbCaps := mariadb_capabilities.val } ⦄ := by
  rcases self with ⟨c, m, ch, sk, ⟨mc, pd⟩⟩
  simp [packets.SslRequest.with_mariadb_capabilities, SslReq.of]

/-- `capabilities`: the field. -/
theorem packets.SslRequest.impl.capabilities_eq (self : packets.SslRequest) :
    packets.SslRequest.impl.capabilities self = ok self.capabilities.1 := by
  rfl

/-- `max_packet_size`: the field. -/
theorem packets.SslRequest.impl.max_packet_size_eq (self : packets.SslRequest) :
    packets.SslRequest.impl.max_packet_size self = ok self.max_packet_size.1 := by
  rfl

/-- `character_set`: the field. -/
theorem packets.SslRequest.impl.character_set_eq (self : packets.SslRequest) :
    packets.SslRequest.impl.character_set self = ok self.character_set.1 := by
  rfl

/-- `MyDeserialize for SslRequest`: `SIZE` is `Some(32)`. -/
theorem packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = ok (some 32#usize) := by
  have h : packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE ⦃ r => r = some 32#usize ⦄ := by
    unfold packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE
    step*
    simp only [Option.some.injEq]
    apply UScalar.eq_of_val_eq
    simp_all
  obtain ⟨v, hv, rfl⟩ := spec_eq_ok h
  exact hv

/-- `MyDeserialize for SslRequest`: total; `sslRequestRead`. -/
theorem packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => ((okPart r).map SslReq.of, rest.val) = sslRequestRead buf.val ⦄ := by
  unfold packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize sslRequestRead
  rw [packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq]
  simp only [bind_ok, core.option.Option.unwrap, ofOption]
  step with parse_usize_spec as ⟨r, buf1, h1⟩
  split_ifs at h1 with hl
  · obtain ⟨h1a, h1b⟩ := h1
    have hl' : 32 ≤ buf.val.length := hl
    rw [ite_eq_right (by omega)]
    cases r with
    | Err e => simp at h1a
    | Ok pb =>
      have hpb : pb.val = buf.val.take 32 := by simpa [okPart] using h1a
      step as ⟨sb, hsb⟩
      subst hsb
      step with pu_rawconst_leu32 as ⟨r1, s1, h2a, h2b⟩
      cases r1 with
      | Err e => simp [okPart] at h2a
      | Ok v1 =>
      step*
      obtain ⟨i1, ph⟩ := val
      rename_i hv1
      rw [cf1_post] at hv1
      have e1 : v1 = (i1, ph) := by injection hv1
      subst e1
      step*
      step with pu_rawint_leu32 as ⟨r2, s2, h3a, h3b⟩
      · simp [Slice.length, h2b, hpb]; omega
      cases r2 with
      | Err e => simp [okPart] at h3a
      | Ok v2 =>
      step*
      step with parse_unchecked_u8_spec as ⟨r3, s3, h4a, h4b⟩
      · simp [Slice.length, h3b, h2b, hpb]; omega
      cases r3 with
      | Err e => simp [okPart] at h4a
      | Ok v3 =>
      step*
      step with pu_skip as ⟨r4, s4, h5a, h5b⟩
      · simp [Slice.length, h4b, h3b, h2b, hpb]; omega
      cases r4 with
      | Err e => simp [okPart] at h5a
      | Ok v4 =>
      step*
      step with pu_rawconst_leu32 as ⟨r5, s5, h6a, h6b⟩
      · simp [Slice.length, h5b, h4b, h3b, h2b, hpb]; omega
      cases r5 with
      | Err e => simp [okPart] at h6a
      | Ok v5 =>
      step*
      obtain ⟨i2, ph2⟩ := val4
      rename_i hv5
      rw [cf6_post] at hv5
      have e5 : v5 = (i2, ph2) := by injection hv5
      subst e5
      step*
      subst_vars
      simp only [core.ops.control_flow.ControlFlow.Continue.injEq] at *
      subst_vars
      simp only [okPart, Option.map_some, Option.some.injEq] at *
      refine ⟨?_, h1b⟩
      have e2 : i1.val = leNat (List.take 4 pb.val) := Option.some.inj h2a
      have e6 : i2.val = leNat (List.take 4 s4.val) := Option.some.inj h6a
      have hi1 : i1.val < 2 ^ 32 := by scalar_tac
      rw [e2] at hi1
      simp only [SslReq.of, SslReq.mk.injEq, cf2_post, mc_post, e2, e6, h3a, h4a, and_all32 _ hi1]
      simp only [h5b, h4b, h3b, h2b, hpb, List.drop_drop, List.drop_take, List.take_take, List.drop_zero]
      simp
  · obtain ⟨h1a, rfl⟩ := h1
    rw [ite_eq_left (by simp only [Slice.length] at hl; omega)]
    cases r with
    | Ok _ => simp at h1a
    | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]

/-- `MySerialize for SslRequest`: appends `sslRequestEnc` of the fields. -/
theorem packets.SslRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.SslRequest) (buf : alloc.vec.Vec U8) (h : buf.length + 32 ≤ Usize.max) :
    packets.SslRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ sslRequestEnc (SslReq.of self) ⦄ := by
  unfold packets.SslRequest.Insts.Mysql_commonProtoMySerialize.serialize
  have hl : buf.val.length + 32 ≤ Usize.max := h
  step*
  all_goals simp_all [alloc.vec.Vec.length, PBUtil.length_leBytes, sslRequestEnc, SslReq.of]
  all_goals omega

/-- Round trip, for fields that fit and known MariaDB bits. -/
theorem packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (v : SslReq) (hv : v.caps < 2 ^ 32 ∧ v.maxPacket < 2 ^ 32 ∧ v.charset < 256 ∧
      v.mariadbCaps &&& mariadbCapabilitiesAll = v.mariadbCaps)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = sslRequestEnc v ++ tail) :
    packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest => (okPart r).map SslReq.of = some v ∧ rest.val = tail ⦄ := by
  apply WP.spec_mono (packets.SslRequest.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  rw [h, sslRequestRead_enc v hv tail] at hr
  simp only [Prod.mk.injEq] at hr
  exact hr

end mysql_common
