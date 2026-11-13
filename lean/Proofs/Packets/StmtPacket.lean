import Defs
import Proofs.Util.PacketsColStmt
import Proofs.Io.ParseBuf
import Proofs.Misc.Raw.Int.RawInt
import Proofs.Misc.Raw.Int.ConstU8
import Proofs.Misc.Raw.Int.LeU16
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Misc.Raw.Skip
import Proofs.Defs.LemmasStmtSession

/-! Statements for `struct StmtPacket and its impls` (spec file: `Specs/Packets/StmtBinlog.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PCSUtil

namespace mysql_common

@[local step]
private theorem branch_spec_stmt {T E : Type} (r : core.result.Result T E) :
    core.result.Result.Insts.CoreOpsTry.branch r ⦃ cf =>
      (∀ v, cf = .Continue v → r = .Ok v) ∧
      (∀ res, cf = .Break res → ∃ e, r = .Err e ∧ res = .Err e) ⦄ :=
  mysql_common.PCSUtil.branch_spec' r

private theorem d_status (buf : io.ParseBuf) (x : U8) (t : List U8) (hb : buf.val = x :: t) :
    misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize 0#u8
      packets.InvalidStmtPacketStatus.Insts.CoreErrorError
      packets.InvalidStmtPacketStatus.Insts.CoreDefaultDefault () buf ⦃ r rest =>
      ((okPart r).isSome ↔ x.val = 0) ∧ rest.val = t ⦄ := by
  apply WP.spec_mono (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec _ _ _
    (by simp [packets.InvalidStmtPacketStatus.Insts.CoreDefaultDefault.default]) buf (by simp [hb]))
  rintro ⟨r, rest⟩ h
  simp_all [WP.uncurry', leNat]

private theorem d_u16 (buf : io.ParseBuf) (x y : U8) (t : List U8) (hb : buf.val = x :: y :: t) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 () buf ⦃ r rest =>
      (okPart r).map (·.1.val) = some (leNat [x, y]) ∧ rest.val = t ⦄ := by
  have := misc.raw.int.RawInt.deserialize_spec misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 buf
    (fun (o : Option U16) (rest : io.ParseBuf) => o.map (fun v : U16 => v.val) = some (leNat [x, y]) ∧ rest.val = t)
    (by
      apply WP.spec_mono (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec buf (by simp [hb]))
      rintro ⟨r, rest⟩ h
      simp_all [WP.uncurry'])
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ h
  simp_all [WP.uncurry', Option.map_map, Function.comp_def]

private theorem d_u32 (buf : io.ParseBuf) (x0 x1 x2 x3 : U8) (t : List U8) (hb : buf.val = x0 :: x1 :: x2 :: x3 :: t) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 () buf ⦃ r rest =>
      (okPart r).map (·.1.val) = some (leNat [x0, x1, x2, x3]) ∧ rest.val = t ⦄ := by
  have := misc.raw.int.RawInt.deserialize_spec misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 buf
    (fun (o : Option U32) (rest : io.ParseBuf) => o.map (fun v : U32 => v.val) = some (leNat [x0, x1, x2, x3]) ∧ rest.val = t)
    (by
      apply WP.spec_mono (misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec buf (by simp [hb]))
      rintro ⟨r, rest⟩ h
      simp_all [WP.uncurry'])
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ h
  simp_all [WP.uncurry', Option.map_map, Function.comp_def]

private theorem d_skip1 (buf : io.ParseBuf) (x : U8) (t : List U8) (hb : buf.val = x :: t) :
    misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize 1#usize () buf ⦃ r rest =>
      (okPart r).isSome ∧ rest.val = t ⦄ := by
  apply WP.spec_mono (misc.raw.Skip.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec _ buf (by simp [hb]))
  rintro ⟨r, rest⟩ h
  simp_all [WP.uncurry']

private theorem len12 {α : Type} (l : List α) (h : l.length = 12) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, l = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] := by
  match l, h with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11], _ => exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

private theorem parse_12 (buf : io.ParseBuf) :
    io.ParseBuf.parse io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize buf 12#usize ⦃ r rest =>
      if 12 ≤ buf.length then
        (okPart r).map (·.val) = some (buf.val.take 12) ∧ rest.val = buf.val.drop 12
      else okPart r = none ∧ rest = buf ⦄ := by
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE])]
  exact mysql_common.PBUtil.deserialize_usize_ok 12#usize buf

attribute [local step] parse_12

/-- `MyDeserialize for StmtPacket`: `SIZE` is `Some(12)`. -/
theorem packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 12#usize := by
  unfold packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for StmtPacket`: total; `stmtOkRead` (12 bytes, status `0x00`). -/
theorem packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map StmtOk.of, rest.val) = stmtOkRead buf.val ⦄ := by
  unfold packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  rw [packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq]
  step as ⟨i, hi⟩
  obtain rfl := Option.some.inj hi
  step*
  · obtain rfl := cf_post pb (by assumption)
    have hlen : 12 ≤ buf.length := by
      by_contra hc; simp [hc, okPart] at r_post
    simp only [hlen, ite_true, okPart, Option.map] at r_post
    obtain ⟨hpb, hb1⟩ := r_post
    have hpb' : pb.val = buf.val.take 12 := by simpa using hpb
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, hx⟩ :=
      len12 pb.val (by rw [hpb']; simp; omega)
    have htake : buf.val.take 12 = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] := hpb' ▸ hx
    clear hpb hpb'
    simp only [io.ParseBuf.parse_unchecked_eq]
    step with d_status pb x0 _ hx as ⟨r1, b2, h1a, h1b⟩
    step*
    step with d_u32 b2 x1 x2 x3 x4 _ h1b as ⟨r2, b3, h2a, h2b⟩
    step*
    step with d_u16 b3 x5 x6 _ h2b as ⟨r3, b4, h3a, h3b⟩
    step*
    step with d_u16 b4 x7 x8 _ h3b as ⟨r4, b5, h4a, h4b⟩
    step*
    step with d_skip1 b5 x9 _ h4b as ⟨r5, b6, h5a, h5b⟩
    step*
    step with d_u16 b6 x10 x11 _ h5b as ⟨r6, b7, h6a, h6b⟩
    step*
    all_goals (simp_all [stmtOkRead, okPart, StmtOk.of])
  · split_ifs at * <;> simp_all [stmtOkRead, okPart]

/-- Round trip: a `COM_STMT_PREPARE_OK` in the protocol layout (`stmtOkEnc`) is read back. -/
theorem packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (p : packets.StmtPacket) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = stmtOkEnc (StmtOk.of p) ++ tail) :
    packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map StmtOk.of = some (StmtOk.of p) ∧ rest.val = tail ⦄ := by
  have ha : (StmtOk.of p).stmtId < 2 ^ 32 := by simp only [StmtOk.of]; scalar_tac
  have hb : (StmtOk.of p).numColumns < 2 ^ 16 := by simp only [StmtOk.of]; scalar_tac
  have hc : (StmtOk.of p).numParams < 2 ^ 16 := by simp only [StmtOk.of]; scalar_tac
  have hd : (StmtOk.of p).warnings < 2 ^ 16 := by simp only [StmtOk.of]; scalar_tac
  apply WP.spec_mono (packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  simp only [WP.uncurry'] at hr ⊢
  rw [h, Defs.stmtOkRead_stmtOkEnc _ ⟨ha, hb, hc, hd⟩] at hr
  simpa using hr

/-- `MySerialize for StmtPacket`: appends the 12 bytes `stmtOkEnc` (status and filler `0x00`). -/
theorem packets.StmtPacket.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.StmtPacket) (buf : alloc.vec.Vec U8) (h : buf.length + 12 ≤ Usize.max) :
    packets.StmtPacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ stmtOkEnc (StmtOk.of self) ⦄ := by
  unfold packets.StmtPacket.Insts.Mysql_commonProtoMySerialize.serialize
  step*
  all_goals (simp_all [stmtOkEnc, StmtOk.of, alloc.vec.Vec.length]; try omega)
  all_goals rfl

/-- `statement_id`: the field. -/
theorem packets.StmtPacket.impl.statement_id_eq (self : packets.StmtPacket) :
    packets.StmtPacket.impl.statement_id self = ok self.statement_id.1 := by
  unfold packets.StmtPacket.impl.statement_id; exact misc.raw.int.RawInt.deref_eq _ _

/-- `num_columns`: the field. -/
theorem packets.StmtPacket.impl.num_columns_eq (self : packets.StmtPacket) :
    packets.StmtPacket.impl.num_columns self = ok self.num_columns.1 := by
  unfold packets.StmtPacket.impl.num_columns; exact misc.raw.int.RawInt.deref_eq _ _

/-- `num_params`: the field. -/
theorem packets.StmtPacket.impl.num_params_eq (self : packets.StmtPacket) :
    packets.StmtPacket.impl.num_params self = ok self.num_params.1 := by
  unfold packets.StmtPacket.impl.num_params; exact misc.raw.int.RawInt.deref_eq _ _

/-- `warning_count`: the field. -/
theorem packets.StmtPacket.impl.warning_count_eq (self : packets.StmtPacket) :
    packets.StmtPacket.impl.warning_count self = ok self.warning_count.1 := by
  unfold packets.StmtPacket.impl.warning_count; exact misc.raw.int.RawInt.deref_eq _ _

end mysql_common
