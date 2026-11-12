import Defs
import Proofs.Util.PacketsOkErr

/-! Statements for `struct SqlState and its impls` (spec file: `Specs/Packets.lean`). Helper lemmas: `Proofs/Util/PacketsOkErr.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil mysql_common.PKUtil
open core.result.Result.Insts

namespace mysql_common

/-- `new`: the given state. -/
theorem packets.SqlState.new_eq (state : Array U8 5#usize) :
    packets.SqlState.new state = ok { __state_marker := (), state } := by
  simp [packets.SqlState.new, misc.raw.int.ConstU8.new]

/-- `as_bytes`: the state. -/
theorem packets.SqlState.as_bytes_eq (self : packets.SqlState) :
    packets.SqlState.as_bytes self = ok self.state := by
  simp [packets.SqlState.as_bytes]

/-- `MyDeserialize for SqlState`: `SIZE` is `Some(6)`. -/
theorem packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 6#usize := by
  simp [packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for SqlState`: total (each part is read with `parse`); `sqlStateRead` (`#`, then 5 bytes). -/
@[step]
theorem packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun s => s.state.val), rest.val) = sqlStateRead buf.val ⦄ := by
  unfold packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec 35#u8
    packets.InvalidSqlStateMarker.Insts.CoreErrorError packets.InvalidSqlStateMarker.Insts.CoreDefaultDefault
    ((WP.spec_ok _).mpr trivial) as ⟨r, buf1, h1⟩
  cases hb : (↑buf : List U8) with
  | nil =>
    have hl : ¬ 1 ≤ Slice.length buf := by simp [Slice.length, hb]
    rw [if_neg hl] at h1
    obtain ⟨hr, rfl⟩ := h1
    cases r with
    | Ok _ => simp at hr
    | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, sqlStateRead, hb]
  | cons m t =>
    have hl : 1 ≤ Slice.length buf := by simp [Slice.length, hb]
    rw [if_pos hl, hb] at h1
    obtain ⟨hr, hb1⟩ := h1
    simp only [List.drop_succ_cons, List.drop_zero] at hb1
    simp only [sqlStateRead]
    cases r with
    | Err e =>
      simp [leNat] at hr
      have hm : m.val ≠ 0x23 := by intro h; apply hr; scalar_tac
      simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, hm, hb1]
    | Ok cm =>
      simp [leNat] at hr
      have hm : m.val = 0x23 := by scalar_tac
      simp only [hm, ne_eq, not_true_eq_false, ite_false, CoreOpsTry.branch, bind_tc_ok]
      step with parse_array_spec as ⟨r1, buf2, h2⟩
      rw [hb1] at h2
      by_cases h5 : t.length < 5
      · have hl5 : ¬ 5 ≤ Slice.length buf1 := by simp [Slice.length, hb1]; omega
        rw [if_neg hl5] at h2
        obtain ⟨hr1, rfl⟩ := h2
        rw [if_pos h5]
        cases r1 with
        | Ok _ => simp at hr1
        | Err e => simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual, hb1]
      · have hl5 : 5 ≤ Slice.length buf1 := by simp [Slice.length, hb1]; omega
        rw [if_pos hl5] at h2
        obtain ⟨hr1, hb2⟩ := h2
        rw [if_neg h5]
        cases r1 with
        | Err e => simp at hr1
        | Ok st =>
          simp at hr1
          simp [CoreOpsTry.branch, hr1, hb2, hb1]

/-- `MySerialize for SqlState`: appends `#` and the state. -/
@[step]
theorem packets.SqlState.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.SqlState) (buf : alloc.vec.Vec U8) (h : buf.length + 6 ≤ Usize.max) :
    packets.SqlState.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ byte 0x23 :: self.state.val ⦄ := by
  unfold packets.SqlState.Insts.Mysql_commonProtoMySerialize.serialize
  step with misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨buf1, h1⟩
  step with ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize_spec as ⟨buf2, h2⟩
  · have : buf1.length = buf.length + 1 := by simp [alloc.vec.Vec.length, h1]
    simp only [this]; scalar_tac
  rw [h2, h1]; simp; rfl

end mysql_common
