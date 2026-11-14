import Defs
import Proofs.Util.PacketsOkErr
import Proofs.Misc.Raw.Int.LeU64
import Proofs.Misc.Raw.Int.RawInt

/-! Statements for `struct GnoInterval and its impls` (spec file:
`Specs/Packets/StmtBinlog.lean`). Proofs: complete. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `parse_unchecked::<RawInt<LeU64>>` on at least 8 bytes. -/
theorem packets.GnoInterval.parse_unchecked_leu64_spec (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      (okPart r).map (·.1.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw.int.RawInt.deserialize_spec misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64 buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8)
    (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec buf h)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ hr
  simpa [Option.map_map] using hr

/-- `parse_unchecked::<RawInt<LeU64>>` panics on fewer than 8 bytes. -/
theorem packets.GnoInterval.parse_unchecked_leu64_panics (buf : io.ParseBuf) (h : buf.length < 8) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () = fail .panic := by
  rw [io.ParseBuf.parse_unchecked_eq]
  show misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize _ () buf = _
  unfold misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  exact PBUtil.bind_fail_left (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_panics buf h)

/-- `GnoInterval::new(start, end)`: the two bounds, unchecked. -/
theorem packets.GnoInterval.new_spec (start «end» : U64) :
    packets.GnoInterval.new start «end» ⦃ g => g.start.1 = start ∧ g.«end».1 = «end» ⦄ := by
  unfold packets.GnoInterval.new
  step*

/-- `start`: the start (inclusive). -/
theorem packets.GnoInterval.impl.start_eq (self : packets.GnoInterval) :
    packets.GnoInterval.impl.start self = ok self.start.1 := by
  rfl

/-- `end`: the end (exclusive). -/
theorem packets.GnoInterval.impl.end_eq (self : packets.GnoInterval) :
    packets.GnoInterval.impl.end self = ok self.«end».1 := by
  rfl

/-- `check_and_new(start, end)`: total; an error iff the interval `[start, end)` is empty or
    contains 0 (`start ≥ end` or `start = 0`; GNOs start at 1), else the interval. -/
theorem packets.GnoInterval.check_and_new_spec (start «end» : U64) :
    packets.GnoInterval.check_and_new start «end» ⦃ r =>
      if «end».val ≤ start.val ∨ start.val = 0 then okPart r = none
      else ∃ g, r = .Ok g ∧ g.start.1 = start ∧ g.«end».1 = «end» ⦄ := by
  unfold packets.GnoInterval.check_and_new
  by_cases h1 : «end».val ≤ start.val
  · have : start ≥ «end» := by scalar_tac
    simp [this, misc.trusted.gno_interval_order_error, h1, okPart]
  · have : ¬ start ≥ «end» := by scalar_tac
    simp only [this, ↓reduceIte, h1, false_or]
    by_cases h2 : start = 0#u64
    · have h2' : start.val = 0 := by simp [h2]
      simp [h2, misc.io_error_msg, okPart]
    · have h2' : ¬ start.val = 0 := by intro h; apply h2; scalar_tac
      have h3 : ¬ «end» = 0#u64 := by intro h; subst h; simp at h1
      simp only [h2, h3, ↓reduceIte]
      unfold packets.GnoInterval.new
      step*
      simp [*]

/-- `MySerialize for GnoInterval`: appends `gnoEnc` (start, end, 8 bytes each). -/
theorem packets.GnoInterval.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.GnoInterval) (buf : alloc.vec.Vec U8) (h : buf.length + 16 ≤ Usize.max) :
    packets.GnoInterval.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ gnoEnc (self.start.1.val, self.«end».1.val) ⦄ := by
  unfold packets.GnoInterval.Insts.Mysql_commonProtoMySerialize.serialize
  obtain ⟨⟨a, ua⟩, ⟨b, ub⟩⟩ := self
  simp only [misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize]
  step with misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec as ⟨ b1, h1 ⟩
  apply WP.spec_mono (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec _ b1 (by simp [h1]; omega))
  intro b hb
  simp [hb, h1, gnoEnc]

/-- `MyDeserialize for GnoInterval`: `SIZE` is `Some(16)`. -/
theorem packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 16#usize := by
  unfold packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for GnoInterval`: reads 16 bytes (start, end). Unchecked: it panics on a
    shorter buffer (`deserialize_panics`); `parse` checks through `SIZE`. -/
theorem packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun g => (g.start.1.val, g.«end».1.val)) =
        some (leNat (buf.val.take 8), leNat ((buf.val.drop 8).take 8)) ∧
      rest.val = buf.val.drop 16 ⦄ := by
  unfold packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with packets.GnoInterval.parse_unchecked_leu64_spec buf (by omega) as ⟨ r, buf1, h1, h2 ⟩
  cases r with
  | Err e => simp [okPart] at h1
  | Ok v =>
    simp only [okPart, Option.map_some, Option.some.injEq] at h1
    simp only [core.result.Result.Insts.CoreOpsTry.branch]
    step with packets.GnoInterval.parse_unchecked_leu64_spec buf1 (by simp [Slice.length, h2] at h ⊢; omega) as ⟨ r1, buf2, h3, h4 ⟩
    cases r1 with
    | Err e => simp [okPart] at h3
    | Ok v1 =>
      simp only [okPart, Option.map_some, Option.some.injEq] at h3
      simp [okPart, h1, h3, h2, h4, List.drop_drop]

/-- `MyDeserialize for GnoInterval` panics on fewer than 16 bytes. -/
theorem packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics
    (buf : io.ParseBuf) (h : buf.length < 16) :
    packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf = fail .panic := by
  unfold packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  by_cases h8 : buf.length < 8
  · exact PBUtil.bind_fail_left (packets.GnoInterval.parse_unchecked_leu64_panics buf h8)
  · obtain ⟨⟨r, buf1⟩, he, h1, h2⟩ := PBUtil.spec_eq_ok (packets.GnoInterval.parse_unchecked_leu64_spec buf (by omega))
    rw [he]
    cases r with
    | Err e => simp [okPart] at h1
    | Ok v =>
      have hp := packets.GnoInterval.parse_unchecked_leu64_panics buf1 (by simp [Slice.length, h2] at h ⊢; omega)
      simp [core.result.Result.Insts.CoreOpsTry.branch, hp]

end mysql_common
