import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf
import Proofs.Misc.Raw.Const.RawConst

/-! Statements for `struct RawSeq and its impls` (spec file: `Specs/Misc/Raw/Seq.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `RawSeq::new(t)`: wraps `t.into()`. -/
theorem misc.raw.seq.RawSeq.new_eq {T T3 P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P)
    (into : core.convert.Into T3 (alloc.borrow.Cow (Slice P) (alloc.vec.Vec P))) (t : T3)
    (c : alloc.borrow.Cow (Slice P) (alloc.vec.Vec P)) (h : into.into t = ok c) :
    misc.raw.seq.RawSeq.new U inst into t = ok (c, ()) := by
  unfold misc.raw.seq.RawSeq.new
  simp [h]; rfl

/-- `len`: the number of items. -/
theorem misc.raw.seq.RawSeq.len_spec {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw.seq.RawSeq T U P) :
    misc.raw.seq.RawSeq.len inst self ⦃ n => n.val = (cowList self.1).length ⦄ := by
  unfold misc.raw.seq.RawSeq.len
  obtain ⟨c, u⟩ := self
  step as ⟨ s, hs ⟩
  simp [Slice.len, hs]

/-- `is_empty`: whether there are no items. -/
theorem misc.raw.seq.RawSeq.is_empty_spec {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw.seq.RawSeq T U P) :
    misc.raw.seq.RawSeq.is_empty inst self ⦃ b => (b ↔ cowList self.1 = []) ⦄ := by
  unfold misc.raw.seq.RawSeq.is_empty
  obtain ⟨c, u⟩ := self
  step as ⟨ s, hs ⟩
  simp [core.slice.Slice.is_empty, Slice.length, hs]

/-- `into_owned`: the same items, owned. -/
theorem misc.raw.seq.RawSeq.into_owned_spec {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw.seq.RawSeq T U P) :
    misc.raw.seq.RawSeq.into_owned inst self ⦃ r =>
      cowList r.1 = cowList self.1 ∧ ∃ v, r.1 = alloc.borrow.Cow.Owned v ⦄ := by
  sorry

/-- `get(index)`: the item at `index` as a `RawConst`, `None` out of range. -/
theorem misc.raw.seq.RawSeq.get_spec {T U P E : Type} (inst : misc.raw.int.IntRepr T P)
    (cp : core.marker.Copy T) (tf : core.convert.TryFrom U P E)
    (self : misc.raw.seq.RawSeq T U P) (index : Usize) :
    misc.raw.seq.RawSeq.get inst cp tf self index ⦃ o => o.map (·.1) = (cowList self.1)[index.val]? ⦄ := by
  unfold misc.raw.seq.RawSeq.get
  obtain ⟨c, u⟩ := self
  step as ⟨ s, hs ⟩
  simp only [core.slice.Slice.get, core.slice.index.Usize.get, bind_ok]
  cases ho : s[index]? with
  | none =>
    simp only
    apply (WP.spec_ok _).mpr
    simp [← hs, ← ho]
  | some x =>
    simp only
    rw [misc.raw._const.RawConst.new_eq]
    apply WP.spec_bind (Pₘ := fun (rc : misc.raw._const.RawConst T U P) => rc.1 = x) ((WP.spec_ok _).mpr rfl)
    intro rc hrc
    apply (WP.spec_ok _).mpr
    simp [hrc, ← hs, ← ho]

/-- `MyDeserialize for RawSeq<T, U>` (`T::Primitive = u8`): `SIZE` is `None`. -/
theorem misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq {T : Type} (U : Type) (inst : misc.raw.int.IntRepr T U8) :
    misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE U inst = none := by
  unfold misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE; rfl

private theorem slice_deser_spec (len : Usize) (buf : io.ParseBuf) :
    SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize len buf ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map (·.val) = some (buf.val.take len.val) ∧ rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄ := by
  unfold SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize
  step with io.ParseBuf.checked_eat_spec buf len as ⟨ o, buf1, ho ⟩
  split at ho
  · obtain ⟨ho1, ho2⟩ := ho
    cases o with
    | none => simp at ho1
    | some x => simp at ho1; simp [okPart, *]
  · obtain ⟨ho1, ho2⟩ := ho
    subst ho1 ho2
    simp [okPart, misc.unexpected_buf_eof, misc.io_error_msg, *]

/-- `MyDeserialize for RawSeq<T, U>`: total; the given number `len` of bytes, an error with the buffer unchanged if there are fewer. -/
theorem misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec {T : Type} (U : Type) (inst : misc.raw.int.IntRepr T U8)
    (len : Usize) (buf : io.ParseBuf) :
    misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize U inst len buf ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map (fun s => cowList s.1) = some (buf.val.take len.val) ∧
        rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄ := by
  unfold misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize
  rw [io.ParseBuf.parse_of_size_none _ _ _ (by
    simp [SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE])]
  step with slice_deser_spec len buf as ⟨ r, buf1, hr ⟩
  split at hr
  · obtain ⟨hr1, hr2⟩ := hr
    cases r with
    | Err e => simp [okPart] at hr1
    | Ok x =>
      simp [okPart] at hr1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok, WP.uncurry'_pair, okPart,
        cowList, ↓reduceIte, *]
      simp
      exact ⟨_, rfl, hr1⟩
  · obtain ⟨hr1, hr2⟩ := hr
    subst hr2
    cases r with
    | Ok x => simp [okPart] at hr1
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch, okPart,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, *]

/-- `MySerialize for RawSeq<T, U>`: appends the bytes (no length). -/
theorem misc.raw.seq.RawSeq0TUU8.Insts.Mysql_commonProtoMySerialize.serialize_spec {T U : Type} (inst : misc.raw.int.IntRepr T U8)
    (self : misc.raw.seq.RawSeq T U U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + (cowList self.1).length ≤ Usize.max) :
    misc.raw.seq.RawSeq0TUU8.Insts.Mysql_commonProtoMySerialize.serialize inst self buf ⦃ buf' => buf'.val = buf.val ++ cowList self.1 ⦄ := by
  unfold misc.raw.seq.RawSeq0TUU8.Insts.Mysql_commonProtoMySerialize.serialize
  obtain ⟨c, u⟩ := self
  step as ⟨ s, hs ⟩
  step as ⟨ v, hv ⟩
  simp [hv, hs]

/-- Round trip: `deserialize(s.len())` reads back what `serialize` writes. -/
theorem misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.roundtrip {T : Type} (U : Type) (inst : misc.raw.int.IntRepr T U8)
    (s tail : List U8) (len : Usize) (hlen : len.val = s.length) (buf : io.ParseBuf)
    (h : buf.val = s ++ tail) :
    misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize U inst len buf ⦃ r rest =>
      (okPart r).map (fun s => cowList s.1) = some s ∧ rest.val = tail ⦄ := by
  have hl : len.val ≤ buf.length := by simp [Slice.length, h, hlen]
  apply WP.spec_mono (misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec U inst len buf)
  rintro ⟨r, rest⟩ hr
  simp only [hl, ↓reduceIte, WP.uncurry'_pair] at hr ⊢
  rw [h, hlen] at hr
  simpa using hr

end mysql_common
