import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf

/-! Statements for `struct RawBytes and its impls` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `RawBytes::new(text)`: wraps `text.into()`. -/
theorem misc.raw.bytes.RawBytes.new_eq {T T2 Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (into : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (text : T2) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into text = ok c) :
    misc.raw.bytes.RawBytes.new inst into text = ok (c, ()) := by
  unfold misc.raw.bytes.RawBytes.new
  simp [h]; rfl

/-- `is_empty`: whether the effective length (`len`) is 0. -/
theorem misc.raw.bytes.RawBytes.is_empty_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (m : Usize) (hm : inst.MAX_LEN = ok m) (self : misc.raw.bytes.RawBytes T Ctx) :
    misc.raw.bytes.RawBytes.is_empty inst self ⦃ b => (b ↔ min (cowList self.1).length m.val = 0) ⦄ := by
  unfold misc.raw.bytes.RawBytes.is_empty misc.raw.bytes.RawBytes.len
  obtain ⟨c, u⟩ := self
  simp only [hm, bind_ok]
  step as ⟨ s, hs ⟩
  step as ⟨ n, hn ⟩
  have : n.val = min (cowList c).length m.val := by simp [hn, Slice.len, hs]
  rw [← this]
  simp only [decide_eq_true_eq]
  constructor
  · intro h; simp [h]
  · intro h; scalar_tac

/-- `len`: the _effective_ length, `min(bytes.len(), T::MAX_LEN)` (documented). -/
theorem misc.raw.bytes.RawBytes.len_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (m : Usize) (hm : inst.MAX_LEN = ok m) (self : misc.raw.bytes.RawBytes T Ctx) :
    misc.raw.bytes.RawBytes.len inst self ⦃ n => n.val = min (cowList self.1).length m.val ⦄ := by
  unfold misc.raw.bytes.RawBytes.len
  obtain ⟨c, u⟩ := self
  simp only [hm, bind_ok]
  step as ⟨ s, hs ⟩
  step as ⟨ n, hn ⟩
  simp [hn, Slice.len, hs]

/-- `as_bytes`: the _effective_ bytes, the first `T::MAX_LEN`. -/
theorem misc.raw.bytes.RawBytes.as_bytes_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (m : Usize) (hm : inst.MAX_LEN = ok m) (self : misc.raw.bytes.RawBytes T Ctx) :
    misc.raw.bytes.RawBytes.as_bytes inst self ⦃ s => s.val = (cowList self.1).take m.val ⦄ := by
  unfold misc.raw.bytes.RawBytes.as_bytes
  have hl := misc.raw.bytes.RawBytes.len_spec inst m hm self
  obtain ⟨c, u⟩ := self
  simp only
  step with hl as ⟨ n, hn ⟩
  step as ⟨ s, hs ⟩
  step as ⟨ s', hs1, hs2 ⟩
  simp [hs1, hs, hn, List.slice, Nat.min_comm]

/-- `MySerialize for RawBytes<T>`: `T::serialize` of all the bytes (not just the effective
    ones; truncation, if any, is up to `T::serialize`). Stated for any property `P` that
    `T::serialize` guarantees. -/
theorem misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (self : misc.raw.bytes.RawBytes T Ctx) (buf : alloc.vec.Vec U8)
    (P : alloc.vec.Vec U8 → Prop)
    (h : ∀ s : Slice U8, s.val = cowList self.1 → inst.serialize s buf ⦃ P ⦄) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize inst self buf ⦃ P ⦄ := by
  unfold misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize
  obtain ⟨c, u⟩ := self
  step as ⟨ s, hs ⟩
  exact h s hs

/-- `MyDeserialize for RawBytes<T>`: `SIZE` is `T::SIZE`. -/
theorem misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE inst = inst.SIZE := by
  unfold misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE; rfl

/-- `MyDeserialize for RawBytes<T>`: `T::deserialize`, wrapped; whatever it guarantees about the
    bytes and the buffer carries over. -/
theorem misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx) (ctx : Ctx)
    (buf : io.ParseBuf) (Q : Option (List U8) → io.ParseBuf → Prop)
    (h : inst.deserialize ctx buf ⦃ r rest => Q ((okPart r).map cowList) rest ⦄) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize inst ctx buf ⦃ r rest => Q ((okPart r).map (fun rb => cowList rb.1)) rest ⦄ := by
  unfold misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize
  step with h as ⟨ r, rest, hr ⟩
  cases r with
  | Ok v => simpa [core.result.Result.Insts.CoreOpsTry.branch, okPart, Option.map] using hr
  | Err e => simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart] using hr

end mysql_common
