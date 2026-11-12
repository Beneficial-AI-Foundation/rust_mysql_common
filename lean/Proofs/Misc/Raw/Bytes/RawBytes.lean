import Defs

/-! Statements for `struct RawBytes and its impls` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `RawBytes::new(text)`: wraps `text.into()`. -/
theorem misc.raw.bytes.RawBytes.new_eq {T T2 Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (into : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))) (text : T2) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into text = ok c) :
    misc.raw.bytes.RawBytes.new inst into text = ok (c, ()) := by
  sorry

/-- `is_empty`: whether the effective length (`len`) is 0. -/
theorem misc.raw.bytes.RawBytes.is_empty_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (m : Usize) (hm : inst.MAX_LEN = ok m) (self : misc.raw.bytes.RawBytes T Ctx) :
    misc.raw.bytes.RawBytes.is_empty inst self ⦃ b => (b ↔ min (cowList self.1).length m.val = 0) ⦄ := by
  sorry

/-- `len`: the _effective_ length, `min(bytes.len(), T::MAX_LEN)` (documented). -/
theorem misc.raw.bytes.RawBytes.len_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (m : Usize) (hm : inst.MAX_LEN = ok m) (self : misc.raw.bytes.RawBytes T Ctx) :
    misc.raw.bytes.RawBytes.len inst self ⦃ n => n.val = min (cowList self.1).length m.val ⦄ := by
  sorry

/-- `as_bytes`: the _effective_ bytes, the first `T::MAX_LEN`. -/
theorem misc.raw.bytes.RawBytes.as_bytes_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (m : Usize) (hm : inst.MAX_LEN = ok m) (self : misc.raw.bytes.RawBytes T Ctx) :
    misc.raw.bytes.RawBytes.as_bytes inst self ⦃ s => s.val = (cowList self.1).take m.val ⦄ := by
  sorry

/-- `MySerialize for RawBytes<T>`: `T::serialize` of all the bytes (not just the effective
    ones; truncation, if any, is up to `T::serialize`). Stated for any property `P` that
    `T::serialize` guarantees. -/
theorem misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx)
    (self : misc.raw.bytes.RawBytes T Ctx) (buf : alloc.vec.Vec U8)
    (P : alloc.vec.Vec U8 → Prop)
    (h : ∀ s : Slice U8, s.val = cowList self.1 → inst.serialize s buf ⦃ P ⦄) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMySerialize.serialize inst self buf ⦃ P ⦄ := by
  sorry

/-- `MyDeserialize for RawBytes<T>`: `SIZE` is `T::SIZE`. -/
theorem misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.SIZE inst = inst.SIZE := by
  sorry

/-- `MyDeserialize for RawBytes<T>`: `T::deserialize`, wrapped; whatever it guarantees about the
    bytes and the buffer carries over. -/
theorem misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec {T Ctx : Type} (inst : misc.raw.bytes.BytesRepr T Ctx) (ctx : Ctx)
    (buf : io.ParseBuf) (Q : Option (List U8) → io.ParseBuf → Prop)
    (h : inst.deserialize ctx buf ⦃ r rest => Q ((okPart r).map cowList) rest ⦄) :
    misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize.deserialize inst ctx buf ⦃ r rest => Q ((okPart r).map (fun rb => cowList rb.1)) rest ⦄ := by
  sorry

end mysql_common
