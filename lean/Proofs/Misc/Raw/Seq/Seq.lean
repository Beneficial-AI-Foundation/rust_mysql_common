import Defs

/-! Statements for `struct Seq and its impls` (spec file: `Specs/Misc/Raw/Seq.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `Deref for Seq`: the items. -/
theorem misc.raw.seq.Seq.Insts.CoreOpsDerefDerefSlice.deref_spec {T U : Type} (cl : core.clone.Clone T)
    (self : misc.raw.seq.Seq T U) :
    misc.raw.seq.Seq.Insts.CoreOpsDerefDerefSlice.deref cl self ⦃ s => s.val = cowList self.1 ⦄ := by
  sorry

/-- `Seq::new(s)`: wraps `s.into()`. -/
theorem misc.raw.seq.Seq.new_eq {T T3 : Type} (U : Type) (cl : core.clone.Clone T)
    (into : core.convert.Into T3 (alloc.borrow.Cow (Slice T) (alloc.vec.Vec T))) (s : T3) (c : alloc.borrow.Cow (Slice T) (alloc.vec.Vec T)) (h : into.into s = ok c) :
    misc.raw.seq.Seq.new U cl into s = ok (c, ()) := by
  sorry

/-- `MySerialize for Seq<T, U>`: `U::serialize` of the items; whatever that guarantees carries over. -/
theorem misc.raw.seq.Seq.Insts.Mysql_commonProtoMySerialize.serialize_spec {T U Ctx : Type} (cl : core.clone.Clone T) (ser : proto.MySerialize T)
    (repr : misc.raw.seq.SeqRepr U Ctx) (self : misc.raw.seq.Seq T U) (buf : alloc.vec.Vec U8)
    (P : alloc.vec.Vec U8 → Prop)
    (h : ∀ s : Slice T, s.val = cowList self.1 → repr.serialize ser s buf ⦃ P ⦄) :
    misc.raw.seq.Seq.Insts.Mysql_commonProtoMySerialize.serialize cl ser repr self buf ⦃ P ⦄ := by
  sorry

/-- `MyDeserialize for Seq<T, U>`: `SIZE` is `None`. -/
theorem misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq {T U Ctx : Type} (cl : core.clone.Clone T) (de : proto.MyDeserialize T Unit)
    (repr : misc.raw.seq.SeqRepr U Ctx) :
    misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.SIZE cl de repr = none := by
  sorry

/-- `MyDeserialize for Seq<T, U>`: `U::deserialize`, wrapped; whatever it guarantees carries over. -/
theorem misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec {T U Ctx : Type} (cl : core.clone.Clone T) (de : proto.MyDeserialize T Unit)
    (repr : misc.raw.seq.SeqRepr U Ctx) (ctx : Ctx) (buf : io.ParseBuf)
    (Q : Option (List T) → io.ParseBuf → Prop)
    (h : repr.deserialize cl de ctx buf ⦃ r rest => Q ((okPart r).map cowList) rest ⦄) :
    misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.deserialize cl de repr ctx buf ⦃ r rest => Q ((okPart r).map (fun s => cowList s.1)) rest ⦄ := by
  sorry

end mysql_common
