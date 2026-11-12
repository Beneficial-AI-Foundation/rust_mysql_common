import Defs

/-! Statements for `struct Const and its impls` (spec file: `Specs/Misc/Raw/Const.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `Const::new(t)` wraps `t`. -/
theorem misc.raw._const.Const.new_eq {T : Type} (U : Type) (t : T) :
    misc.raw._const.Const.new U t = ok (t, ()) := by
  sorry

/-- `Deref for Const`: the wrapped value. -/
theorem misc.raw._const.Const.deref_eq {T U : Type} (self : misc.raw._const.Const T U) :
    misc.raw._const.Const.Insts.CoreOpsDerefDeref.deref self = ok self.1 := by
  sorry

/-- `MyDeserialize for Const<T, U>`: `SIZE` is `U::SIZE`. -/
theorem misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T U P E : Type} (inst : misc.raw.int.IntRepr U P)
    (tf : core.convert.TryFrom T P E) (err : core.error.Error E) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE inst tf err = inst.SIZE := by
  sorry

/-- `MyDeserialize for Const<T, U>`: `U::deserialize` of the raw value, then `T::try_from`; a
    failed conversion is an `InvalidData` error (documented). Stated given what `U::deserialize`
    guarantees (`Q`) and what `T::try_from` guarantees (`R`). -/
theorem misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T U P E : Type} (inst : misc.raw.int.IntRepr U P)
    (tf : core.convert.TryFrom T P E) (err : core.error.Error E) (buf : io.ParseBuf)
    (Q : Option P → io.ParseBuf → Prop) (hQ : inst.deserialize buf ⦃ r rest => Q (okPart r) rest ⦄)
    (R : P → Option T → Prop) (hR : ∀ p, tf.try_from p ⦃ r => R p (okPart r) ⦄) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize inst tf err () buf ⦃ r rest =>
      ∃ o, Q o rest ∧
        match o with
        | none => okPart r = none
        | some p => R p ((okPart r).map (·.1)) ⦄ := by
  sorry

/-- `MySerialize for Const<T, U>`: `U::serialize` of `t.into()`. -/
theorem misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq {T U P : Type} (cp : core.marker.Copy T) (into : core.convert.Into T P)
    (inst : misc.raw.int.IntRepr U P) (self : misc.raw._const.Const T U) (p : P)
    (h : into.into self.1 = ok p) (buf : alloc.vec.Vec U8) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize cp into inst self buf = inst.serialize p buf := by
  sorry

end mysql_common
