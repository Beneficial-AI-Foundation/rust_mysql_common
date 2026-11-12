import Defs

/-! Statements for `struct RawConst and its impls` (spec file: `Specs/Misc/Raw/Const.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `RawConst::new(t)` wraps `t`. -/
theorem misc.raw._const.RawConst.new_eq {T P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P) (t : P) :
    misc.raw._const.RawConst.new U inst t = ok (t, ()) := by
  sorry

/-- `Deref for RawConst`: the raw value. -/
theorem misc.raw._const.RawConst.deref_eq {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw._const.RawConst T U P) :
    misc.raw._const.RawConst.Insts.CoreOpsDerefDeref.deref inst self = ok self.1 := by
  sorry

/-- `get`: `U::try_from` of the raw value. -/
theorem misc.raw._const.RawConst.get_eq {T U P E : Type} (inst : misc.raw.int.IntRepr T P)
    (cp : core.marker.Copy P) (tf : core.convert.TryFrom U P E) (self : misc.raw._const.RawConst T U P) :
    misc.raw._const.RawConst.get inst cp tf self = tf.try_from self.1 := by
  sorry

/-- `MyDeserialize for RawConst<T, U>`: `SIZE` is `T::SIZE`. -/
theorem misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P) :
    misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE U inst = inst.SIZE := by
  sorry

/-- `MyDeserialize for RawConst<T, U>`: `T::deserialize` of the raw value (no conversion, so no `InvalidData`); whatever it guarantees carries over. -/
theorem misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P)
    (buf : io.ParseBuf) (Q : Option P → io.ParseBuf → Prop)
    (h : inst.deserialize buf ⦃ r rest => Q (okPart r) rest ⦄) :
    misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize U inst () buf ⦃ r rest => Q ((okPart r).map (·.1)) rest ⦄ := by
  sorry

/-- `MySerialize for RawConst<T, U>`: `T::serialize` of the raw value. -/
theorem misc.raw._const.RawConst.Insts.Mysql_commonProtoMySerialize.serialize_eq {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw._const.RawConst T U P) (buf : alloc.vec.Vec U8) :
    misc.raw._const.RawConst.Insts.Mysql_commonProtoMySerialize.serialize inst self buf = inst.serialize self.1 buf := by
  sorry

end mysql_common
