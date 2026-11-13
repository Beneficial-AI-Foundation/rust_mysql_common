import Proofs.Util.IntAndMisc

/-! Statements for `struct RawInt and its impls` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `RawInt::new(x)` wraps `x`. -/
theorem misc.raw.int.RawInt.new_eq {T P : Type} (inst : misc.raw.int.IntRepr T P) (x : P) :
    misc.raw.int.RawInt.new inst x = ok (x, ()) := by
  rfl

/-- `Deref for RawInt`: the wrapped value. -/
theorem misc.raw.int.RawInt.deref_eq {T P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw.int.RawInt T P) :
    misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref inst self = ok self.1 := by
  rfl

/-- `MyDeserialize for RawInt<T>`: `SIZE` is `T::SIZE`. -/
theorem misc.raw.int.RawInt.SIZE_eq {T P : Type} (inst : misc.raw.int.IntRepr T P) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE inst = inst.SIZE := by
  simp [misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE]

/-- `MyDeserialize for RawInt<T>`: `T::deserialize`, wrapped; whatever `T::deserialize`
    guarantees about its result and the buffer carries over. -/
theorem misc.raw.int.RawInt.deserialize_spec {T P : Type} (inst : misc.raw.int.IntRepr T P)
    (buf : io.ParseBuf) (Q : Option P → io.ParseBuf → Prop)
    (h : inst.deserialize buf ⦃ r rest => Q (okPart r) rest ⦄) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize inst () buf ⦃ r rest => Q ((okPart r).map (·.1)) rest ⦄ := by
  exact IntAndMisc.rawint_deserialize_spec inst buf Q h

/-- `MySerialize for RawInt<T>`: `T::serialize` of the wrapped value. -/
theorem misc.raw.int.RawInt.serialize_eq {T P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw.int.RawInt T P) (buf : alloc.vec.Vec U8) :
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize inst self buf =
      inst.serialize self.1 buf := by
  rfl

end mysql_common
