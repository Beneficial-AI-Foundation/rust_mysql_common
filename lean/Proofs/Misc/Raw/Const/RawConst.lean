import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf

/-! Statements for `struct RawConst and its impls` (spec file: `Specs/Misc/Raw/Const.lean`). Proofs: complete. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `RawConst::new(t)` wraps `t`. -/
theorem misc.raw._const.RawConst.new_eq {T P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P) (t : P) :
    misc.raw._const.RawConst.new U inst t = ok (t, ()) := by
  rfl

/-- `Deref for RawConst`: the raw value. -/
theorem misc.raw._const.RawConst.deref_eq {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw._const.RawConst T U P) :
    misc.raw._const.RawConst.Insts.CoreOpsDerefDeref.deref inst self = ok self.1 := by
  obtain ⟨t, u⟩ := self; rfl

/-- `get`: `U::try_from` of the raw value. -/
theorem misc.raw._const.RawConst.get_eq {T U P E : Type} (inst : misc.raw.int.IntRepr T P)
    (cp : core.marker.Copy P) (tf : core.convert.TryFrom U P E) (self : misc.raw._const.RawConst T U P) :
    misc.raw._const.RawConst.get inst cp tf self = tf.try_from self.1 := by
  obtain ⟨t, u⟩ := self; rfl

/-- `MyDeserialize for RawConst<T, U>`: `SIZE` is `T::SIZE`. -/
theorem misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P) :
    misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE U inst = inst.SIZE := by
  unfold misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for RawConst<T, U>`: `T::deserialize` of the raw value (no conversion, so no `InvalidData`); whatever it guarantees carries over. -/
theorem misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P)
    (buf : io.ParseBuf) (Q : Option P → io.ParseBuf → Prop)
    (h : inst.deserialize buf ⦃ r rest => Q (okPart r) rest ⦄) :
    misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize U inst () buf ⦃ r rest => Q ((okPart r).map (·.1)) rest ⦄ := by
  unfold misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with rawint_parse_unchecked_spec inst buf Q h as ⟨ r, rest, hr ⟩
  cases r with
  | Ok val =>
    obtain ⟨v, _⟩ := val
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, misc.raw._const.RawConst.new]
    apply WP.spec_bind (Pₘ := fun (rc : misc.raw._const.RawConst T U P) => rc.1 = v) ((WP.spec_ok _).mpr rfl)
    intro rc hrc
    apply (WP.spec_ok _).mpr
    simpa [okPart, hrc, Option.map] using hr
  | Err e =>
    simpa [okPart, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using hr

/-- `MySerialize for RawConst<T, U>`: `T::serialize` of the raw value. -/
theorem misc.raw._const.RawConst.Insts.Mysql_commonProtoMySerialize.serialize_eq {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw._const.RawConst T U P) (buf : alloc.vec.Vec U8) :
    misc.raw._const.RawConst.Insts.Mysql_commonProtoMySerialize.serialize inst self buf = inst.serialize self.1 buf := by
  obtain ⟨t, u⟩ := self
  unfold misc.raw._const.RawConst.Insts.Mysql_commonProtoMySerialize.serialize
  change (Bind.bind (misc.raw.int.RawInt.new inst t) fun ri =>
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize inst ri buf) = _
  rw [rawint_new_eq]
  exact Std.bind_tc_ok (α := misc.raw.int.RawInt T P) ((t, ()) : misc.raw.int.RawInt T P) _

end mysql_common
