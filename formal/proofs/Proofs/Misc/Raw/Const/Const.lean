import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf

/-! Statements for `struct Const and its impls` (spec file: `Specs/Misc/Raw/Const.lean`). Proofs: complete. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `Const::new(t)` wraps `t`. -/
theorem misc.raw._const.Const.new_eq {T : Type} (U : Type) (t : T) :
    misc.raw._const.Const.new U t = ok (t, ()) := by
  rfl

/-- `Deref for Const`: the wrapped value. -/
theorem misc.raw._const.Const.deref_eq {T U : Type} (self : misc.raw._const.Const T U) :
    misc.raw._const.Const.Insts.CoreOpsDerefDeref.deref self = ok self.1 := by
  obtain ⟨t, u⟩ := self; rfl

/-- `MyDeserialize for Const<T, U>`: `SIZE` is `U::SIZE`. -/
theorem misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T U P E : Type} (inst : misc.raw.int.IntRepr U P)
    (tf : core.convert.TryFrom T P E) (err : core.error.Error E) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE inst tf err = inst.SIZE := by
  unfold misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for Const<T, U>`: `U::deserialize` of the raw value, then `T::try_from`; a
    failed conversion is an error (its kind is not stated: `io::Error` is opaque; documented as
    `InvalidData`). Stated given what `U::deserialize`
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
  unfold misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with rawint_parse_unchecked_spec inst buf Q hQ as ⟨ r, rest, hr ⟩
  cases r with
  | Ok val =>
    obtain ⟨v, _⟩ := val
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref]
    step with hR v as ⟨ r1, hr1 ⟩
    cases r1 with
    | Ok x =>
      simp only [misc.raw._const.Const.new]
      apply WP.spec_bind (Pₘ := fun (c : misc.raw._const.Const T U) => c.1 = x) ((WP.spec_ok _).mpr rfl)
      intro c hc
      apply (WP.spec_ok _).mpr
      refine ⟨some v, by simpa [okPart, Option.map] using hr, ?_⟩
      simpa [okPart, hc] using hr1
    | Err e =>
      simp only [misc.io_error_from, bind_ok, WP.spec_ok, WP.uncurry'_pair]
      exact ⟨some v, by simpa [okPart, Option.map] using hr, by simpa [okPart] using hr1⟩
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart]
    exact ⟨none, by simpa [okPart] using hr, trivial⟩

/-- `MySerialize for Const<T, U>`: `U::serialize` of `t.into()`. -/
theorem misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq {T U P : Type} (cp : core.marker.Copy T) (into : core.convert.Into T P)
    (inst : misc.raw.int.IntRepr U P) (self : misc.raw._const.Const T U) (p : P)
    (h : into.into self.1 = ok p) (buf : alloc.vec.Vec U8) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize cp into inst self buf = inst.serialize p buf := by
  obtain ⟨t, u⟩ := self
  unfold misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize
  change (Bind.bind (into.into t) fun t1 => Bind.bind (misc.raw.int.RawInt.new inst t1) fun ri =>
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize inst ri buf) = _
  simp only at h
  rw [h, bind_tc_ok, rawint_new_eq]
  exact Std.bind_tc_ok (α := misc.raw.int.RawInt U P) ((p, ()) : misc.raw.int.RawInt U P) _

end mysql_common
