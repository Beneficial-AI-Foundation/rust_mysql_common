import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf

/-! Statements for `struct RawFlags and its impls` (spec file: `Specs/Misc/Raw/Flags.lean`). Proofs: complete. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `RawFlags::new(value)` wraps `value`. -/
theorem misc.raw.flags.RawFlags.new_eq {T B : Type} (U : Type) (fl : bitflags.traits.Flags T B) (value : B) :
    misc.raw.flags.RawFlags.new U fl value = ok (value, ()) := by
  rfl

/-- `get`: `T::from_bits_truncate` of the raw bits (unknown bits dropped, documented). -/
theorem misc.raw.flags.RawFlags.get_eq {T U B : Type} (fl : bitflags.traits.Flags T B)
    (self : misc.raw.flags.RawFlags T U B) :
    misc.raw.flags.RawFlags.get fl self = fl.from_bits_truncate self.1 := by
  obtain ⟨t, u⟩ := self; rfl

/-- `MyDeserialize for RawFlags<T, U>`: `U::deserialize` of the raw bits (all of them: unknown bits are kept); whatever it guarantees carries over. -/
theorem misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T U B : Type} (fl : bitflags.traits.Flags T B)
    (inst : misc.raw.int.IntRepr U B) (buf : io.ParseBuf) (Q : Option B → io.ParseBuf → Prop)
    (h : inst.deserialize buf ⦃ r rest => Q (okPart r) rest ⦄) :
    misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize fl inst () buf ⦃ r rest => Q ((okPart r).map (·.1)) rest ⦄ := by
  unfold misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with rawint_parse_unchecked_spec inst buf Q h as ⟨ r, rest, hr ⟩
  cases r with
  | Ok val =>
    obtain ⟨v, _⟩ := val
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref]
    apply WP.spec_bind (Pₘ := fun (t : B) => t = v) ((WP.spec_ok _).mpr rfl)
    intro t ht
    rw [ht]
    apply WP.spec_bind (Pₘ := fun (rf : misc.raw.flags.RawFlags T U B) => rf.1 = v) ((WP.spec_ok _).mpr rfl)
    intro rf hrf
    apply (WP.spec_ok _).mpr
    simpa [okPart, hrf, Option.map] using hr
  | Err e =>
    simpa [okPart, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using hr

/-- `MySerialize for RawFlags<T, U>`: `U::serialize` of the raw bits. -/
theorem misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMySerialize.serialize_eq {T U B : Type} (fl : bitflags.traits.Flags T B)
    (inst : misc.raw.int.IntRepr U B) (self : misc.raw.flags.RawFlags T U B) (buf : alloc.vec.Vec U8) :
    misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMySerialize.serialize fl inst self buf = inst.serialize self.1 buf := by
  obtain ⟨t, u⟩ := self
  unfold misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMySerialize.serialize
  change (Bind.bind (misc.raw.int.RawInt.new inst t) fun ri =>
    misc.raw.int.RawInt.Insts.Mysql_commonProtoMySerialize.serialize inst ri buf) = _
  rw [rawint_new_eq]
  exact Std.bind_tc_ok (α := misc.raw.int.RawInt U B) ((t, ()) : misc.raw.int.RawInt U B) _

end mysql_common
