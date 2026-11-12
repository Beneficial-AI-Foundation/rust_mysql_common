import Proofs.Util.IntAndMisc
import Proofs.Misc.Raw.Int.RawInt

/-! Statements for `struct RawFlags and its impls` (spec file: `Specs/Misc/Raw/Flags.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `RawFlags::new(value)` wraps `value`. -/
theorem misc.raw.flags.RawFlags.new_eq {T B : Type} (U : Type) (fl : bitflags.traits.Flags T B) (value : B) :
    misc.raw.flags.RawFlags.new U fl value = ok (value, ()) := by
  rfl

/-- `get`: `T::from_bits_truncate` of the raw bits (unknown bits dropped, documented). -/
theorem misc.raw.flags.RawFlags.get_eq {T U B : Type} (fl : bitflags.traits.Flags T B)
    (self : misc.raw.flags.RawFlags T U B) :
    misc.raw.flags.RawFlags.get fl self = fl.from_bits_truncate self.1 := by
  rfl

/-- `MyDeserialize for RawFlags<T, U>`: `U::deserialize` of the raw bits (all of them: unknown bits are kept); whatever it guarantees carries over. -/
theorem misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T U B : Type} (fl : bitflags.traits.Flags T B)
    (inst : misc.raw.int.IntRepr U B) (buf : io.ParseBuf) (Q : Option B → io.ParseBuf → Prop)
    (h : inst.deserialize buf ⦃ r rest => Q (okPart r) rest ⦄) :
    misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize fl inst () buf ⦃ r rest => Q ((okPart r).map (·.1)) rest ⦄ := by
  unfold misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  rw [io.ParseBuf.parse_unchecked_eq]
  have := IntAndMisc.rawint_deserialize_spec inst buf Q h
  step with this as ⟨ r, rest, hq ⟩
  cases r
  · step*
    subst rf_post t_post cf_post
    simp only [core.ops.control_flow.ControlFlow.Continue.injEq] at *
    subst_vars
    exact hq
  · step*
    simp_all [okPart]

/-- `MySerialize for RawFlags<T, U>`: `U::serialize` of the raw bits. -/
theorem misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMySerialize.serialize_eq {T U B : Type} (fl : bitflags.traits.Flags T B)
    (inst : misc.raw.int.IntRepr U B) (self : misc.raw.flags.RawFlags T U B) (buf : alloc.vec.Vec U8) :
    misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMySerialize.serialize fl inst self buf = inst.serialize self.1 buf := by
  unfold misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMySerialize.serialize
  obtain ⟨t, u⟩ := self
  show Std.bind (misc.raw.int.RawInt.new inst t) _ = _
  rw [IntAndMisc.rawint_new_bind]
  rfl

end mysql_common
