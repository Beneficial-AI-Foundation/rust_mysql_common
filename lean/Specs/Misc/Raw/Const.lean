import Proofs.Misc.Raw.Const.Const
import Proofs.Misc.Raw.Const.RawConst

/-!
# `src/misc/raw/_const.rs`
    `Const<T, U>` (a parsed constant `T`, serialized as the integer representation `U`) and
    `RawConst<T, U>` (the raw `U::Primitive`, parsed on demand as `T`).

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/Bytes.lean` (`okPart`).

    **Reading the statements.** Generic in `T` and `U`: transfer lemmas from `U`'s `IntRepr` and
    `T`'s `TryFrom`/`Into`.

    **Not covered.** `DerefMut` impls; `Debug`; derived impls.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct Const and its impls` -/

/-- `Const::new(t)` wraps `t`. -/
recall misc.raw._const.Const.new_eq {T : Type} (U : Type) (t : T) :
    misc.raw._const.Const.new U t = ok (t, ())

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw._const.Const.new_eq`

/-- `Deref for Const`: the wrapped value. -/
recall misc.raw._const.Const.deref_eq {T U : Type} (self : misc.raw._const.Const T U) :
    misc.raw._const.Const.Insts.CoreOpsDerefDeref.deref self = ok self.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw._const.Const.deref_eq`

/-- `MyDeserialize for Const<T, U>`: `SIZE` is `U::SIZE`. -/
recall misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T U P E : Type} (inst : misc.raw.int.IntRepr U P)
    (tf : core.convert.TryFrom T P E) (err : core.error.Error E) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE inst tf err = inst.SIZE

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for Const<T, U>`: `U::deserialize` of the raw value, then `T::try_from`; a
    failed conversion is an `InvalidData` error (documented). Stated given what `U::deserialize`
    guarantees (`Q`) and what `T::try_from` guarantees (`R`). -/
recall misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T U P E : Type} (inst : misc.raw.int.IntRepr U P)
    (tf : core.convert.TryFrom T P E) (err : core.error.Error E) (buf : io.ParseBuf)
    (Q : Option P → io.ParseBuf → Prop) (hQ : inst.deserialize buf ⦃ r rest => Q (okPart r) rest ⦄)
    (R : P → Option T → Prop) (hR : ∀ p, tf.try_from p ⦃ r => R p (okPart r) ⦄) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize inst tf err () buf ⦃ r rest =>
      ∃ o, Q o rest ∧
        match o with
        | none => okPart r = none
        | some p => R p ((okPart r).map (·.1)) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw._const.Const.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MySerialize for Const<T, U>`: `U::serialize` of `t.into()`. -/
recall misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq {T U P : Type} (cp : core.marker.Copy T) (into : core.convert.Into T P)
    (inst : misc.raw.int.IntRepr U P) (self : misc.raw._const.Const T U) (p : P)
    (h : into.into self.1 = ok p) (buf : alloc.vec.Vec U8) :
    misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize cp into inst self buf = inst.serialize p buf

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw._const.Const.Insts.Mysql_commonProtoMySerialize.serialize_eq`

/-! ### `struct RawConst and its impls` -/

/-- `RawConst::new(t)` wraps `t`. -/
recall misc.raw._const.RawConst.new_eq {T P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P) (t : P) :
    misc.raw._const.RawConst.new U inst t = ok (t, ())

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw._const.RawConst.new_eq`

/-- `Deref for RawConst`: the raw value. -/
recall misc.raw._const.RawConst.deref_eq {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw._const.RawConst T U P) :
    misc.raw._const.RawConst.Insts.CoreOpsDerefDeref.deref inst self = ok self.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw._const.RawConst.deref_eq`

/-- `get`: `U::try_from` of the raw value. -/
recall misc.raw._const.RawConst.get_eq {T U P E : Type} (inst : misc.raw.int.IntRepr T P)
    (cp : core.marker.Copy P) (tf : core.convert.TryFrom U P E) (self : misc.raw._const.RawConst T U P) :
    misc.raw._const.RawConst.get inst cp tf self = tf.try_from self.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw._const.RawConst.get_eq`

/-- `MyDeserialize for RawConst<T, U>`: `SIZE` is `T::SIZE`. -/
recall misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P) :
    misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE U inst = inst.SIZE

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for RawConst<T, U>`: `T::deserialize` of the raw value (no conversion, so no `InvalidData`); whatever it guarantees carries over. -/
recall misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P)
    (buf : io.ParseBuf) (Q : Option P → io.ParseBuf → Prop)
    (h : inst.deserialize buf ⦃ r rest => Q (okPart r) rest ⦄) :
    misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize U inst () buf ⦃ r rest => Q ((okPart r).map (·.1)) rest ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MySerialize for RawConst<T, U>`: `T::serialize` of the raw value. -/
recall misc.raw._const.RawConst.Insts.Mysql_commonProtoMySerialize.serialize_eq {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw._const.RawConst T U P) (buf : alloc.vec.Vec U8) :
    misc.raw._const.RawConst.Insts.Mysql_commonProtoMySerialize.serialize inst self buf = inst.serialize self.1 buf

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw._const.RawConst.Insts.Mysql_commonProtoMySerialize.serialize_eq`
end mysql_common
