import Proofs.Misc.Raw.Flags.RawFlags

/-!
# `src/misc/raw/flags.rs`
    `RawFlags<T, U>`: a bit-flags value `T::Bits`, serialized as the integer representation `U`.

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/Bytes.lean` (`okPart`).

    **Not covered.** `MyDeserialize::SIZE` for `RawFlags` is `Some(size_of::<T::Bits>())`, which the
    translation leaves to the uninterpreted `core.mem.size_of` (an axiom of `FunsExternal.lean`):
    nothing is stated about it, so nothing here depends on its value. `Debug`.

    **Behaviour to note.** Deserialization keeps unknown bits (documented); `get` truncates them.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct RawFlags and its impls` -/

/-- `RawFlags::new(value)` wraps `value`. -/
recall misc.raw.flags.RawFlags.new_eq {T B : Type} (U : Type) (fl : bitflags.traits.Flags T B) (value : B) :
    misc.raw.flags.RawFlags.new U fl value = ok (value, ())

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.flags.RawFlags.new_eq`

/-- `get`: `T::from_bits_truncate` of the raw bits (unknown bits dropped, documented). -/
recall misc.raw.flags.RawFlags.get_eq {T U B : Type} (fl : bitflags.traits.Flags T B)
    (self : misc.raw.flags.RawFlags T U B) :
    misc.raw.flags.RawFlags.get fl self = fl.from_bits_truncate self.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.flags.RawFlags.get_eq`

/-- `MyDeserialize for RawFlags<T, U>`: `U::deserialize` of the raw bits (all of them: unknown bits are kept); whatever it guarantees carries over. -/
recall misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T U B : Type} (fl : bitflags.traits.Flags T B)
    (inst : misc.raw.int.IntRepr U B) (buf : io.ParseBuf) (Q : Option B → io.ParseBuf → Prop)
    (h : inst.deserialize buf ⦃ r rest => Q (okPart r) rest ⦄) :
    misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize fl inst () buf ⦃ r rest => Q ((okPart r).map (·.1)) rest ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MySerialize for RawFlags<T, U>`: `U::serialize` of the raw bits. -/
recall misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMySerialize.serialize_eq {T U B : Type} (fl : bitflags.traits.Flags T B)
    (inst : misc.raw.int.IntRepr U B) (self : misc.raw.flags.RawFlags T U B) (buf : alloc.vec.Vec U8) :
    misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMySerialize.serialize fl inst self buf = inst.serialize self.1 buf

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMySerialize.serialize_eq`
end mysql_common
