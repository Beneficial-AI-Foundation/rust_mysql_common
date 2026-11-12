import Defs

/-! Statements for `struct ConstU8 and its impls` (spec file: `Specs/Misc/Raw/Int.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ConstU8::new()`. -/
theorem misc.raw.int.ConstU8.new_eq (T : Type) (N : U8) :
    misc.raw.int.ConstU8.new T N = ok () := by
  sorry

/-- `ConstU8::value`: `N`. -/
theorem misc.raw.int.ConstU8.value_spec {T : Type} {N : U8} (self : misc.raw.int.ConstU8 T N) :
    misc.raw.int.ConstU8.value self ⦃ v => v = N ⦄ := by
  sorry

/-- `MyDeserialize for ConstU8`: `SIZE` is `Some(1)`. -/
theorem misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T : Type} (N : U8) (e : core.error.Error T) (d : core.default.Default T) :
    misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE N e d = some 1#usize := by
  sorry

/-- `MyDeserialize for ConstU8`: reads 1 bytes (unchecked: panics on a shorter buffer; `parse` checks), `Ok` iff they encode `N`, else an `InvalidData` error; the bytes are consumed either way. (`T::default()` must not panic.) -/
theorem misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T : Type} (N : U8) (e : core.error.Error T)
    (d : core.default.Default T) (hd : d.default ⦃ _ => True ⦄)
    (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize N e d () buf ⦃ r rest =>
      ((okPart r).isSome ↔ leNat (buf.val.take 1) = N.val) ∧ rest.val = buf.val.drop 1 ⦄ := by
  sorry

/-- `MySerialize for ConstU8`: appends `N`. -/
theorem misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec {T : Type} {N : U8} (self : misc.raw.int.ConstU8 T N)
    (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ [N] ⦄ := by
  sorry

end mysql_common
