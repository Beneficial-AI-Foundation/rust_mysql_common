import Defs

/-! Statements for `struct ConstU32 and its impls` (spec file: `Specs/Misc/Raw/Int.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `ConstU32::new()`. -/
theorem misc.raw.int.ConstU32.new_eq (T : Type) (N : U32) :
    misc.raw.int.ConstU32.new T N = ok () := by
  sorry

/-- `MyDeserialize for ConstU32`: `SIZE` is `Some(4)`. -/
theorem misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T : Type} (N : U32) (e : core.error.Error T) (d : core.default.Default T) :
    misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE N e d = some 4#usize := by
  sorry

/-- `MyDeserialize for ConstU32`: reads 4 bytes (unchecked: panics on a shorter buffer, `deserialize_panics`; `parse` checks), `Ok` iff they encode `N`, else an error (its kind is not stated: `io::Error` is opaque; the code uses `InvalidData`); the bytes are consumed either way. (`T::default()` must not panic.) -/
theorem misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T : Type} (N : U32) (e : core.error.Error T)
    (d : core.default.Default T) (hd : d.default ⦃ _ => True ⦄)
    (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize N e d () buf ⦃ r rest =>
      ((okPart r).isSome ↔ leNat (buf.val.take 4) = N.val) ∧ rest.val = buf.val.drop 4 ⦄ := by
  sorry

/-- `MyDeserialize for ConstU32` panics on fewer than 4 bytes. -/
theorem misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics {T : Type} (N : U32) (e : core.error.Error T)
    (d : core.default.Default T) (buf : io.ParseBuf) (h : buf.length < 4) :
    ¬ misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize N e d () buf ⦃ _ => True ⦄ := by
  sorry

/-- `buf.parse::<ConstU32>(())`: total (checked through `SIZE`); an error with the buffer unchanged on fewer than 4 bytes. -/
theorem misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec {T : Type} (N : U32) (e : core.error.Error T)
    (d : core.default.Default T) (hd : d.default ⦃ _ => True ⦄) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.ConstU32.Insts.Mysql_commonProtoMyDeserializeDeTuple N e d) buf () ⦃ r rest =>
      if 4 ≤ buf.length then
        ((okPart r).isSome ↔ leNat (buf.val.take 4) = N.val) ∧ rest.val = buf.val.drop 4
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- `MySerialize for ConstU32`: appends `N`. -/
theorem misc.raw.int.ConstU32.Insts.Mysql_commonProtoMySerialize.serialize_spec {T : Type} {N : U32} (self : misc.raw.int.ConstU32 T N)
    (buf : alloc.vec.Vec U8) (h : buf.length + 4 ≤ Usize.max) :
    misc.raw.int.ConstU32.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ leBytes 4 N.val ⦄ := by
  sorry

end mysql_common
