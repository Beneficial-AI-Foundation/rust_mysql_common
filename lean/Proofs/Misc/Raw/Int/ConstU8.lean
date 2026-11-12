import Proofs.Util.IntAndMisc

/-! Statements for `struct ConstU8 and its impls` (spec file: `Specs/Misc/Raw/Int.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- `ConstU8::new()`. -/
theorem misc.raw.int.ConstU8.new_eq (T : Type) (N : U8) :
    misc.raw.int.ConstU8.new T N = ok () := by
  rfl

/-- `ConstU8::value`: `N`. -/
theorem misc.raw.int.ConstU8.value_spec {T : Type} {N : U8} (self : misc.raw.int.ConstU8 T N) :
    misc.raw.int.ConstU8.value self ⦃ v => v = N ⦄ := by
  simp [misc.raw.int.ConstU8.value]

/-- `MyDeserialize for ConstU8`: `SIZE` is `Some(1)`. -/
theorem misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T : Type} (N : U8) (e : core.error.Error T) (d : core.default.Default T) :
    misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE N e d = some 1#usize := by
  unfold misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for ConstU8`: reads 1 byte (unchecked: panics on a shorter buffer, `deserialize_panics`; `parse` checks), `Ok` iff they encode `N`, else an error (its kind is not stated: `io::Error` is opaque; the code uses `InvalidData`); the bytes are consumed either way. (`T::default()` must not panic.) -/
theorem misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T : Type} (N : U8) (e : core.error.Error T)
    (d : core.default.Default T) (hd : d.default ⦃ _ => True ⦄)
    (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize N e d () buf ⦃ r rest =>
      ((okPart r).isSome ↔ leNat (buf.val.take 1) = N.val) ∧ rest.val = buf.val.drop 1 ⦄ := by
  unfold misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with io.ParseBuf.eat_u8_spec as ⟨ i, rest, hi, hr ⟩
  split
  · rename_i heq
    subst heq
    simp [okPart, hi, hr]
  · rename_i hne
    step with hd as ⟨ t ⟩
    step*
    refine ⟨?_, hr⟩
    simp only [okPart, Option.isSome_none, Bool.false_eq_true, false_iff]
    intro h'; apply hne; apply UScalar.eq_of_val_eq; rw [hi, h']

/-- `MyDeserialize for ConstU8` panics on fewer than 1 byte. -/
theorem misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics {T : Type} (N : U8) (e : core.error.Error T)
    (d : core.default.Default T) (buf : io.ParseBuf) (h : buf.length < 1) :
    ¬ misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize N e d () buf ⦃ _ => True ⦄ := by
  unfold misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  exact PBUtil.not_spec_bind_left (io.ParseBuf.eat_u8_panics buf h)

/-- `buf.parse::<ConstU8>(())`: total (checked through `SIZE`); an error with the buffer unchanged on fewer than 1 byte. -/
theorem misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec {T : Type} (N : U8) (e : core.error.Error T)
    (d : core.default.Default T) (hd : d.default ⦃ _ => True ⦄) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple N e d) buf () ⦃ r rest =>
      if 1 ≤ buf.length then
        ((okPart r).isSome ↔ leNat (buf.val.take 1) = N.val) ∧ rest.val = buf.val.drop 1
      else okPart r = none ∧ rest = buf ⦄ := by
  have := IntAndMisc.parse_fixed (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple N e d) 1#usize (by simp [misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq]) buf ()
    (fun o => (o.isSome ↔ leNat (buf.val.take 1) = N.val)) (by
      intro sub hsub hl
      apply spec_mono (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec N e d hd sub (by simp [Slice.length, hsub] at *; omega))
      rintro ⟨r, rest⟩ ⟨h1, _⟩
      simpa [hsub, List.take_take] using h1)
  exact this

/-- `MySerialize for ConstU8`: appends `N`. -/
theorem misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec {T : Type} {N : U8} (self : misc.raw.int.ConstU8 T N)
    (buf : alloc.vec.Vec U8) (h : buf.length + 1 ≤ Usize.max) :
    misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ [N] ⦄ := by
  unfold misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize
  exact IntAndMisc.put_u8_spec buf N h

end mysql_common
