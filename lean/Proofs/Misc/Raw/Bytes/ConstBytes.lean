import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf
import Proofs.Misc.Raw.Array

/-! Statements for `struct ConstBytes and its impls` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MyDeserialize for ConstBytes<T, LEN>`: `SIZE` is `Some(LEN)`. -/
theorem misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T E : Type} {LEN : Usize} (d : core.default.Default T)
    (v : misc.raw.bytes.ConstBytesValue T E LEN) :
    misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE d v = some LEN := by
  unfold misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for ConstBytes<T, LEN>`: reads `LEN` bytes (unchecked: panics on a shorter
    buffer, `deserialize_panics`; `parse` checks); `Ok` iff they are `T::VALUE`, else an error
    (its kind is not stated: `io::Error` is opaque; the code uses `InvalidData`); consumed either
    way. (`T::VALUE` and `T::Error::default()` must not panic.) -/
theorem misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec {T E : Type} {LEN : Usize} (d : core.default.Default T)
    (v : misc.raw.bytes.ConstBytesValue T E LEN) (a : Array U8 LEN) (hv : v.VALUE = ok a)
    (hd : v.coredefaultDefaultInst.default ⦃ _ => True ⦄)
    (buf : io.ParseBuf) (h : LEN.val ≤ buf.length) :
    misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize d v () buf ⦃ r rest =>
      ((okPart r).isSome ↔ buf.val.take LEN.val = a.val) ∧ rest.val = buf.val.drop LEN.val ⦄ := by
  unfold misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize io.ParseBuf.parse_unchecked
  step with ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec LEN buf h as ⟨ r, rest, hr1, hr2 ⟩
  cases r with
  | Err e => simp [okPart] at hr1
  | Ok val =>
    simp [okPart] at hr1
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hv]
    step as ⟨ b, hb ⟩
    split
    · have := hb.mp (by assumption)
      simp only [WP.spec_ok, WP.uncurry'_pair, okPart, Option.isSome_some, true_iff]
      exact ⟨by rw [← hr1, this], hr2⟩
    · rename_i hnb
      step with hd as ⟨ t ⟩
      simp only [misc.io_error_from, bind_ok, WP.spec_ok, WP.uncurry'_pair, okPart, Option.isSome_none,
        Bool.false_eq_true, false_iff]
      exact ⟨fun e => hnb (hb.mpr (by rw [hr1, e])), hr2⟩

/-- `MyDeserialize for ConstBytes<T, LEN>` panics on fewer than `LEN` bytes. -/
theorem misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics {T E : Type} {LEN : Usize} (d : core.default.Default T)
    (v : misc.raw.bytes.ConstBytesValue T E LEN) (buf : io.ParseBuf) (h : buf.length < LEN.val) :
    ¬ misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize d v () buf ⦃ _ => True ⦄ := by
  unfold misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize io.ParseBuf.parse_unchecked
  intro hc
  exact ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics LEN buf h (spec_of_bind _ _ _ hc)

/-- `buf.parse::<ConstBytes<T, LEN>>(())`: total (checked through `SIZE`); an error with the buffer unchanged on fewer than `LEN` bytes. -/
theorem misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec {T E : Type} {LEN : Usize} (d : core.default.Default T)
    (v : misc.raw.bytes.ConstBytesValue T E LEN) (a : Array U8 LEN) (hv : v.VALUE = ok a)
    (hd : v.coredefaultDefaultInst.default ⦃ _ => True ⦄) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple d v) buf () ⦃ r rest =>
      if LEN.val ≤ buf.length then
        ((okPart r).isSome ↔ buf.val.take LEN.val = a.val) ∧ rest.val = buf.val.drop LEN.val
      else okPart r = none ∧ rest = buf ⦄ := by
  have hs : (misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple d v).SIZE = ok (some LEN) := by
    simp only [misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq]
  split_ifs with hl
  · apply WP.spec_mono (io.ParseBuf.parse_of_size _ buf () LEN hs hl
      (fun o => (o.isSome ↔ buf.val.take LEN.val = a.val)) ?_)
    · rintro ⟨r, rest⟩ hr; exact hr
    · intro sub hsub
      have hsl : LEN.val ≤ sub.length := by simp [Slice.length, hsub]; omega
      apply WP.spec_mono (misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec d v a hv hd sub hsl)
      rintro ⟨r, rest⟩ hr
      simp only [WP.uncurry'_pair] at hr ⊢
      rw [hr.1, hsub, List.take_take, Nat.min_self]
  · exact io.ParseBuf.parse_of_size_short _ buf () LEN hs (by omega)

/-- `MySerialize for ConstBytes<T, LEN>`: appends `T::VALUE`. -/
theorem misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec {T E : Type} {LEN : Usize}
    (v : misc.raw.bytes.ConstBytesValue T E LEN) (a : Array U8 LEN) (hv : v.VALUE = ok a)
    (self : misc.raw.bytes.ConstBytes T LEN) (buf : alloc.vec.Vec U8)
    (h : buf.length + LEN.val ≤ Usize.max) :
    misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMySerialize.serialize v self buf ⦃ buf' => buf'.val = buf.val ++ a.val ⦄ := by
  unfold misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMySerialize.serialize
  rw [hv]
  apply WP.spec_bind (Pₘ := fun x => x = a) (by simp)
  intro x hx; rw [hx]
  exact ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize_spec a buf h

end mysql_common
