import Defs

/-! Statements for `struct ConstBytes and its impls` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `MyDeserialize for ConstBytes<T, LEN>`: `SIZE` is `Some(LEN)`. -/
theorem misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq {T E : Type} {LEN : Usize} (d : core.default.Default T)
    (v : misc.raw.bytes.ConstBytesValue T E LEN) :
    misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE d v = some LEN := by
  sorry

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
  sorry

/-- `MyDeserialize for ConstBytes<T, LEN>` panics on fewer than `LEN` bytes. -/
theorem misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics {T E : Type} {LEN : Usize} (d : core.default.Default T)
    (v : misc.raw.bytes.ConstBytesValue T E LEN) (buf : io.ParseBuf) (h : buf.length < LEN.val) :
    ¬ misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize d v () buf ⦃ _ => True ⦄ := by
  sorry

/-- `buf.parse::<ConstBytes<T, LEN>>(())`: total (checked through `SIZE`); an error with the buffer unchanged on fewer than `LEN` bytes. -/
theorem misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec {T E : Type} {LEN : Usize} (d : core.default.Default T)
    (v : misc.raw.bytes.ConstBytesValue T E LEN) (a : Array U8 LEN) (hv : v.VALUE = ok a)
    (hd : v.coredefaultDefaultInst.default ⦃ _ => True ⦄) (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMyDeserializeDeTuple d v) buf () ⦃ r rest =>
      if LEN.val ≤ buf.length then
        ((okPart r).isSome ↔ buf.val.take LEN.val = a.val) ∧ rest.val = buf.val.drop LEN.val
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- `MySerialize for ConstBytes<T, LEN>`: appends `T::VALUE`. -/
theorem misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMySerialize.serialize_spec {T E : Type} {LEN : Usize}
    (v : misc.raw.bytes.ConstBytesValue T E LEN) (a : Array U8 LEN) (hv : v.VALUE = ok a)
    (self : misc.raw.bytes.ConstBytes T LEN) (buf : alloc.vec.Vec U8)
    (h : buf.length + LEN.val ≤ Usize.max) :
    misc.raw.bytes.ConstBytes.Insts.Mysql_commonProtoMySerialize.serialize v self buf ⦃ buf' => buf'.val = buf.val ++ a.val ⦄ := by
  sorry

end mysql_common
