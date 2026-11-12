import Defs

/-! Statements for `impl From<&[u8]>, From<Vec<u8>>, From<&str>, From<Cow<T>>, From<String>, From<[u8; N]> for Value` (spec file: `Specs/Value/Convert.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<&[u8]> for Value`: `Bytes` of a copy. -/
theorem value.Value.Insts.CoreConvertFromSharedASliceU8.from_spec (x : Slice U8) :
    value.Value.Insts.CoreConvertFromSharedASliceU8.from x ⦃ w => Val.ofValue w = .bytes x.val ⦄ := by
  sorry

/-- `From<Vec<u8>> for Value`: `Bytes`. -/
theorem value.Value.Insts.CoreConvertFromVecU8.from_eq (x : alloc.vec.Vec U8) : value.Value.Insts.CoreConvertFromVecU8.from x = ok (.Bytes x) := by
  sorry

/-- Round trip: `from_value_opt::<Vec<u8>>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromVecU8.roundtrip (x : alloc.vec.Vec U8) :
    (do let w ← value.Value.Insts.CoreConvertFromVecU8.from x; value.convert.from_value_opt alloc.vec.VecU8.Insts.Mysql_commonValueConvertFromValueVecU8 w) = ok (.Ok x) := by
  sorry

/-- `From<&str> for Value`: `Bytes` of the string's (UTF-8) bytes. -/
theorem value.Value.Insts.CoreConvertFromSharedAStr.from_spec (x : Str) :
    value.Value.Insts.CoreConvertFromSharedAStr.from x ⦃ w => Val.ofValue w = .bytes x.val ⦄ := by
  sorry

/-- Round trip: a `&str` reads back as a `String` with the same bytes. (A Rust `&str` is always
    valid UTF-8; Aeneas' `Str` is any byte slice, hence the hypothesis.) -/
theorem value.Value.Insts.CoreConvertFromSharedAStr.roundtrip (x : Str) (hx : IsUtf8 x.val) :
    (do let w ← value.Value.Insts.CoreConvertFromSharedAStr.from x; value.convert.from_value_opt alloc.string.String.Insts.Mysql_commonValueConvertFromValueString w) ⦃ r =>
      ∃ s, r = .Ok s ∧ utf8 s = x.val ⦄ := by
  sorry

/-- `From<Cow<'a, T>> for Value`: `Borrowed(x)` is `(&x).into()`, `Owned(x)` is `x.into()`. -/
theorem value.Value.Insts.CoreConvertFromCow.from_eq {T O : Type} (toOwned : alloc.borrow.ToOwned T O) (intoO : core.convert.Into O value.Value)
    (intoB : core.convert.Into T value.Value) (x : alloc.borrow.Cow T O) :
    value.Value.Insts.CoreConvertFromCow.from toOwned intoO intoB x =
      match x with | .Borrowed b => intoB.into b | .Owned o => intoO.into o := by
  sorry

/-- `From<Cow<[u8]>> for Value`: `Bytes` of the contents, borrowed or owned. -/
theorem value.Value.Insts.CoreConvertFromCow.from_slice_u8_spec (x : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    value.Value.Insts.CoreConvertFromCow.from (Slice.Insts.AllocBorrowToOwnedVec core.clone.CloneU8)
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromVecU8)
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromSharedASliceU8) x ⦃ w =>
        Val.ofValue w = .bytes (cowList x) ⦄ := by
  sorry

/-- Round trip: a `Cow<[u8]>` reads back (owned) with the same contents. -/
theorem value.Value.Insts.CoreConvertFromCow.roundtrip_slice_u8 (x : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    (do
      let w ← value.Value.Insts.CoreConvertFromCow.from (Slice.Insts.AllocBorrowToOwnedVec core.clone.CloneU8)
        (core.convert.IntoFrom value.Value.Insts.CoreConvertFromVecU8)
        (core.convert.IntoFrom value.Value.Insts.CoreConvertFromSharedASliceU8) x
      value.convert.from_value_opt alloc.borrow.CowStaticSliceU8VecU8.Insts.Mysql_commonValueConvertFromValueCowStaticSliceU8VecU8 w) ⦃ r => ∃ c, r = .Ok c ∧ cowList c = cowList x ⦄ := by
  sorry

/-- `From<String> for Value`: `Bytes` of its UTF-8 encoding. (The hypothesis holds for every
    Rust `String`; Lean strings are unbounded.) -/
theorem value.Value.Insts.CoreConvertFromString.from_spec (s : String) (h : (utf8 s).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromString.from s ⦃ w => Val.ofValue w = .bytes (utf8 s) ⦄ := by
  sorry

/-- Round trip: `from_value_opt::<String>(Value::from(s)) = Ok(s)`. -/
theorem value.Value.Insts.CoreConvertFromString.roundtrip (s : String) (h : (utf8 s).length ≤ Usize.max) :
    (do let w ← value.Value.Insts.CoreConvertFromString.from s; value.convert.from_value_opt alloc.string.String.Insts.Mysql_commonValueConvertFromValueString w) ⦃ r => r = .Ok s ⦄ := by
  sorry

/-- `From<[u8; N]> for Value`: `Bytes` of the array. -/
theorem value.Value.Insts.CoreConvertFromArrayU8N.from_spec {N : Usize} (x : Array U8 N) :
    value.Value.Insts.CoreConvertFromArrayU8N.from x ⦃ w => Val.ofValue w = .bytes x.val ⦄ := by
  sorry

/-- Round trip: `from_value_opt::<[u8; N]>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromArrayU8N.roundtrip {N : Usize} (x : Array U8 N) :
    (do let w ← value.Value.Insts.CoreConvertFromArrayU8N.from x; value.convert.from_value_opt (ArrayU8N.Insts.Mysql_commonValueConvertFromValueArrayU8N N) w) ⦃ r => r = .Ok x ⦄ := by
  sorry

end mysql_common
