import Defs
import Proofs.Util.ConvBytesTime
import Proofs.Value.Convert.String
import Proofs.Value.Convert.VecU8
import Proofs.Value.Convert.CowSliceU8
import Proofs.Value.Convert.ArrayU8N

/-! Statements for `impl From<&[u8]>, From<Vec<u8>>, From<&str>, From<Cow<T>>, From<String>, From<[u8; N]> for Value` (spec file: `Specs/Value/Convert.lean`). Helper lemmas: `Proofs/Util/ConvBytesTime.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<&[u8]> for Value`: `Bytes` of a copy. -/
theorem value.Value.Insts.CoreConvertFromSharedASliceU8.from_spec (x : Slice U8) :
    value.Value.Insts.CoreConvertFromSharedASliceU8.from x ⦃ w => Val.ofValue w = .bytes x.val ⦄ := by
  unfold value.Value.Insts.CoreConvertFromSharedASliceU8.from
  step*
  simp_all [Val.ofValue, alloc.vec.Vec.val]

/-- `From<Vec<u8>> for Value`: `Bytes`. -/
theorem value.Value.Insts.CoreConvertFromVecU8.from_eq (x : alloc.vec.Vec U8) : value.Value.Insts.CoreConvertFromVecU8.from x = ok (.Bytes x) := by
  rfl

/-- Round trip: `from_value_opt::<Vec<u8>>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromVecU8.roundtrip (x : alloc.vec.Vec U8) :
    (do let w ← value.Value.Insts.CoreConvertFromVecU8.from x; value.convert.from_value_opt alloc.vec.VecU8.Insts.Mysql_commonValueConvertFromValueVecU8 w) = ok (.Ok x) := by
  simp only [value.Value.Insts.CoreConvertFromVecU8.from_eq, bind_ok,
    alloc.vec.VecU8.Insts.Mysql_commonValueConvertFromValueVecU8.from_value_opt_eq]

/-- `From<&str> for Value`: `Bytes` of the string's (UTF-8) bytes. -/
theorem value.Value.Insts.CoreConvertFromSharedAStr.from_spec (x : Str) :
    value.Value.Insts.CoreConvertFromSharedAStr.from x ⦃ w => Val.ofValue w = .bytes x.val ⦄ := by
  have := value.Value.Insts.CoreConvertFromSharedASliceU8.from_spec x
  unfold value.Value.Insts.CoreConvertFromSharedASliceU8.from at this
  simp only [value.Value.Insts.CoreConvertFromSharedAStr.from, value.convert.trusted.str_as_bytes]
  refine WP.spec_bind (Pₘ := fun s => s = x) ((WP.spec_ok _).mpr rfl) ?_
  rintro s rfl; exact this

/-- Round trip: a `&str` reads back as a `String` with the same bytes. (A Rust `&str` is always
    valid UTF-8; Aeneas' `Str` is any byte slice, hence the hypothesis.) -/
theorem value.Value.Insts.CoreConvertFromSharedAStr.roundtrip (x : Str) (hx : IsUtf8 x.val) :
    (do let w ← value.Value.Insts.CoreConvertFromSharedAStr.from x; value.convert.from_value_opt alloc.string.String.Insts.Mysql_commonValueConvertFromValueString w) ⦃ r =>
      ∃ s, r = .Ok s ∧ utf8 s = x.val ⦄ := by
  obtain ⟨s, hs⟩ := hx
  apply WP.spec_bind (value.Value.Insts.CoreConvertFromSharedAStr.from_spec x)
  intro w hw
  apply WP.spec_mono (alloc.string.String.Insts.Mysql_commonValueConvertFromValueString.from_value_opt_spec w)
  intro r hr
  exact ⟨s, (hr.1 s).mpr (by rw [hw, hs]), hs⟩

/-- `From<Cow<'a, T>> for Value`: `Borrowed(x)` is `(&x).into()`, `Owned(x)` is `x.into()`. -/
theorem value.Value.Insts.CoreConvertFromCow.from_eq {T O : Type} (toOwned : alloc.borrow.ToOwned T O) (intoO : core.convert.Into O value.Value)
    (intoB : core.convert.Into T value.Value) (x : alloc.borrow.Cow T O) :
    value.Value.Insts.CoreConvertFromCow.from toOwned intoO intoB x =
      match x with | .Borrowed b => intoB.into b | .Owned o => intoO.into o := by
  cases x <;> rfl

/-- `From<Cow<[u8]>> for Value`: `Bytes` of the contents, borrowed or owned. -/
theorem value.Value.Insts.CoreConvertFromCow.from_slice_u8_spec (x : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    value.Value.Insts.CoreConvertFromCow.from (Slice.Insts.AllocBorrowToOwnedVec core.clone.CloneU8)
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromVecU8)
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromSharedASliceU8) x ⦃ w =>
        Val.ofValue w = .bytes (cowList x) ⦄ := by
  cases x with
  | Borrowed b =>
    simpa [value.Value.Insts.CoreConvertFromCow.from, core.convert.IntoFrom.into, cowList] using
      value.Value.Insts.CoreConvertFromSharedASliceU8.from_spec b
  | Owned o =>
    simp [value.Value.Insts.CoreConvertFromCow.from, core.convert.IntoFrom.into, cowList,
      value.Value.Insts.CoreConvertFromVecU8.from, Val.ofValue]

/-- Round trip: a `Cow<[u8]>` reads back (owned) with the same contents. -/
theorem value.Value.Insts.CoreConvertFromCow.roundtrip_slice_u8 (x : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    (do
      let w ← value.Value.Insts.CoreConvertFromCow.from (Slice.Insts.AllocBorrowToOwnedVec core.clone.CloneU8)
        (core.convert.IntoFrom value.Value.Insts.CoreConvertFromVecU8)
        (core.convert.IntoFrom value.Value.Insts.CoreConvertFromSharedASliceU8) x
      value.convert.from_value_opt alloc.borrow.CowStaticSliceU8VecU8.Insts.Mysql_commonValueConvertFromValueCowStaticSliceU8VecU8 w) ⦃ r => ∃ c, r = .Ok c ∧ cowList c = cowList x ⦄ := by
  apply WP.spec_bind (value.Value.Insts.CoreConvertFromCow.from_slice_u8_spec x)
  intro w hw
  cases w <;> simp only [Val.ofValue, reduceCtorEq] at hw
  rename_i b
  rw [alloc.borrow.CowStaticSliceU8VecU8.Insts.Mysql_commonValueConvertFromValueCowStaticSliceU8VecU8.from_value_opt_eq]
  simp only [WP.spec_ok]
  exact ⟨_, rfl, by simp only [cowList]; exact (Val.bytes.inj hw)⟩

/-- `From<String> for Value`: `Bytes` of its UTF-8 encoding. (The hypothesis holds for every
    Rust `String`; Lean strings are unbounded.) -/
theorem value.Value.Insts.CoreConvertFromString.from_spec (s : String) (h : (utf8 s).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromString.from s ⦃ w => Val.ofValue w = .bytes (utf8 s) ⦄ := by
  simp only [value.Value.Insts.CoreConvertFromString.from, value.convert.trusted.string_into_bytes,
    mysql_common.CBTUtil.u8sOf_toUTF8, h, _root_.dite_true]
  simp [Val.ofValue]

/-- Round trip: `from_value_opt::<String>(Value::from(s)) = Ok(s)`. -/
theorem value.Value.Insts.CoreConvertFromString.roundtrip (s : String) (h : (utf8 s).length ≤ Usize.max) :
    (do let w ← value.Value.Insts.CoreConvertFromString.from s; value.convert.from_value_opt alloc.string.String.Insts.Mysql_commonValueConvertFromValueString w) ⦃ r => r = .Ok s ⦄ := by
  apply WP.spec_bind (value.Value.Insts.CoreConvertFromString.from_spec s h)
  intro w hw
  apply WP.spec_mono (alloc.string.String.Insts.Mysql_commonValueConvertFromValueString.from_value_opt_spec w)
  intro r hr
  exact (hr.1 s).mpr hw

/-- `From<[u8; N]> for Value`: `Bytes` of the array. -/
theorem value.Value.Insts.CoreConvertFromArrayU8N.from_spec {N : Usize} (x : Array U8 N) :
    value.Value.Insts.CoreConvertFromArrayU8N.from x ⦃ w => Val.ofValue w = .bytes x.val ⦄ := by
  unfold value.Value.Insts.CoreConvertFromArrayU8N.from
  step*
  simp_all [Val.ofValue, alloc.vec.Vec.val, Array.to_slice]

/-- Round trip: `from_value_opt::<[u8; N]>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromArrayU8N.roundtrip {N : Usize} (x : Array U8 N) :
    (do let w ← value.Value.Insts.CoreConvertFromArrayU8N.from x; value.convert.from_value_opt (ArrayU8N.Insts.Mysql_commonValueConvertFromValueArrayU8N N) w) ⦃ r => r = .Ok x ⦄ := by
  apply WP.spec_bind (value.Value.Insts.CoreConvertFromArrayU8N.from_spec x)
  intro w hw
  apply WP.spec_mono (ArrayU8N.Insts.Mysql_commonValueConvertFromValueArrayU8N.from_value_opt_spec N w)
  intro r hr
  exact (hr.1 x).mpr hw

end mysql_common
