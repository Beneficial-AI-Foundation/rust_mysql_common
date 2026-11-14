import Defs
import Proofs.Util.ConvBytesTime
import Proofs.Util.RawBytesSeq

/-! Statements for `struct Tag and its impls` (spec file: `Specs/Packets/StmtBinlog.lean`).
Proofs: complete. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

namespace TagUtil

/-- `Deref<Target = str> for Cow<str>`: the bytes (when they fit in a `usize`). -/
theorem str_cow_deref_spec (c : alloc.borrow.Cow Str String) (hfit : (strCowBytes c).length ≤ Usize.max) :
    alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref Str.Insts.AllocBorrowToOwnedString c ⦃ s =>
      s.val = strCowBytes c ⦄ := by
  cases c with
  | Borrowed b => simp [alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref, strCowBytes]
  | Owned o =>
    have hu := CBTUtil.u8sOf_toUTF8 o
    simp only [String.toUTF8_eq_toByteArray] at hu
    simp only [strCowBytes] at hfit
    simp only [alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref,
      alloc.string.String.Insts.CoreBorrowBorrowStr.borrow, strCowBytes, String.toUTF8_eq_toByteArray, hu]
    rw [dite_eq_left_of_eq_true (eq_true hfit)]
    exact (WP.spec_ok _).mpr (Slice.from_val _ _)

/-- The deref of a `Cow<str>` never returns a value other than its bytes. -/
theorem str_cow_deref_ok (c : alloc.borrow.Cow Str String) (s : Str)
    (h : alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref Str.Insts.AllocBorrowToOwnedString c = ok s) :
    s.val = strCowBytes c := by
  cases c with
  | Borrowed b => simp [alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref] at h; simp [h, strCowBytes]
  | Owned o =>
    have hu := CBTUtil.u8sOf_toUTF8 o
    simp only [String.toUTF8_eq_toByteArray] at hu
    simp only [alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref,
      alloc.string.String.Insts.CoreBorrowBorrowStr.borrow] at h
    split at h
    · have := Result.ok_injective h
      rw [← this, Slice.from_val]
      simp only [strCowBytes, String.toUTF8_eq_toByteArray, hu]
    · simp at h

theorem bind_ok_inv {α β : Type} {m : Result α} {k : α → Result β} {w : β}
    (h : Std.bind m k = ok w) : ∃ a, m = ok a ∧ k a = ok w := by
  cases m <;> simp_all

/-- `Tag::validate`: `Empty` on an empty string, `TooLong` on more than 32 bytes. -/
theorem validate_empty (s : Str) (h : s.val = []) :
    packets.Tag.validate s = ok (.Err .Empty) := by
  simp [packets.Tag.validate, core.str.Str.is_empty, h]

theorem validate_too_long (s : Str) (h : 32 < s.val.length) :
    packets.Tag.validate s ⦃ r => ∃ n : Usize, r = .Err (.TooLong n) ∧ n.val = s.val.length ⦄ := by
  have hne : ¬ s.val.length = 0 := by omega
  simp only [packets.Tag.validate, core.str.Str.is_empty, core.str.Str.len, hne, decide_false, bind_ok,
    Bool.false_eq_true, ↓reduceIte]
  have hgt : Slice.len s > packets.Tag.MAX_LEN := by
    have := Slice.len_val s
    simp only [packets.Tag.MAX_LEN]; scalar_tac
  simp [hgt]

end TagUtil

/-- `Tag::new(s)` of an empty string: `InvalidTag::Empty`. -/
theorem packets.Tag.new_empty {T : Type} (into : core.convert.Into T (alloc.borrow.Cow Str String))
    (s : T) (c : alloc.borrow.Cow Str String) (h : into.into s = ok c) (he : strCowBytes c = []) :
    packets.Tag.new into s = ok (.Err .Empty) := by
  unfold packets.Tag.new
  have hd := TagUtil.str_cow_deref_spec c (by simp [he])
  obtain ⟨s2, hs2, hv⟩ := PBUtil.spec_eq_ok hd
  rw [he] at hv
  simp [h, hs2, TagUtil.validate_empty s2 hv, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `Tag::new(s)` of a string of more than 32 bytes (`Tag::MAX_LEN`): `InvalidTag::TooLong` with
    the length. -/
theorem packets.Tag.new_too_long {T : Type} (into : core.convert.Into T (alloc.borrow.Cow Str String))
    (s : T) (c : alloc.borrow.Cow Str String) (h : into.into s = ok c)
    (hl : 32 < (strCowBytes c).length) (hfit : (strCowBytes c).length ≤ Usize.max) :
    packets.Tag.new into s ⦃ r => ∃ n : Usize, r = .Err (.TooLong n) ∧ n.val = (strCowBytes c).length ⦄ := by
  unfold packets.Tag.new
  obtain ⟨s2, hs2, hv⟩ := PBUtil.spec_eq_ok (TagUtil.str_cow_deref_spec c hfit)
  obtain ⟨r, hr, n, rfl, hn⟩ := PBUtil.spec_eq_ok (TagUtil.validate_too_long s2 (by rw [hv]; exact hl))
  simp only [h, hs2, hr, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply spec_bind_ok
  apply (WP.spec_ok _).mpr
  exact ⟨n, rfl, by rw [hn, hv]⟩

/-- `Tag::new(s)`, partially: if it returns a tag, the tag is `s.into()` and has 1 to 32 bytes.
    (The character checks, `[a-z_][a-z0-9_]*`, go through `Chars::next`, an Aeneas-library
    function without a model, so whether a 1–32-byte string is accepted is not stated.) -/
theorem packets.Tag.new_ok {T : Type} (into : core.convert.Into T (alloc.borrow.Cow Str String))
    (s : T) (c : alloc.borrow.Cow Str String) (h : into.into s = ok c) (t : packets.Tag)
    (hr : packets.Tag.new into s = ok (.Ok t)) :
    t = c ∧ 1 ≤ (strCowBytes c).length ∧ (strCowBytes c).length ≤ 32 := by
  unfold packets.Tag.new at hr
  rw [h, bind_ok] at hr
  obtain ⟨s2, hd, hr⟩ := TagUtil.bind_ok_inv hr
  have hv := TagUtil.str_cow_deref_ok c s2 hd
  obtain ⟨r, hval, hr⟩ := TagUtil.bind_ok_inv hr
  have hok : r = .Ok () := by
    cases r with
    | Ok u => rfl
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hr
  subst hok
  simp [core.result.Result.Insts.CoreOpsTry.branch] at hr
  refine ⟨hr.symm, ?_, ?_⟩
  · by_cases h0 : s2.val = []
    · rw [TagUtil.validate_empty s2 h0] at hval; simp at hval
    · rw [← hv]; cases hs : s2.val with
      | nil => exact absurd hs h0
      | cons _ _ => simp
  · by_cases h32 : 32 < s2.val.length
    · obtain ⟨r, hr', n, rfl, -⟩ := PBUtil.spec_eq_ok (TagUtil.validate_too_long s2 h32)
      rw [hr'] at hval; simp at hval
    · rw [← hv]; omega

/-- `as_str`: the tag's bytes. (Precondition: they fit in a `usize`, true of every real
    string.) -/
theorem packets.Tag.as_str_spec (self : packets.Tag) (hfit : (strCowBytes self).length ≤ Usize.max) :
    packets.Tag.as_str self ⦃ s => s.val = strCowBytes self ⦄ := by
  unfold packets.Tag.as_str
  exact TagUtil.str_cow_deref_spec self hfit

/-- `into_owned`: an owned tag with the same bytes. (Preconditions: the bytes are valid UTF-8,
    as those of every Rust `&str`, and fit in a `usize`.) -/
theorem packets.Tag.into_owned_spec (self : packets.Tag) (hu : IsUtf8 (strCowBytes self))
    (hfit : (strCowBytes self).length ≤ Usize.max) :
    packets.Tag.into_owned self ⦃ t => (∃ o, t = .Owned o) ∧ strCowBytes t = strCowBytes self ⦄ := by
  unfold packets.Tag.into_owned
  cases self with
  | Borrowed b =>
    obtain ⟨st, hst⟩ := hu
    simp only [strCowBytes] at hst
    have hf : String.fromUTF8? (Trusted.bytesOf b.val) = some st := by
      rw [← hst]; exact CBTUtil.fromUTF8?_utf8 st
    simp [alloc.borrow.Cow.into_owned,
      Str.Insts.AllocBorrowToOwnedString.to_owned, hf, strCowBytes, hst]
  | Owned o => simp [alloc.borrow.Cow.into_owned]

/-- `Deref<Target = str> for Tag`: the tag's bytes. -/
theorem packets.Tag.Insts.CoreOpsDerefDerefStr.deref_spec (self : packets.Tag)
    (hfit : (strCowBytes self).length ≤ Usize.max) :
    packets.Tag.Insts.CoreOpsDerefDerefStr.deref self ⦃ s => s.val = strCowBytes self ⦄ := by
  unfold packets.Tag.Insts.CoreOpsDerefDerefStr.deref
  exact TagUtil.str_cow_deref_spec self hfit

/-- `TryFrom<&str> for Tag`: `Tag::new` of the borrowed string. -/
theorem packets.Tag.Insts.CoreConvertTryFromSharedAStrInvalidTag.try_from_eq (s : Str) :
    packets.Tag.Insts.CoreConvertTryFromSharedAStrInvalidTag.try_from s =
      packets.Tag.new (core.convert.IntoFrom alloc.borrow.CowAStrString.Insts.CoreConvertFromSharedAStr) s := by
  rfl

/-- `TryFrom<String> for Tag`: `Tag::new` of the owned string. -/
theorem packets.TagStatic.Insts.CoreConvertTryFromStringInvalidTag.try_from_eq (s : String) :
    packets.TagStatic.Insts.CoreConvertTryFromStringInvalidTag.try_from s =
      packets.Tag.new (core.convert.IntoFrom alloc.borrow.CowAStrString.Insts.CoreConvertFromString) s := by
  rfl

end mysql_common
