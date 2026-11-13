import Defs

/-! Statements for `struct Tag and its impls` (spec file: `Specs/Packets/StmtBinlog.lean`).
Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `Tag::new(s)` of an empty string: `InvalidTag::Empty`. -/
theorem packets.Tag.new_empty {T : Type} (into : core.convert.Into T (alloc.borrow.Cow Str String))
    (s : T) (c : alloc.borrow.Cow Str String) (h : into.into s = ok c) (he : strCowBytes c = []) :
    packets.Tag.new into s = ok (.Err .Empty) := by
  sorry

/-- `Tag::new(s)` of a string of more than 32 bytes (`Tag::MAX_LEN`): `InvalidTag::TooLong` with
    the length. -/
theorem packets.Tag.new_too_long {T : Type} (into : core.convert.Into T (alloc.borrow.Cow Str String))
    (s : T) (c : alloc.borrow.Cow Str String) (h : into.into s = ok c)
    (hl : 32 < (strCowBytes c).length) (hfit : (strCowBytes c).length ≤ Usize.max) :
    packets.Tag.new into s ⦃ r => ∃ n : Usize, r = .Err (.TooLong n) ∧ n.val = (strCowBytes c).length ⦄ := by
  sorry

/-- `Tag::new(s)`, partially: if it returns a tag, the tag is `s.into()` and has 1 to 32 bytes.
    (The character checks, `[a-z_][a-z0-9_]*`, go through `Chars::next`, an Aeneas-library
    function without a model, so whether a 1–32-byte string is accepted is not stated.) -/
theorem packets.Tag.new_ok {T : Type} (into : core.convert.Into T (alloc.borrow.Cow Str String))
    (s : T) (c : alloc.borrow.Cow Str String) (h : into.into s = ok c) (t : packets.Tag)
    (hr : packets.Tag.new into s = ok (.Ok t)) :
    t = c ∧ 1 ≤ (strCowBytes c).length ∧ (strCowBytes c).length ≤ 32 := by
  sorry

/-- `as_str`: the tag's bytes. (Precondition: they fit in a `usize`, true of every real
    string.) -/
theorem packets.Tag.as_str_spec (self : packets.Tag) (hfit : (strCowBytes self).length ≤ Usize.max) :
    packets.Tag.as_str self ⦃ s => s.val = strCowBytes self ⦄ := by
  sorry

/-- `into_owned`: an owned tag with the same bytes. (Preconditions: the bytes are valid UTF-8,
    as those of every Rust `&str`, and fit in a `usize`.) -/
theorem packets.Tag.into_owned_spec (self : packets.Tag) (hu : IsUtf8 (strCowBytes self))
    (hfit : (strCowBytes self).length ≤ Usize.max) :
    packets.Tag.into_owned self ⦃ t => (∃ o, t = .Owned o) ∧ strCowBytes t = strCowBytes self ⦄ := by
  sorry

/-- `Deref<Target = str> for Tag`: the tag's bytes. -/
theorem packets.Tag.Insts.CoreOpsDerefDerefStr.deref_spec (self : packets.Tag)
    (hfit : (strCowBytes self).length ≤ Usize.max) :
    packets.Tag.Insts.CoreOpsDerefDerefStr.deref self ⦃ s => s.val = strCowBytes self ⦄ := by
  sorry

/-- `TryFrom<&str> for Tag`: `Tag::new` of the borrowed string. -/
theorem packets.Tag.Insts.CoreConvertTryFromSharedAStrInvalidTag.try_from_eq (s : Str) :
    packets.Tag.Insts.CoreConvertTryFromSharedAStrInvalidTag.try_from s =
      packets.Tag.new (core.convert.IntoFrom alloc.borrow.CowAStrString.Insts.CoreConvertFromSharedAStr) s := by
  sorry

/-- `TryFrom<String> for Tag`: `Tag::new` of the owned string. -/
theorem packets.TagStatic.Insts.CoreConvertTryFromStringInvalidTag.try_from_eq (s : String) :
    packets.TagStatic.Insts.CoreConvertTryFromStringInvalidTag.try_from s =
      packets.Tag.new (core.convert.IntoFrom alloc.borrow.CowAStrString.Insts.CoreConvertFromString) s := by
  sorry

end mysql_common
