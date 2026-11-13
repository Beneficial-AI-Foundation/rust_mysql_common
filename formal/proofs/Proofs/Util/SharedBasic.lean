import Defs
import Proofs.Util.ParseBuf

/-! Pure helper lemmas shared by several packet proofs: `Usize`, list sums, `Result`,
length-prefixed strings and slice equality. Only `Defs` and `Util/ParseBuf.lean` are imported, so any proof file can
use them without pulling in other proofs (`Shared.lean` has the raw-type steps). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common.Shared

theorem usize_max_lt : Usize.max < 2 ^ 64 := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max, U64.max, U32.numBits, U64.numBits]

theorem sum_take_le (l : List Nat) (k : Nat) : (l.take k).sum ≤ l.sum := by
  have := congrArg List.sum (List.take_append_drop k l)
  rw [List.sum_append] at this; omega

theorem sum_take_succ (l : List Nat) (k : Nat) (hk : k < l.length) :
    (l.take (k + 1)).sum = (l.take k).sum + l[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.sum_append]; simp

theorem drop_app (l t : List U8) (n : Nat) (h : l.length = n) : (l ++ t).drop n = t := by
  subst h; simp

/-- A pair-returning step followed by a continuation that fails on every outcome fails. -/
theorem bind_fail_pair {α β γ : Type} {m : Result (α × β)} {k : α → β → Result γ} {P : α → β → Prop}
    {e : Error} (hm : m ⦃ a b => P a b ⦄) (hk : ∀ a b, P a b → k a b = fail e) :
    (do let (a, b) ← m; k a b) = fail e := by
  obtain ⟨⟨a, b⟩, h1, h2⟩ := PBUtil.spec_eq_ok hm
  rw [h1]; simpa using hk a b h2

theorem checkedLenPrefixed_u8LenStr (s t : List U8) (hs : s.length ≤ 255) :
    checkedLenPrefixed 1 (u8LenStr s ++ t) = (some s, t) := by
  simp [checkedLenPrefixed, readLE, u8LenStr, leNat, byte_val, Nat.mod_eq_of_lt (by omega : s.length < 256)]

theorem slice_u8_eq_spec (s1 s2 : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s1 s2 ⦃ b => b = true ↔ s1.val = s2.val ⦄ := by
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec _ _ _ ?_)
  · intro b hb; rw [← Slice.eq_iff]; simpa using hb
  · intro x y; simp

end mysql_common.Shared
