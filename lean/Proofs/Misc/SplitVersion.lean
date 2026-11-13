import Defs

/-! Statements for `fn split_version` and `fn split_version_inner` (spec file: `Specs/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `split_version(version_str)`: total, exact on any input. It returns `splitVersion` of the string's bytes: the major and minor parts (before the first and second `.`), and the run of ASCII digits starting the third part, each a number in `0..=255`. It returns `(0, 0, 0)` if there are fewer than two `.` or a part is not such a number. **Quirks:**
    * a failure is indistinguishable from version `0.0.0`;
    * the first two parts may carry a sign (`"+5.-0.7"` gives `(5, 0, 7)`, via `btoi`);
    * a part above 255 makes the whole result `(0, 0, 0)`.
    Stated for any `AsRef<[u8]>` whose `as_ref` returns. -/
theorem misc.split_version_eq {T : Type} (inst : core.convert.AsRef T (Slice U8)) (x : T) (s : Slice U8)
    (hs : inst.as_ref x = ok s) :
    misc.split_version inst x = ok ((splitVersion s.val).getD (0#u8, 0#u8, 0#u8)) := by
  sorry

/-- `split_version_inner(input)`: total; exactly `splitVersion`. -/
theorem misc.split_version_inner_eq (input : Slice U8) :
    misc.split_version_inner input = ok (splitVersion input.val) := by
  sorry

end mysql_common
