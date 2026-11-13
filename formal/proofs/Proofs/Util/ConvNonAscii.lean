import Defs
import Proofs.Util.ConvBytesTime

/-! Helper lemmas for the date/time string parsers on input with a non-ASCII byte: what
`Trusted.isMatch_loose` gives (a match is longer than the pattern and has a byte `≥ 128` at a
`\d` position), and that a field holding such a byte makes `btou(..).unwrap()` panic. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical mysql_common.CBTUtil

namespace mysql_common.NAUtil

/-! ## The shape of a match (`Trusted.Pat.Loose`) -/

/-- The class is ASCII. -/
def patAscii : Trusted.Pat → Prop
  | .d => True
  | .r _ hi => hi < 128

theorem loose_length : ∀ (ps : List Trusted.Pat) (l : List U8), Trusted.Pat.Loose ps l →
    ps.length ≤ l.length
  | [], l, h => by simp
  | .r lo hi :: ps, l, h => by
    obtain ⟨x, bs, rfl, -, -, h⟩ := h
    have := loose_length ps bs h
    simp; omega
  | .d :: ps, l, h => by
    rcases h with ⟨x, bs, rfl, -, h⟩ | ⟨u, bs, rfl, hu, -, h⟩
    · have := loose_length ps bs h
      simp; omega
    · have := loose_length ps bs h
      simp; omega

/-- A match with a non-ASCII byte is longer than the pattern. -/
theorem loose_nonascii_length : ∀ (ps : List Trusted.Pat) (l : List U8), Trusted.Pat.Loose ps l →
    (∀ p ∈ ps, patAscii p) → (∃ c ∈ l, 128 ≤ c.val) → ps.length < l.length
  | [], l, h, _, hn => by
    obtain ⟨c, hc, -⟩ := hn
    simp only [Trusted.Pat.Loose] at h
    simp [h] at hc
  | .r lo hi :: ps, l, h, ha, hn => by
    obtain ⟨x, bs, rfl, -, hx, h⟩ := h
    obtain ⟨c, hc, hc'⟩ := hn
    have hhi : hi < 128 := ha (.r lo hi) (by simp)
    have hcb : c ∈ bs := by
      rcases List.mem_cons.1 hc with rfl | hc
      · omega
      · exact hc
    have := loose_nonascii_length ps bs h (fun p hp => ha p (by simp [hp])) ⟨c, hcb, hc'⟩
    simp; omega
  | .d :: ps, l, h, ha, hn => by
    rcases h with ⟨x, bs, rfl, hx, h⟩ | ⟨u, bs, rfl, hu, -, h⟩
    · obtain ⟨c, hc, hc'⟩ := hn
      have hcb : c ∈ bs := by
        rcases List.mem_cons.1 hc with rfl | hc
        · simp [Trusted.isAsciiDigit] at hx; omega
        · exact hc
      have := loose_nonascii_length ps bs h (fun p hp => ha p (by simp [hp])) ⟨c, hcb, hc'⟩
      simp; omega
    · have := loose_length ps bs h
      simp; omega

/-- A match with a non-ASCII byte has a byte `≥ 128` at a `\d` position. -/
theorem loose_nonascii_pos : ∀ (ps : List Trusted.Pat) (l : List U8), Trusted.Pat.Loose ps l →
    (∀ p ∈ ps, patAscii p) → (∃ c ∈ l, 128 ≤ c.val) →
    ∃ (i : Nat) (x : U8), l[i]? = some x ∧ 128 ≤ x.val ∧ ps[i]? = some Trusted.Pat.d
  | [], l, h, _, hn => by
    obtain ⟨c, hc, -⟩ := hn
    simp only [Trusted.Pat.Loose] at h
    simp [h] at hc
  | .r lo hi :: ps, l, h, ha, hn => by
    obtain ⟨x, bs, rfl, -, hx, h⟩ := h
    obtain ⟨c, hc, hc'⟩ := hn
    have hhi : hi < 128 := ha (.r lo hi) (by simp)
    have hcb : c ∈ bs := by
      rcases List.mem_cons.1 hc with rfl | hc
      · omega
      · exact hc
    obtain ⟨i, y, h1, h2, h3⟩ :=
      loose_nonascii_pos ps bs h (fun p hp => ha p (by simp [hp])) ⟨c, hcb, hc'⟩
    exact ⟨i + 1, y, by simpa using h1, h2, by simpa using h3⟩
  | .d :: ps, l, h, ha, hn => by
    rcases h with ⟨x, bs, rfl, hx, h⟩ | ⟨u, bs, rfl, hu, hall, h⟩
    · obtain ⟨c, hc, hc'⟩ := hn
      have hcb : c ∈ bs := by
        rcases List.mem_cons.1 hc with rfl | hc
        · simp [Trusted.isAsciiDigit] at hx; omega
        · exact hc
      obtain ⟨i, y, h1, h2, h3⟩ :=
        loose_nonascii_pos ps bs h (fun p hp => ha p (by simp [hp])) ⟨c, hcb, hc'⟩
      exact ⟨i + 1, y, by simpa using h1, h2, by simpa using h3⟩
    · match u, hu, hall with
      | y :: u', _, hall => exact ⟨0, y, by simp, hall y (by simp), by simp⟩

theorem ascii_ymdHms : ∀ p ∈ Trusted.Pat.ymdHms, patAscii p := by
  simp [Trusted.Pat.ymdHms, Trusted.Pat.ymd, patAscii]

theorem ascii_ymd : ∀ p ∈ Trusted.Pat.ymd, patAscii p := by
  simp [Trusted.Pat.ymd, patAscii]

theorem ascii_hhmmss : ∀ p ∈ Trusted.Pat.hhmmss, patAscii p := by
  simp [Trusted.Pat.hhmmss, Trusted.Pat.mmss, patAscii]

theorem ascii_hhhmmss : ∀ p ∈ Trusted.Pat.hhhmmss, patAscii p := by
  simp [Trusted.Pat.hhhmmss, Trusted.Pat.mmss, patAscii]

theorem ascii_frac (n : Nat) : ∀ p ∈ Trusted.Pat.frac n, patAscii p := by
  simp [Trusted.Pat.frac, patAscii]

theorem ascii_append {ps qs : List Trusted.Pat} (h1 : ∀ p ∈ ps, patAscii p)
    (h2 : ∀ p ∈ qs, patAscii p) : ∀ p ∈ ps ++ qs, patAscii p := by
  intro p hp
  rcases List.mem_append.1 hp with h | h
  · exact h1 p h
  · exact h2 p h

/-! ## The regexes on input with a non-ASCII byte -/

/-- The length of the shortest ASCII match of each regex. -/
def minLen : Trusted.Regex → Nat
  | .datetimeYmd => 10
  | .datetimeYmdHms => 19
  | .datetimeYmdHmsNs => 21
  | .timeHhMmSs => 8
  | .timeHhMmSsMs => 10
  | .timeHhhMmSs => 9
  | .timeHhhMmSsMs => 11

/-- A match holding a non-ASCII byte is longer than the shortest ASCII match: a non-ASCII digit
    takes at least two bytes. -/
theorem isMatch_nonascii_length (r : Trusted.Regex) (b : Slice U8)
    (h : Trusted.isMatch r b = true) (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    minLen r < b.val.length := by
  have hl := Trusted.isMatch_loose r b h
  cases r
  · exact loose_nonascii_length _ _ hl ascii_ymd hn
  · exact loose_nonascii_length _ _ hl ascii_ymdHms hn
  · obtain ⟨n, h1, h2, hl⟩ := hl
    have := loose_nonascii_length _ _ hl (ascii_append ascii_ymdHms (ascii_frac n)) hn
    simp [Trusted.Pat.ymdHms, Trusted.Pat.ymd, Trusted.Pat.frac] at this
    simp only [minLen]; omega
  · exact loose_nonascii_length _ _ hl ascii_hhmmss hn
  · obtain ⟨n, h1, h2, hl⟩ := hl
    have := loose_nonascii_length _ _ hl (ascii_append ascii_hhmmss (ascii_frac n)) hn
    simp [Trusted.Pat.hhmmss, Trusted.Pat.mmss, Trusted.Pat.frac] at this
    simp only [minLen]; omega
  · exact loose_nonascii_length _ _ hl ascii_hhhmmss hn
  · obtain ⟨n, h1, h2, hl⟩ := hl
    have := loose_nonascii_length _ _ hl (ascii_append ascii_hhhmmss (ascii_frac n)) hn
    simp [Trusted.Pat.hhhmmss, Trusted.Pat.mmss, Trusted.Pat.frac] at this
    simp only [minLen]; omega

/-- `DATETIME_RE_YMD_HMS_NS` on input with a non-ASCII byte: a byte `≥ 128` in a field. -/
theorem ns_nonascii_pos (b : Slice U8) (h : Trusted.isMatch .datetimeYmdHmsNs b = true)
    (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    ∃ (i : Nat) (x : U8), b.val[i]? = some x ∧ 128 ≤ x.val ∧
      i ≠ 4 ∧ i ≠ 7 ∧ i ≠ 10 ∧ i ≠ 13 ∧ i ≠ 16 ∧ i ≠ 19 := by
  obtain ⟨n, -, -, hl⟩ := Trusted.isMatch_loose _ b h
  obtain ⟨i, x, h1, h2, h3⟩ :=
    loose_nonascii_pos _ _ hl (ascii_append ascii_ymdHms (ascii_frac n)) hn
  refine ⟨i, x, h1, h2, ?_⟩
  and_intros <;> rintro rfl <;>
    simp [Trusted.Pat.ymdHms, Trusted.Pat.ymd, Trusted.Pat.frac] at h3

/-- `TIME_RE_HH_MM_SS_MS` on input with a non-ASCII byte: a byte `≥ 128` in a field. -/
theorem hhms_nonascii_pos (b : Slice U8) (h : Trusted.isMatch .timeHhMmSsMs b = true)
    (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    ∃ (i : Nat) (x : U8), b.val[i]? = some x ∧ 128 ≤ x.val ∧ i ≠ 2 ∧ i ≠ 5 ∧ i ≠ 8 := by
  obtain ⟨n, -, -, hl⟩ := Trusted.isMatch_loose _ b h
  obtain ⟨i, x, h1, h2, h3⟩ :=
    loose_nonascii_pos _ _ hl (ascii_append ascii_hhmmss (ascii_frac n)) hn
  refine ⟨i, x, h1, h2, ?_⟩
  and_intros <;> rintro rfl <;>
    simp [Trusted.Pat.hhmmss, Trusted.Pat.mmss, Trusted.Pat.frac] at h3

/-- `TIME_RE_HHH_MM_SS_MS` on input with a non-ASCII byte: a byte `≥ 128` in a field. -/
theorem hhhms_nonascii_pos (b : Slice U8) (h : Trusted.isMatch .timeHhhMmSsMs b = true)
    (hn : ∃ c ∈ b.val, 128 ≤ c.val) :
    ∃ (i : Nat) (x : U8), b.val[i]? = some x ∧ 128 ≤ x.val ∧ i ≠ 3 ∧ i ≠ 6 ∧ i ≠ 9 := by
  obtain ⟨n, -, -, hl⟩ := Trusted.isMatch_loose _ b h
  obtain ⟨i, x, h1, h2, h3⟩ :=
    loose_nonascii_pos _ _ hl (ascii_append ascii_hhhmmss (ascii_frac n)) hn
  refine ⟨i, x, h1, h2, ?_⟩
  and_intros <;> rintro rfl <;>
    simp [Trusted.Pat.hhhmmss, Trusted.Pat.mmss, Trusted.Pat.frac] at h3

/-! ## Reading a field that holds a non-ASCII byte panics -/

theorem btou_nonascii (ty : UScalarTy) (s : Slice U8) (h : ∃ x ∈ s.val, 128 ≤ x.val) :
    Trusted.btou ty s = none := by
  obtain ⟨x, hx, hx'⟩ := h
  have : s.val.all Trusted.isAsciiDigit = false := by
    rw [List.all_eq_false]
    exact ⟨x, hx, by simp [Trusted.isAsciiDigit]; omega⟩
  simp [Trusted.btou, Trusted.decimalDigits?, this]

theorem mem_slice {l : List U8} {i s e : Nat} {x : U8} (h : l[i]? = some x) (hs : s ≤ i)
    (he : i < e) : x ∈ List.slice s e l := by
  have hi : i < l.length := by
    by_contra hc; simp [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at h
  rw [List.mem_iff_getElem?]
  refine ⟨i - s, ?_⟩
  simp only [List.slice, List.getElem?_take, List.getElem?_drop]
  rw [show s + (i - s) = i by omega, h]; simp; omega

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

/-- The type-class bind of `Result` is `Std.bind`. -/
theorem tc_bind_eq {α β : Type} (m : Result α) (f : α → Result β) :
    (Bind.bind m f : Result β) = Aeneas.Std.bind m f := rfl

/-- `m` returns or panics. -/
def OkOrPanic {α : Type} (m : Result α) : Prop := m = fail .panic ∨ ∃ v, m = ok v

theorem bind_okp {α β : Type} {m : Result α} {f : α → Result β} (hm : OkOrPanic m)
    (hf : ∀ v, f v = fail .panic) : (do let v ← m; f v) = fail .panic := by
  rcases hm with h | ⟨v, h⟩
  · simp [h]
  · simp [h, hf]

theorem bind_p {α β : Type} {m : Result α} {f : α → Result β} (hm : m = fail .panic) :
    (do let v ← m; f v) = fail .panic := by simp [hm]

/-- `btou(&b[r]).unwrap()` at `u32`. -/
def fld32 (b : Slice U8) (r : core.ops.range.Range Usize) : Result U32 := do
  let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b r
  let o ← value.convert.trusted.btou_u32 s
  core.option.Option.unwrap o

/-- `btou(&b[r]).unwrap()` at `u8`. -/
def fld8 (b : Slice U8) (r : core.ops.range.Range Usize) : Result U8 := do
  let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) b r
  let o ← value.convert.trusted.btou_u8 s
  core.option.Option.unwrap o

/-- `btou(&b[..e]).unwrap()` at `u32`. -/
def fldTo32 (b : Slice U8) (r : core.ops.range.RangeTo Usize) : Result U32 := do
  let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) b r
  let o ← value.convert.trusted.btou_u32 s
  core.option.Option.unwrap o

/-- `parse_micros(&b[r])`. -/
def fldMicros (b : Slice U8) (r : core.ops.range.RangeFrom Usize) : Result U32 := do
  let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) b r
  value.convert.parse_micros s

theorem fld32_okp (b : Slice U8) (r : core.ops.range.Range Usize) : OkOrPanic (fld32 b r) := by
  unfold fld32 OkOrPanic
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index,
    value.convert.trusted.btou_u32]
  split
  · simp only [bind_ok]
    cases Trusted.btou .U32 _ <;> simp [core.option.Option.unwrap, Result.ofOption]
  · simp

theorem fld8_okp (b : Slice U8) (r : core.ops.range.Range Usize) : OkOrPanic (fld8 b r) := by
  unfold fld8 OkOrPanic
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index,
    value.convert.trusted.btou_u8]
  split
  · simp only [bind_ok]
    cases Trusted.btou .U8 _ <;> simp [core.option.Option.unwrap, Result.ofOption]
  · simp

theorem fldTo32_okp (b : Slice U8) (r : core.ops.range.RangeTo Usize) :
    OkOrPanic (fldTo32 b r) := by
  unfold fldTo32 OkOrPanic
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    value.convert.trusted.btou_u32]
  split
  · simp only [bind_ok]
    cases Trusted.btou .U32 _ <;> simp [core.option.Option.unwrap, Result.ofOption]
  · simp

theorem fld32_panic (b : Slice U8) (r : core.ops.range.Range Usize) (i : Nat) (x : U8)
    (h : b.val[i]? = some x) (hx : 128 ≤ x.val) (hs : r.start.val ≤ i) (he : i < r.end.val) :
    fld32 b r = fail .panic := by
  unfold fld32
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index,
    value.convert.trusted.btou_u32]
  split
  · simp only [bind_ok]
    rw [btou_nonascii]
    · simp [core.option.Option.unwrap, Result.ofOption]
    · exact ⟨x, by rw [Slice.from_val]; exact mem_slice h hs he, hx⟩
  · simp

theorem fld8_panic (b : Slice U8) (r : core.ops.range.Range Usize) (i : Nat) (x : U8)
    (h : b.val[i]? = some x) (hx : 128 ≤ x.val) (hs : r.start.val ≤ i) (he : i < r.end.val) :
    fld8 b r = fail .panic := by
  unfold fld8
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index,
    value.convert.trusted.btou_u8]
  split
  · simp only [bind_ok]
    rw [btou_nonascii]
    · simp [core.option.Option.unwrap, Result.ofOption]
    · exact ⟨x, by rw [Slice.from_val]; exact mem_slice h hs he, hx⟩
  · simp

theorem fldTo32_panic (b : Slice U8) (r : core.ops.range.RangeTo Usize) (i : Nat) (x : U8)
    (h : b.val[i]? = some x) (hx : 128 ≤ x.val) (he : i < r.end.val) :
    fldTo32 b r = fail .panic := by
  unfold fldTo32
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    value.convert.trusted.btou_u32]
  split
  · simp only [bind_ok]
    rw [btou_nonascii]
    · simp [core.option.Option.unwrap, Result.ofOption]
    · exact ⟨x, by rw [Slice.from_val]; exact mem_slice h (Nat.zero_le _) he, hx⟩
  · simp

theorem fldMicros_panic (b : Slice U8) (r : core.ops.range.RangeFrom Usize) (i : Nat) (x : U8)
    (h : b.val[i]? = some x) (hx : 128 ≤ x.val) (hs : r.start.val ≤ i) :
    fldMicros b r = fail .panic := by
  have hi : i < b.val.length := by
    by_contra hc; simp [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at h
  unfold fldMicros
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice.index]
  have hle : r.start.val ≤ b.length := by simp [Slice.length]; omega
  simp only [hle, ite_true]
  simp only [bind_ok, value.convert.parse_micros, value.convert.trusted.btou_u32]
  rw [btou_nonascii]
  · simp [core.option.Option.unwrap, Result.ofOption]
  · refine ⟨x, ?_, hx⟩
    simp only [Slice.getElem!_val_drop]
    rw [List.mem_iff_getElem?]
    exact ⟨i - r.start.val, by rw [List.getElem?_drop, show r.start.val + (i - r.start.val) = i by omega, h]⟩

/-! ## The ASCII matches are ASCII -/

theorem matchSeq_ascii : ∀ (ps : List (U8 → Bool)) (l : List U8), Trusted.matchSeq ps l = true →
    (∀ p ∈ ps, ∀ x, p x = true → x.val < 128) → ∀ c ∈ l, c.val < 128
  | [], [], _, _ => by simp
  | p :: ps, b :: bs, h, hp => by
    simp only [Trusted.matchSeq, Bool.and_eq_true] at h
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hp p (by simp) _ h.1
    · exact matchSeq_ascii ps bs h.2 (fun q hq => hp q (by simp [hq])) c hc
  | [], _ :: _, h, _ => by simp [Trusted.matchSeq] at h
  | _ :: _, [], h, _ => by simp [Trusted.matchSeq] at h

theorem matchFrac_ascii (l : List U8) (h : Trusted.matchFrac l = true) : ∀ c ∈ l, c.val < 128 := by
  match l with
  | [] => simp
  | b :: ds =>
    simp only [Trusted.matchFrac, Trusted.lit, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at h
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · omega
    · have := h.2 c hc
      simp [Trusted.isAsciiDigit] at this; omega

theorem cls_digit (x : U8) (h : Trusted.digit x = true) : x.val < 128 := by
  simp [Trusted.digit, Trusted.isAsciiDigit] at h; omega

theorem cls_lit (c : Nat) (hc : c < 128) (x : U8) (h : Trusted.lit c x = true) : x.val < 128 := by
  simp [Trusted.lit] at h; omega

theorem cls_byteIn (lo hi : Nat) (hc : hi < 128) (x : U8) (h : Trusted.byteIn lo hi x = true) :
    x.val < 128 := by
  simp [Trusted.byteIn] at h; omega

theorem cls_ymdHms : ∀ p ∈ Trusted.ymdHms, ∀ x, p x = true → x.val < 128 := by
  simp only [Trusted.ymdHms, Trusted.ymd, List.cons_append, List.nil_append, List.forall_mem_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩ <;>
    first | exact cls_digit | exact cls_lit _ (by norm_num)

theorem cls_ymd : ∀ p ∈ Trusted.ymd, ∀ x, p x = true → x.val < 128 := by
  simp only [Trusted.ymd, List.forall_mem_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩ <;>
    first | exact cls_digit | exact cls_lit _ (by norm_num)

theorem cls_hhmmss : ∀ p ∈ Trusted.hhmmss, ∀ x, p x = true → x.val < 128 := by
  simp only [Trusted.hhmmss, Trusted.mmss, List.cons_append, List.nil_append, List.forall_mem_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩ <;>
    first | exact cls_digit | exact cls_lit _ (by norm_num) | exact cls_byteIn _ _ (by norm_num)

theorem cls_hhhmmss : ∀ p ∈ Trusted.hhhmmss, ∀ x, p x = true → x.val < 128 := by
  simp only [Trusted.hhhmmss, Trusted.mmss, List.cons_append, List.nil_append, List.forall_mem_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩ <;>
    first | exact cls_digit | exact cls_lit _ (by norm_num) | exact cls_byteIn _ _ (by norm_num)

theorem take_drop_ascii (l : List U8) (n : Nat) (h1 : ∀ c ∈ l.take n, c.val < 128)
    (h2 : ∀ c ∈ l.drop n, c.val < 128) : ∀ c ∈ l, c.val < 128 := by
  intro c hc
  rw [← List.take_append_drop n l] at hc
  rcases List.mem_append.1 hc with h | h
  · exact h1 c h
  · exact h2 c h

/-- What a regex matches on ASCII input (`Regex.asciiMatch`) is ASCII. -/
theorem asciiMatch_ascii (r : Trusted.Regex) (l : List U8) (h : r.asciiMatch l = true) :
    ∀ c ∈ l, c.val < 128 := by
  cases r <;> simp only [Trusted.Regex.asciiMatch, Bool.and_eq_true] at h
  · exact matchSeq_ascii _ _ h cls_ymd
  · exact matchSeq_ascii _ _ h cls_ymdHms
  · exact take_drop_ascii l 19 (matchSeq_ascii _ _ h.1 cls_ymdHms) (matchFrac_ascii _ h.2)
  · exact matchSeq_ascii _ _ h cls_hhmmss
  · exact take_drop_ascii l 8 (matchSeq_ascii _ _ h.1 cls_hhmmss) (matchFrac_ascii _ h.2)
  · exact matchSeq_ascii _ _ h cls_hhhmmss
  · exact take_drop_ascii l 9 (matchSeq_ascii _ _ h.1 cls_hhhmmss) (matchFrac_ascii _ h.2)

/-! ## On ASCII input the shape axiom adds nothing: an ASCII match has the shape -/

/-- The single-byte class of a pattern position on ASCII input. -/
def patCls : Trusted.Pat → U8 → Bool
  | .d => Trusted.digit
  | .r lo hi => Trusted.byteIn lo hi

theorem lit_eq (c : Nat) : Trusted.lit c = Trusted.byteIn c c := by
  funext b
  rw [Bool.eq_iff_iff]
  simp [Trusted.lit, Trusted.byteIn]; omega

theorem loose_of_matchSeq : ∀ (ps : List Trusted.Pat) (l : List U8),
    Trusted.matchSeq (ps.map patCls) l = true → Trusted.Pat.Loose ps l
  | [], [], _ => by simp [Trusted.Pat.Loose]
  | [], _ :: _, h => by simp [Trusted.matchSeq] at h
  | _ :: _, [], h => by simp [Trusted.matchSeq] at h
  | .d :: ps, x :: bs, h => by
    simp only [List.map_cons, Trusted.matchSeq, Bool.and_eq_true] at h
    exact Or.inl ⟨x, bs, rfl, h.1, loose_of_matchSeq ps bs h.2⟩
  | .r lo hi :: ps, x :: bs, h => by
    simp only [List.map_cons, Trusted.matchSeq, Bool.and_eq_true, patCls, Trusted.byteIn,
      decide_eq_true_eq] at h
    exact ⟨x, bs, rfl, h.1.1, h.1.2, loose_of_matchSeq ps bs h.2⟩

theorem loose_append : ∀ (ps qs : List Trusted.Pat) (l1 l2 : List U8), Trusted.Pat.Loose ps l1 →
    Trusted.Pat.Loose qs l2 → Trusted.Pat.Loose (ps ++ qs) (l1 ++ l2)
  | [], qs, l1, l2, h1, h2 => by
    simp only [Trusted.Pat.Loose] at h1
    simpa [h1] using h2
  | .r lo hi :: ps, qs, l1, l2, h1, h2 => by
    obtain ⟨x, bs, rfl, a, b, h⟩ := h1
    exact ⟨x, bs ++ l2, rfl, a, b, loose_append ps qs bs l2 h h2⟩
  | .d :: ps, qs, l1, l2, h1, h2 => by
    rcases h1 with ⟨x, bs, rfl, a, h⟩ | ⟨u, bs, rfl, a, b, h⟩
    · exact Or.inl ⟨x, bs ++ l2, rfl, a, loose_append ps qs bs l2 h h2⟩
    · exact Or.inr ⟨u, bs ++ l2, by simp, a, b, loose_append ps qs bs l2 h h2⟩

theorem loose_digits : ∀ ds : List U8, ds.all Trusted.isAsciiDigit = true →
    Trusted.Pat.Loose (List.replicate ds.length .d) ds
  | [], _ => by simp [Trusted.Pat.Loose]
  | x :: ds, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact Or.inl ⟨x, ds, rfl, h.1, loose_digits ds h.2⟩

theorem loose_of_matchFrac (l : List U8) (h : Trusted.matchFrac l = true) :
    ∃ n, 1 ≤ n ∧ n ≤ 6 ∧ Trusted.Pat.Loose (Trusted.Pat.frac n) l := by
  match l with
  | [] => simp [Trusted.matchFrac] at h
  | b :: ds =>
    simp only [Trusted.matchFrac, Trusted.lit, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨ds.length, h.1.1.2, h.1.2, b, ds, rfl, by omega, by omega, loose_digits ds h.2⟩

theorem map_ymd : Trusted.ymd = Trusted.Pat.ymd.map patCls := by
  simp [Trusted.ymd, Trusted.Pat.ymd, patCls, lit_eq]

theorem map_ymdHms : Trusted.ymdHms = Trusted.Pat.ymdHms.map patCls := by
  simp [Trusted.ymdHms, Trusted.Pat.ymdHms, map_ymd, patCls, lit_eq]

theorem map_hhmmss : Trusted.hhmmss = Trusted.Pat.hhmmss.map patCls := by
  simp [Trusted.hhmmss, Trusted.mmss, Trusted.Pat.hhmmss, Trusted.Pat.mmss, patCls, lit_eq]

theorem map_hhhmmss : Trusted.hhhmmss = Trusted.Pat.hhhmmss.map patCls := by
  simp [Trusted.hhhmmss, Trusted.mmss, Trusted.Pat.hhhmmss, Trusted.Pat.mmss, patCls, lit_eq]

theorem loose_take_drop (ps : List Trusted.Pat) (l : List U8) (k : Nat)
    (h1 : Trusted.Pat.Loose ps (l.take k))
    (h2 : ∃ n, 1 ≤ n ∧ n ≤ 6 ∧ Trusted.Pat.Loose (Trusted.Pat.frac n) (l.drop k)) :
    ∃ n, 1 ≤ n ∧ n ≤ 6 ∧ Trusted.Pat.Loose (ps ++ Trusted.Pat.frac n) l := by
  obtain ⟨n, a, b, h2⟩ := h2
  refine ⟨n, a, b, ?_⟩
  have := loose_append _ _ _ _ h1 h2
  rwa [List.take_append_drop] at this

end mysql_common.NAUtil

namespace mysql_common

open NAUtil in
/-- Sanity check of `Trusted.isMatch_loose` against `Trusted.isMatch_ascii`: what a regex
    matches on ASCII input (`Regex.asciiMatch`) has the shape `Regex.Loose`. So on ASCII input
    `isMatch_loose` follows from `isMatch_ascii`; it is a new assumption only about input with a
    non-ASCII byte. -/
theorem Trusted.Regex.loose_of_asciiMatch (r : Trusted.Regex) (l : List U8)
    (h : r.asciiMatch l = true) : r.Loose l := by
  cases r <;> simp only [Trusted.Regex.asciiMatch, Bool.and_eq_true] at h <;>
    simp only [Trusted.Regex.Loose]
  · exact loose_of_matchSeq _ _ (map_ymd ▸ h)
  · exact loose_of_matchSeq _ _ (map_ymdHms ▸ h)
  · exact loose_take_drop _ _ 19 (loose_of_matchSeq _ _ (map_ymdHms ▸ h.1)) (loose_of_matchFrac _ h.2)
  · exact loose_of_matchSeq _ _ (map_hhmmss ▸ h)
  · exact loose_take_drop _ _ 8 (loose_of_matchSeq _ _ (map_hhmmss ▸ h.1)) (loose_of_matchFrac _ h.2)
  · exact loose_of_matchSeq _ _ (map_hhhmmss ▸ h)
  · exact loose_take_drop _ _ 9 (loose_of_matchSeq _ _ (map_hhhmmss ▸ h.1)) (loose_of_matchFrac _ h.2)

end mysql_common
