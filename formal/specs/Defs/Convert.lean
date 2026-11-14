import Defs.Value

/-!
# Value conversions: what each conversion means

The definitions the specs of `value::convert` (`FromValue`, `From<T> for Value`) are stated
with. They are written from the meaning of the values, not from the crate's code:

* **text numbers**: the ASCII decimal integers `[+-]?[0-9]+` (`asciiInt`) and the decimal
  representation of an integer (`decimalBytes`);
* **integers**: which `Value`s denote an integer (`Val.integer`), which of them a Rust integer
  type with range `[lo, hi]` accepts (`intConv`), and the `Value` that `From<T> for Value` makes
  of an integer (`intVal`);
* **UTF-8**: the bytes of a Lean `String` (`utf8`); a byte list is valid UTF-8 iff it is the
  `utf8` of some string (`IsUtf8`). Lean strings are sequences of Unicode scalar values and
  `String.toUTF8` is the standard encoding, so this is the definition std checks;
* **durations**: the number of nanoseconds a MySQL `TIME` denotes (`timeNanos`, signed:
  `timeSignedNanos`) and the `TIME` that a `std::time::Duration` (`durationTime`) or a
  `time::Duration` (`signedDurationTime`) is sent as;
* **MySQL date and time literals** (as text, in the formats of
  <https://dev.mysql.com/doc/refman/8.4/en/date-and-time-literals.html>, restricted to what the
  crate accepts): `timeStringRead` and `datetimeStringRead`.

All byte-level definitions are about ASCII: a byte `c` is the character with code `c.val`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ## ASCII digits and decimal integers -/

/-- `c` is an ASCII digit `'0'..'9'` (codes 48–57). -/
def isDigit (c : U8) : Bool := 48 ≤ c.val && c.val ≤ 57

/-- The value of a list of ASCII digits, most significant first: `digitsVal "042" = 42`. -/
def digitsVal (ds : List U8) : Nat := ds.foldl (fun acc d => 10 * acc + (d.val - 48)) 0

/-- `bs` is a non-empty list of ASCII digits. -/
def allDigits (bs : List U8) : Bool := !bs.isEmpty && bs.all isDigit

/-- The integer written by `bs` in the format `[+-]?[0-9]+`: an optional sign `+` (43) or `-`
    (45), then at least one ASCII digit, nothing else (no spaces). Leading zeros are allowed and
    `-0` is `0` (so an unsigned target type accepts `"-0"`, as btoi does). `none` for anything
    else. -/
def asciiInt : List U8 → Option Int
  | [] => none
  | c :: rest =>
    if c.val = 43 then (if allDigits rest then some (digitsVal rest) else none)
    else if c.val = 45 then (if allDigits rest then some (-(digitsVal rest : Int)) else none)
    else if allDigits (c :: rest) then some (digitsVal (c :: rest)) else none

/-- The shortest decimal representation of `n` in ASCII: a `-` if `n < 0`, then the digits of
    `|n|` without leading zeros (`"0"` for 0). This is Rust's `Display` for integers. -/
def decimalBytes (n : Int) : List U8 :=
  (if n < 0 then [byte 45] else []) ++ (Nat.toDigits 10 n.natAbs).map (fun c => byte c.toNat)

/-! ## Integers -/

/-- The integer a value denotes, for the integer conversions (`FromValue` for `i8`..`u128`,
    `isize`, `usize`): an `Int` or `UInt` is its number, `Bytes` holding an ASCII decimal integer
    (`asciiInt`) is that integer, and nothing else denotes an integer (not even `NULL`, floats,
    or a decimal with a fractional part). -/
def Val.integer : Val → Option Int
  | .int x => some x
  | .uint x => some x
  | .bytes b => asciiInt b
  | _ => none

/-- The integer a value converts to, for a Rust integer type with range `[lo, hi]`: the integer
    it denotes, if that is in range. -/
def intConv (lo hi : Int) (v : Val) : Option Int :=
  match v.integer with
  | some n => if lo ≤ n ∧ n ≤ hi then some n else none
  | none => none

/-- The intermediate result of the integer conversions (`ParseIrOpt<T>`), as
    `(parsed, n)`: `parsed` is `true` when the number was parsed from `Bytes` (the
    intermediate is then `Parsed n v`, keeping the original value) and `false` for an `Int` or
    `UInt` (`Ready n`). -/
def intIr (lo hi : Int) (v : Val) : Option (Bool × Int) :=
  (intConv lo hi v).map fun n => (match v with | .bytes _ => true | _ => false, n)

/-- A `ParseIrOpt<T>` read as `(parsed, number)`, given the number of a `T`. -/
def irView {T : Type} (f : T → Int) : value.convert.ParseIrOpt T → Bool × Int
  | .Ready t => (false, f t)
  | .Parsed t _ => (true, f t)

/-- The `Value` that `From<T> for Value` makes of the integer `n` of a Rust integer type
    (`signed` for `i8`..`i128`, `isize`): a signed type gives `Int n` when `n` fits in an `i64`;
    otherwise (and for every unsigned type) `UInt n` when `0 ≤ n < 2^64`; otherwise (only
    `i128`/`u128` values outside both ranges) `Bytes` of its decimal representation. -/
def intVal (signed : Bool) (n : Int) : Val :=
  if signed ∧ -2 ^ 63 ≤ n ∧ n < 2 ^ 63 then .int n
  else if 0 ≤ n ∧ n < 2 ^ 64 then .uint n.toNat
  else .bytes (decimalBytes n)

/-- What converting `v` to an integer type and back (`From<ParseIrOpt<T>> for Value` on the
    intermediate, or the error value on failure) gives: an `Int`/`UInt` in range comes back as
    `intVal signed n` (so e.g. `UInt 5` read as an `i8` comes back as `Int 5`); everything else,
    including `Bytes`, comes back unchanged. -/
def intRecover (lo hi : Int) (signed : Bool) (v : Val) : Val :=
  match v with
  | .int x => if lo ≤ x ∧ x ≤ hi then intVal signed x else v
  | .uint x => if lo ≤ (x : Int) ∧ (x : Int) ≤ hi then intVal signed x else v
  | _ => v

/-! ## UTF-8 -/

/-- The UTF-8 encoding of a string (Rust's `String::as_bytes`/`into_bytes`). -/
def utf8 (s : String) : List U8 := s.toUTF8.data.toList.map fun b => byte b.toNat

/-- `bs` is valid UTF-8: the encoding of some string (of Unicode scalar values). -/
def IsUtf8 (bs : List U8) : Prop := ∃ s : String, utf8 s = bs

/-! ## Durations and MySQL `TIME` -/

/-- The length of a `std::time::Duration` in nanoseconds. (A `Duration` is determined by it:
    `secs = n / 10^9` and `nanos = n % 10^9`.) -/
def durNanos (d : core.time.Duration) : Nat := d.secs.val * 10 ^ 9 + d.nanos.val

/-- The nanoseconds of the (non-negative) MySQL `TIME` `days hours:minutes:seconds.micros`,
    without range checks on the fields. -/
def timeNanos (days hours minutes seconds micros : Nat) : Nat :=
  (((days * 24 + hours) * 60 + minutes) * 60 + seconds) * 10 ^ 9 + micros * 1000

/-- The `TIME` value that `From<Duration> for Value` makes of a duration of `secs` seconds and
    `nanos < 10^9` nanoseconds: non-negative (sign flag false), the seconds split into days, hours, minutes and
    seconds, the nanoseconds rounded to the nearest microsecond (half up). Two departures from a
    faithful `TIME`, both the crate's behaviour:
    * the rounding is not carried: `nanos ≥ 999_999_500` gives `micros = 1_000_000`;
    * the days are truncated to `u32` (`as u32`): durations of `2^32` days or more wrap. -/
def durationTime (secs nanos : Nat) : Val :=
  .time false ((secs / 86400) % 2 ^ 32) ((secs % 86400) / 3600) ((secs % 3600) / 60) (secs % 60)
    ((nanos + 500) / 1000)

/-- The signed nanoseconds of the MySQL `TIME` `[-]days hours:minutes:seconds.micros`, without
    range checks on the fields: `timeNanos`, negated when the sign flag is set (a negative zero
    is 0). -/
def timeSignedNanos (neg : Bool) (days hours minutes seconds micros : Nat) : Int :=
  if neg then -(timeNanos days hours minutes seconds micros : Int)
  else (timeNanos days hours minutes seconds micros : Int)

/-- The `TIME` value that `From<time::Duration> for Value` makes of a duration of `n`
    nanoseconds (`n` may be negative): the sign flag is `n < 0`, and `|n|` is split into days,
    hours (`< 24`), minutes (`< 60`), seconds (`< 60`) and microseconds (`< 10^6`). Two
    departures from a faithful `TIME`, both the crate's behaviour:
    * nanoseconds below a microsecond are dropped (truncated toward zero);
    * the days are truncated to `u32` (`as u32`): durations of `2^32` days or more wrap. -/
def signedDurationTime (n : Int) : Val :=
  let secs := n.natAbs / 10 ^ 9
  .time (decide (n < 0)) ((secs / 86400) % 2 ^ 32) ((secs % 86400) / 3600) ((secs % 3600) / 60)
    (secs % 60) ((n.natAbs % 10 ^ 9) / 1000)

/-! ## MySQL date and time literals (text) -/

/-- An optional fractional part `.f`, `f` one to six ASCII digits, as microseconds (the digits
    are the leading digits of the six-digit microsecond count: `.5` is 500000 µs, `.000123` is
    123 µs). The empty list is no fraction (0 µs); anything else is `none`. -/
def fracRead : List U8 → Option Nat
  | [] => some 0
  | c :: ds =>
    if c.val = 46 ∧ 1 ≤ ds.length ∧ ds.length ≤ 6 ∧ ds.all isDigit then
      some (digitsVal ds * 10 ^ (6 - ds.length))
    else none

/-- `c` is an ASCII digit from `'0'` up to the digit `d`. -/
def digitUpTo (d : Nat) (c : U8) : Bool := 48 ≤ c.val && c.val ≤ 48 + d

/-- The text `TIME` literals the crate reads (`parse_mysql_time_string`), on ASCII input, as
    `(negative, hours, minutes, seconds, microseconds)`: `[-]HH:MM:SS[.f]` or `[-]HHH:MM:SS[.f]`
    where `HH` is any two digits, `HHH` three digits whose first is `0`–`8` (so hours up to 899,
    MySQL's `TIME` range is ±838:59:59), `MM` and `SS` two digits whose first is `0`–`5`, and `f`
    one to six digits (`fracRead`). Unlike MySQL, the crate does not accept a days part
    (`D HH:MM:SS`), single-digit fields, or the forms without colons (`HHMMSS`). -/
def timeStringRead (bs : List U8) : Option (Bool × Nat × Nat × Nat × Nat) :=
  let (neg, t) : Bool × List U8 :=
    match bs with
    | c :: rest => if c.val = 45 then (true, rest) else (false, bs)
    | [] => (false, [])
  -- the hours, and what follows them
  let hours : Option (Nat × List U8) :=
    match t with
    | h1 :: h2 :: h3 :: rest =>
      if digitUpTo 8 h1 ∧ isDigit h2 ∧ isDigit h3 then some (digitsVal [h1, h2, h3], rest)
      else if isDigit h1 ∧ isDigit h2 then some (digitsVal [h1, h2], h3 :: rest)
      else none
    | _ => none
  match hours with
  | some (h, c1 :: m1 :: m2 :: c2 :: s1 :: s2 :: frac) =>
    if c1.val = 58 ∧ c2.val = 58 ∧ digitUpTo 5 m1 ∧ isDigit m2 ∧ digitUpTo 5 s1 ∧ isDigit s2 then
      (fracRead frac).map fun us => (neg, h, digitsVal [m1, m2], digitsVal [s1, s2], us)
    else none
  | _ => none

/-- The text `DATE`/`DATETIME` literals the crate reads (`parse_mysql_datetime_string`), on
    ASCII input, as `(year, month, day, hour, minute, second, microsecond)`: `YYYY-MM-DD`,
    `YYYY-MM-DD hh:mm:ss` and `YYYY-MM-DD hh:mm:ss.f` (`f` one to six digits, `fracRead`), with
    exactly these digit counts and separators; time fields absent are 0. The fields are not
    range-checked here (any digits are accepted; the callers check them). MySQL forms the crate
    does **not** accept: the `T` separator (`2024-01-31T12:00:00`), two-digit years, relaxed or
    other delimiters (`2024/01/31`, `2024-1-31`), the forms without delimiters (`YYYYMMDD`,
    `YYYYMMDDhhmmss`), and more than six fractional digits. -/
def datetimeStringRead (bs : List U8) : Option (Nat × Nat × Nat × Nat × Nat × Nat × Nat) :=
  match bs with
  | y1 :: y2 :: y3 :: y4 :: d1 :: mo1 :: mo2 :: d2 :: dd1 :: dd2 :: rest =>
    if allDigits [y1, y2, y3, y4, mo1, mo2, dd1, dd2] ∧ d1.val = 45 ∧ d2.val = 45 then
      let y := digitsVal [y1, y2, y3, y4]
      let mo := digitsVal [mo1, mo2]
      let d := digitsVal [dd1, dd2]
      match rest with
      | [] => some (y, mo, d, 0, 0, 0, 0)
      | sp :: h1 :: h2 :: c1 :: mi1 :: mi2 :: c2 :: s1 :: s2 :: frac =>
        if sp.val = 32 ∧ c1.val = 58 ∧ c2.val = 58 ∧ allDigits [h1, h2, mi1, mi2, s1, s2] then
          (fracRead frac).map fun us =>
            (y, mo, d, digitsVal [h1, h2], digitsVal [mi1, mi2], digitsVal [s1, s2], us)
        else none
      | _ => none
    else none
  | _ => none

/-! ## Where the date/time text parsers panic

The crate's regexes run in Unicode mode, so `\d` also matches non-ASCII decimal digits, which
`btou(..).unwrap()` then rejects with a panic. Which non-ASCII byte sequences are digits is
not modelled, so these conditions are stated with the opaque `Trusted.isMatch`
(`REGEX.is_match`). Both are false of ASCII input, and `timeStringRead`/`datetimeStringRead`
are `none` on every input they are true of (and on every other input with a non-ASCII byte). -/

/-- `parse_mysql_time_string` panics on `bs`: `bs` has a non-ASCII byte and, after an optional
    leading `-` (45), is matched by one of the two fractional regexes (`TIME_RE_HH_MM_SS_MS`,
    `TIME_RE_HHH_MM_SS_MS`), e.g. `"00:00:00.\u{0660}"`. (`t` is the input after the sign, as
    a slice.) -/
def timeTextPanics (bs : List U8) : Prop :=
  (∃ c ∈ bs, 128 ≤ c.val) ∧
  ∃ t : Slice U8,
    t.val = (match bs with
      | c :: rest => if c.val = 45 then rest else bs
      | [] => []) ∧
    (Trusted.isMatch .timeHhMmSsMs t = true ∨ Trusted.isMatch .timeHhhMmSsMs t = true)

/-- `parse_mysql_datetime_string` panics on `bs`: `bs` has a non-ASCII byte, is 21 to 26 bytes
    long and is matched by the fractional regex (`DATETIME_RE_YMD_HMS_NS`), e.g.
    `"2020-01-01 00:00:00.\u{0660}"`. (`t` is the input as a slice.) -/
def datetimeTextPanics (bs : List U8) : Prop :=
  (∃ c ∈ bs, 128 ≤ c.val) ∧ 20 < bs.length ∧ bs.length < 27 ∧
  ∃ t : Slice U8, t.val = bs ∧ Trusted.isMatch .datetimeYmdHmsNs t = true

/-- The value is `Bytes` on which `parse_mysql_time_string` panics (`timeTextPanics`); false of
    every other value. -/
def Val.timeTextPanics : Val → Prop
  | .bytes b => Defs.timeTextPanics b
  | _ => False

/-- The value is `Bytes` on which `parse_mysql_datetime_string` panics (`datetimeTextPanics`);
    false of every other value. -/
def Val.datetimeTextPanics : Val → Prop
  | .bytes b => Defs.datetimeTextPanics b
  | _ => False

/-! ## What the temporal conversions read from a `Value` -/

/-- The nanoseconds of the non-negative duration a value denotes, for `FromValue for
    std::time::Duration`: a non-negative (sign flag false) `TIME` (`timeNanos`, fields not range-checked), or `Bytes`
    holding a non-negative text `TIME` literal (`timeStringRead`); `none` for anything else,
    including every negative `TIME` (even a negative zero). -/
def Val.durationNanos : Val → Option Nat
  | .time false d h m s us => some (timeNanos d h m s us)
  | .bytes b =>
    match timeStringRead b with
    | some (false, h, m, s, us) => some (timeNanos 0 h m s us)
    | _ => none
  | _ => none

/-- The signed nanoseconds of the duration a value denotes, for `FromValue for time::Duration`:
    any `TIME` (`timeSignedNanos`, fields not range-checked), or `Bytes` holding a text `TIME`
    literal (`timeStringRead`, which has no days part); `none` for anything else. -/
def Val.signedDurationNanos : Val → Option Int
  | .time neg d h m s us => some (timeSignedNanos neg d h m s us)
  | .bytes b => (timeStringRead b).map fun t => timeSignedNanos t.1 0 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
  | _ => none

/-- The calendar fields `(year, month, day, hour, minute, second, microsecond)` a value denotes,
    for the chrono date-time conversions (`NaiveDateTime`, `NaiveDate`): a `Date`, or `Bytes` holding a text `DATE`/`DATETIME` literal
    (`datetimeStringRead`); `none` for anything else. Not range-checked. -/
def Val.dateTimeFields : Val → Option (Nat × Nat × Nat × Nat × Nat × Nat × Nat)
  | .date y mo d h mi s us => some (y, mo, d, h, mi, s, us)
  | .bytes b => datetimeStringRead b
  | _ => none

/-- The time-of-day fields `(hour, minute, second, microsecond)` a value denotes, for the
    chrono time-of-day conversion (`NaiveTime`): a non-negative (sign flag false) `TIME` with 0 days, or `Bytes` holding a non-negative text
    `TIME` literal (`timeStringRead`); `none` for anything else. Not range-checked. -/
def Val.timeOfDayFields : Val → Option (Nat × Nat × Nat × Nat)
  | .time false 0 h m s us => some (h, m, s, us)
  | .bytes b =>
    match timeStringRead b with
    | some (false, h, m, s, us) => some (h, m, s, us)
    | _ => none
  | _ => none

/-! ## The observable fields of the opaque chrono and time values

chrono's and time's types are opaque (`TypesExternal.lean`); the specs speak about them only
through their getters (the `Trusted` axioms of `FunsExternal.lean`). -/

/-- A `chrono::NaiveDate` as `(year, month, day)`. -/
noncomputable def chronoDate (d : chrono.naive.date.NaiveDate) : Int × Nat × Nat :=
  ((Trusted.NaiveDate.year d).val, (Trusted.NaiveDate.month d).val, (Trusted.NaiveDate.day d).val)

/-- A `chrono::NaiveTime` as `(hour, minute, second, nanosecond)`. -/
noncomputable def chronoTime (t : chrono.naive.time.NaiveTime) : Nat × Nat × Nat × Nat :=
  ((Trusted.NaiveTime.hour t).val, (Trusted.NaiveTime.minute t).val,
    (Trusted.NaiveTime.second t).val, (Trusted.NaiveTime.nanosecond t).val)

/-- A `chrono::NaiveDateTime` as its date and its time. -/
noncomputable def chronoDateTime (x : chrono.naive.datetime.NaiveDateTime) :
    (Int × Nat × Nat) × (Nat × Nat × Nat × Nat) :=
  (chronoDate (Trusted.NaiveDateTime.date x), chronoTime (Trusted.NaiveDateTime.time x))

/-- A `time::Date` as `(year, month, day)` (month as its number 1–12). -/
noncomputable def timeDate (d : time.date.Date) : Int × Nat × Nat :=
  ((Trusted.Date.year d).val, Trusted.monthNumber (Trusted.Date.month d), (Trusted.Date.day d).val)

/-- A `time::Time` as `(hour, minute, second, microsecond)`. -/
noncomputable def timeTime (t : time.time.Time) : Nat × Nat × Nat × Nat :=
  ((Trusted.Time.hour t).val, (Trusted.Time.minute t).val, (Trusted.Time.second t).val,
    (Trusted.Time.microsecond t).val)

/-- A `time::PrimitiveDateTime` as its date and its time. -/
noncomputable def timeDateTime (x : time.plain_date_time.PlainDateTime) :
    (Int × Nat × Nat) × (Nat × Nat × Nat × Nat) :=
  (timeDate (Trusted.PrimitiveDateTime.date x), timeTime (Trusted.PrimitiveDateTime.time x))

/-- `time::Date::from_calendar_date(year, month, day)` succeeds (time 0.3, `large-dates` off:
    years `-9999..=9999`), for a month number. -/
def timeDateValid (y : Int) (mo d : Nat) : Prop :=
  1 ≤ mo ∧ mo ≤ 12 ∧ -9999 ≤ y ∧ y ≤ 9999 ∧ 1 ≤ d ∧ d ≤ Trusted.daysInMonth y mo

/-- `time::Time::from_hms_micro(hour, minute, second, micro)` succeeds. -/
def timeTimeValid (h m s us : Nat) : Prop := h < 24 ∧ m < 60 ∧ s < 60 ∧ us < 1000000

end Defs
