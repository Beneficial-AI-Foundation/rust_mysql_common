import Proofs.Value.Escaped
import Proofs.Value.AsSql

/-!
# `src/value/mod.rs`: `Value::as_sql` and `fn escaped`
    (In a separate file from `Specs/Value.lean` so as not to edit that file while other areas
    are specified; it belongs there, in source order: `escaped` before `as_sql`.) Patches
    84–86: `escaped` loops over bytes instead of `char`s (equivalent, all compared and inserted
    characters are ASCII); every `format!` goes through `sql_trusted`.

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/SqlText.lean` §3 (`quoteSql`, `sqlStrLit`, `hexLit`, `dateSql`,
    `timeSql`, `ascii`), `Defs/Convert.lean` (`utf8`, `IsUtf8`, `decimalBytes`).

    **Trusted axioms:** none, except `Trusted.f32Display` / `Trusted.f64Display` (opaque float
    `Display`) for `as_sql_float` / `as_sql_double`.

    **What is stated.** The exact output for every variant; the `u32` overflow panic of
    `24·days + hours` for `Time` (exactly when it does not fit); the security headline
    `as_sql_bytes_literal`: valid-UTF-8 `Bytes` become one string literal that the server reads
    back as the same bytes and that ends exactly at the end of the output (both
    `no_backslash_escape` modes); invalid UTF-8 becomes an `0x…` hex literal.

    **Behaviour to note.**
    - Security caveat: the literal is safe only for connection character sets in which bytes
      0x27/0x5C are always `'`/`\`; with `gbk`, `big5`, `sjis`, `cp932`, `gb18030` a valid UTF-8
      string such as `"¿'"` (C2 BF 27, escaped C2 BF 5C 27) has BF 5C read as one character,
      leaving `'` unescaped in backslash mode.
    - No range checks: out-of-range dates/times are printed as given (year 10000, month 13,
      micros ≥ 10⁶ printed with 7+ digits, TIME beyond 838:59:59).
    - `Float`/`Double` use Rust's `Display`, unverified here: NaN and infinities print as
      `NaN`/`inf`, which are not SQL literals.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `fn escaped` -/

/-- `escaped(s, nbe)`: exactly the MySQL quoting `quoteSql nbe` of the bytes of `s`. (A Rust
    `&str` is always valid UTF-8; for a `Str` that is not, the final `from_utf8` would fail and
    this panics, which cannot happen from Rust.) -/
recall value.escaped_spec (s : Str) (nbe : Bool) (h : IsUtf8 s.val) :
    value.escaped s nbe ⦃ r => utf8 r = quoteSql nbe s.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.escaped_spec`

/-! ### `Value::as_sql` -/

/-- `as_sql(NULL)` is `NULL`. -/
recall value.Value.as_sql_null (nbe : Bool) :
    value.Value.as_sql .NULL nbe ⦃ r => utf8 r = ascii "NULL" ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.as_sql_null`

/-- `as_sql(Int x)`: the decimal representation of `x` (with `-` if negative). -/
recall value.Value.as_sql_int (x : I64) (nbe : Bool) :
    value.Value.as_sql (.Int x) nbe ⦃ r => utf8 r = decimalBytes x.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.as_sql_int`

/-- `as_sql(UInt x)`: the decimal representation of `x`. -/
recall value.Value.as_sql_uint (x : U64) (nbe : Bool) :
    value.Value.as_sql (.UInt x) nbe ⦃ r => utf8 r = decimalBytes x.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.as_sql_uint`

/-- `as_sql(Float x)`: Rust's `Display` of the `f32` (opaque: `Trusted.f32Display`). -/
recall value.Value.as_sql_float (x : F32) (nbe : Bool) :
    value.Value.as_sql (.Float x) nbe ⦃ r => r = Trusted.f32Display x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.as_sql_float`

/-- `as_sql(Double x)`: Rust's `Display` of the `f64` (opaque: `Trusted.f64Display`). -/
recall value.Value.as_sql_double (x : F64) (nbe : Bool) :
    value.Value.as_sql (.Double x) nbe ⦃ r => r = Trusted.f64Display x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.as_sql_double`

/-- `as_sql(Date ..)`: the quoted literal `dateSql` (date only if the time part is zero; the
    fraction only if non-zero). Never panics. -/
recall value.Value.as_sql_date (y : U16) (mo d h mi s : U8) (us : U32) (nbe : Bool) :
    value.Value.as_sql (.Date y mo d h mi s us) nbe ⦃ r =>
      utf8 r = dateSql y.val mo.val d.val h.val mi.val s.val us.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.as_sql_date`

/-- `as_sql(Time ..)` when `24·days + hours` fits in a `u32`: the quoted literal `timeSql`. -/
recall value.Value.as_sql_time (neg : Bool) (d : U32) (h mi s : U8) (us : U32) (nbe : Bool)
    (hfit : d.val * 24 + h.val ≤ U32.max) :
    value.Value.as_sql (.Time neg d h mi s us) nbe ⦃ r =>
      utf8 r = timeSql neg d.val h.val mi.val s.val us.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.as_sql_time`

/-- `as_sql(Time ..)` panics (`u32` overflow of `days * 24 + hours`) exactly when the hours do
    not fit in a `u32`, i.e. for `days ≥ 178956971`, or `days = 178956970` and `hours ≥ 16`.
    (In release builds it would wrap instead.) -/
recall value.Value.as_sql_time_overflow (neg : Bool) (d : U32) (h mi s : U8) (us : U32)
    (nbe : Bool) (hover : U32.max < d.val * 24 + h.val) :
    value.Value.as_sql (.Time neg d h mi s us) nbe = fail .integerOverflow

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.as_sql_time_overflow`

/-- `as_sql(Bytes b)` for `b` valid UTF-8: the MySQL string literal `quoteSql nbe b`. -/
recall value.Value.as_sql_bytes_utf8 (b : alloc.vec.Vec U8) (nbe : Bool) (h : IsUtf8 b.val) :
    value.Value.as_sql (.Bytes b) nbe ⦃ r => utf8 r = quoteSql nbe b.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.as_sql_bytes_utf8`

/-- `as_sql(Bytes b)` for `b` not valid UTF-8: the hexadecimal literal `0x…` of `b` (upper-case
    digits; only the bytes `0`–`9`, `A`–`F`, `x`). -/
recall value.Value.as_sql_bytes_hex (b : alloc.vec.Vec U8) (nbe : Bool) (h : ¬ IsUtf8 b.val) :
    value.Value.as_sql (.Bytes b) nbe ⦃ r => utf8 r = hexLit b.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.as_sql_bytes_hex`

/-- **Security headline.** For `Bytes b` with `b` valid UTF-8, `as_sql` is one SQL string
    literal, read back by the server (in the same `NO_BACKSLASH_ESCAPES` mode `nbe`) as exactly
    `b`, ending exactly where the output ends, whatever SQL text follows it (unless that text
    starts with `'`, which would continue the literal as `''`). So the value cannot terminate
    the literal early or inject SQL. The reading is byte-wise: valid for connection character
    sets in which 0x27 and 0x5C are always `'` and `\` (e.g. utf8mb4, latin1), not for
    `big5`/`cp932`/`gbk`/`gb18030`/`sjis` (see `Defs/SqlText.lean`). -/
recall value.Value.as_sql_bytes_literal (b : alloc.vec.Vec U8) (nbe : Bool) (h : IsUtf8 b.val) :
    value.Value.as_sql (.Bytes b) nbe ⦃ r =>
      ∀ rest : List U8, rest.head?.map (·.val) ≠ some 39 →
        sqlStrLit nbe (utf8 r ++ rest) = some (b.val, rest) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.as_sql_bytes_literal`

end mysql_common
