import Defs

/-! Statements for `Value::as_sql` (spec file: `Specs/Value/AsSql.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `as_sql(NULL)` is `NULL`. -/
theorem value.Value.as_sql_null (nbe : Bool) :
    value.Value.as_sql .NULL nbe ⦃ r => utf8 r = ascii "NULL" ⦄ := by
  sorry

/-- `as_sql(Int x)`: the decimal representation of `x` (with `-` if negative). -/
theorem value.Value.as_sql_int (x : I64) (nbe : Bool) :
    value.Value.as_sql (.Int x) nbe ⦃ r => utf8 r = decimalBytes x.val ⦄ := by
  sorry

/-- `as_sql(UInt x)`: the decimal representation of `x`. -/
theorem value.Value.as_sql_uint (x : U64) (nbe : Bool) :
    value.Value.as_sql (.UInt x) nbe ⦃ r => utf8 r = decimalBytes x.val ⦄ := by
  sorry

/-- `as_sql(Float x)`: Rust's `Display` of the `f32` (opaque: `Trusted.f32Display`). -/
theorem value.Value.as_sql_float (x : F32) (nbe : Bool) :
    value.Value.as_sql (.Float x) nbe ⦃ r => r = Trusted.f32Display x ⦄ := by
  sorry

/-- `as_sql(Double x)`: Rust's `Display` of the `f64` (opaque: `Trusted.f64Display`). -/
theorem value.Value.as_sql_double (x : F64) (nbe : Bool) :
    value.Value.as_sql (.Double x) nbe ⦃ r => r = Trusted.f64Display x ⦄ := by
  sorry

/-- `as_sql(Date ..)`: the quoted literal `dateSql` (date only if the time part is zero; the
    fraction only if non-zero). Never panics. -/
theorem value.Value.as_sql_date (y : U16) (mo d h mi s : U8) (us : U32) (nbe : Bool) :
    value.Value.as_sql (.Date y mo d h mi s us) nbe ⦃ r =>
      utf8 r = dateSql y.val mo.val d.val h.val mi.val s.val us.val ⦄ := by
  sorry

/-- `as_sql(Time ..)` when `24·days + hours` fits in a `u32`: the quoted literal `timeSql`. -/
theorem value.Value.as_sql_time (neg : Bool) (d : U32) (h mi s : U8) (us : U32) (nbe : Bool)
    (hfit : d.val * 24 + h.val ≤ U32.max) :
    value.Value.as_sql (.Time neg d h mi s us) nbe ⦃ r =>
      utf8 r = timeSql neg d.val h.val mi.val s.val us.val ⦄ := by
  sorry

/-- `as_sql(Time ..)` panics (`u32` overflow of `days * 24 + hours`) exactly when the hours do
    not fit in a `u32`, i.e. for `days ≥ 178956971`, or `days = 178956970` and `hours ≥ 16`.
    (In release builds it would wrap instead.) -/
theorem value.Value.as_sql_time_overflow (neg : Bool) (d : U32) (h mi s : U8) (us : U32)
    (nbe : Bool) (hover : U32.max < d.val * 24 + h.val) :
    value.Value.as_sql (.Time neg d h mi s us) nbe = fail .integerOverflow := by
  sorry

/-- `as_sql(Bytes b)` for `b` valid UTF-8: the MySQL string literal `quoteSql nbe b`. -/
theorem value.Value.as_sql_bytes_utf8 (b : alloc.vec.Vec U8) (nbe : Bool) (h : IsUtf8 b.val) :
    value.Value.as_sql (.Bytes b) nbe ⦃ r => utf8 r = quoteSql nbe b.val ⦄ := by
  sorry

/-- `as_sql(Bytes b)` for `b` not valid UTF-8: the hexadecimal literal `0x…` of `b` (upper-case
    digits; only the bytes `0`–`9`, `A`–`F`, `x`). -/
theorem value.Value.as_sql_bytes_hex (b : alloc.vec.Vec U8) (nbe : Bool) (h : ¬ IsUtf8 b.val) :
    value.Value.as_sql (.Bytes b) nbe ⦃ r => utf8 r = hexLit b.val ⦄ := by
  sorry

/-- **Security headline.** For `Bytes b` with `b` valid UTF-8, `as_sql` is one SQL string
    literal, read back by the server (in the same `NO_BACKSLASH_ESCAPES` mode `nbe`) as exactly
    `b`, ending exactly where the output ends, whatever SQL text follows it (unless that text
    starts with `'`, which would continue the literal as `''`). So the value cannot terminate
    the literal early or inject SQL. The reading is byte-wise: valid for connection character
    sets in which 0x27 and 0x5C are always `'` and `\` (e.g. utf8mb4, latin1), not for
    `big5`/`cp932`/`gbk`/`gb18030`/`sjis` (see `Defs/SqlText.lean`). -/
theorem value.Value.as_sql_bytes_literal (b : alloc.vec.Vec U8) (nbe : Bool) (h : IsUtf8 b.val) :
    value.Value.as_sql (.Bytes b) nbe ⦃ r =>
      ∀ rest : List U8, rest.head?.map (·.val) ≠ some 39 →
        sqlStrLit nbe (utf8 r ++ rest) = some (b.val, rest) ⦄ := by
  sorry

end mysql_common
