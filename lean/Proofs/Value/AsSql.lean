import Defs
import Proofs.Util.ParamsAsSql
import Proofs.Value.Escaped
import Proofs.Defs.LemmasSqlText

/-! Statements for `Value::as_sql` (spec file: `Specs/Value/AsSql.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

open PASUtil

private theorem isUtf8_iff_valid (bs : List U8) : IsUtf8 bs ↔ (Trusted.bytesOf bs).IsValidUTF8 := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [CBTUtil.bytesOf_utf8]; exact t.isValidUTF8
  · intro h; exact ⟨_, CBTUtil.utf8_ofByteArray bs h⟩

private theorem as_sql_loop_spec (bytes : alloc.vec.Vec U8) :
    ∀ (n : Nat) (s : String) (k : Usize), bytes.length - k.val = n → k.val ≤ bytes.length →
    value.Value.as_sql_loop bytes s k ⦃ r => utf8 r = utf8 s ++
      (bytes.val.drop k.val).flatMap (fun b => [hexDigit (b.val / 16), hexDigit (b.val % 16)]) ⦄ := by
  intro n
  induction n with
  | zero =>
    intro s k hn hk
    unfold value.Value.as_sql_loop
    rw [loop]
    simp only
    rw [value.Value.as_sql_loop.body]
    have : ¬ k.val < bytes.length := by omega
    have hd : bytes.val.drop k.val = [] := by
      apply List.drop_eq_nil_of_le; simp only [alloc.vec.Vec.length] at this; omega
    simp [this, hd]
  | succ n ih =>
    intro s k hn hk
    unfold value.Value.as_sql_loop
    rw [loop]
    simp only
    rw [value.Value.as_sql_loop.body]
    have hlt : k.val < bytes.length := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp only [alloc.vec.Vec.len]; exact hlt))]
    step as ⟨c, hc⟩
    simp only [sql_trusted.format_hex_upper_02, sql_trusted.string_extend_chars, Std.bind_ok]
    step as ⟨k1, hk1⟩
    have := ih (s ++ Trusted.hexByteUpper c.val) k1 (by omega) (by omega)
    refine WP.spec_mono this ?_
    intro r hr
    have hdrop : bytes.val.drop k.val = c :: bytes.val.drop (k.val + 1) := by
      rw [hc]; exact List.drop_eq_getElem_cons _
    rw [hr, hdrop, hk1, utf8_append, utf8_hexByteUpper _ (by scalar_tac)]
    simp

/-- `as_sql(NULL)` is `NULL`. -/
theorem value.Value.as_sql_null (nbe : Bool) :
    value.Value.as_sql .NULL nbe ⦃ r => utf8 r = ascii "NULL" ⦄ := by
  unfold value.Value.as_sql
  simp [str_null, ascii]

/-- `as_sql(Int x)`: the decimal representation of `x` (with `-` if negative). -/
theorem value.Value.as_sql_int (x : I64) (nbe : Bool) :
    value.Value.as_sql (.Int x) nbe ⦃ r => utf8 r = decimalBytes x.val ⦄ := by
  unfold value.Value.as_sql
  simp only [sql_trusted.format_i64, WP.spec_ok]
  exact utf8_toString_int x.val

/-- `as_sql(UInt x)`: the decimal representation of `x`. -/
theorem value.Value.as_sql_uint (x : U64) (nbe : Bool) :
    value.Value.as_sql (.UInt x) nbe ⦃ r => utf8 r = decimalBytes x.val ⦄ := by
  unfold value.Value.as_sql
  simp only [sql_trusted.format_u64, WP.spec_ok]
  exact utf8_toString_int (x.val : _root_.Int)

/-- `as_sql(Float x)`: Rust's `Display` of the `f32` (opaque: `Trusted.f32Display`). -/
theorem value.Value.as_sql_float (x : F32) (nbe : Bool) :
    value.Value.as_sql (.Float x) nbe ⦃ r => r = Trusted.f32Display x ⦄ := by
  unfold value.Value.as_sql
  simp [sql_trusted.format_f32]

/-- `as_sql(Double x)`: Rust's `Display` of the `f64` (opaque: `Trusted.f64Display`). -/
theorem value.Value.as_sql_double (x : F64) (nbe : Bool) :
    value.Value.as_sql (.Double x) nbe ⦃ r => r = Trusted.f64Display x ⦄ := by
  unfold value.Value.as_sql
  simp [sql_trusted.format_f64]

/-- `as_sql(Date ..)`: the quoted literal `dateSql` (date only if the time part is zero; the
    fraction only if non-zero). Never panics. -/
theorem value.Value.as_sql_date (y : U16) (mo d h mi s : U8) (us : U32) (nbe : Bool) :
    value.Value.as_sql (.Date y mo d h mi s us) nbe ⦃ r =>
      utf8 r = dateSql y.val mo.val d.val h.val mi.val s.val us.val ⦄ := by
  unfold value.Value.as_sql
  simp only
  repeat' split
  all_goals
    simp only [sql_trusted.format_date, sql_trusted.format_datetime, sql_trusted.format_datetime_micros,
      WP.spec_ok, utf8_append, utf8_padDec, dateSql]
  all_goals
    simp_all only [UScalar.eq_equiv, imp_false, uscalar_mk_val]
    simp_all [ascii]

/-- `as_sql(Time ..)` when `24·days + hours` fits in a `u32`: the quoted literal `timeSql`. -/
theorem value.Value.as_sql_time (neg : Bool) (d : U32) (h mi s : U8) (us : U32) (nbe : Bool)
    (hfit : d.val * 24 + h.val ≤ U32.max) :
    value.Value.as_sql (.Time neg d h mi s us) nbe ⦃ r =>
      utf8 r = timeSql neg d.val h.val mi.val s.val us.val ⦄ := by
  unfold value.Value.as_sql
  simp only
  have h24 : d.val * 24 ≤ U32.max := by omega
  have hh : h.val % 2 ^ UScalarTy.U32.numBits = h.val := Nat.mod_eq_of_lt (by scalar_tac)
  have hq : utf8 "'-" = utf8 "'" ++ utf8 "-" := by decide
  split
  all_goals
    split
    all_goals
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      simp only [sql_trusted.format_time, sql_trusted.format_time_neg, sql_trusted.format_time_micros,
        sql_trusted.format_time_micros_neg, WP.spec_ok, utf8_append, utf8_padDec, timeSql]
      simp_all only [UScalar.eq_equiv, imp_false, uscalar_mk_val, UScalar.cast_val_eq]
      simp_all [ascii]

/-- `as_sql(Time ..)` panics (`u32` overflow of `days * 24 + hours`) exactly when the hours do
    not fit in a `u32` (with `as_sql_time`, an exact split). For `hours < 24` (a valid TIME
    value) that is `days ≥ 178956971`, or `days = 178956970` and `hours ≥ 16`; `hours` is an
    unchecked `u8`. (In release builds it would wrap instead.) -/
theorem value.Value.as_sql_time_overflow (neg : Bool) (d : U32) (h mi s : U8) (us : U32)
    (nbe : Bool) (hover : U32.max < d.val * 24 + h.val) :
    value.Value.as_sql (.Time neg d h mi s us) nbe = fail .integerOverflow := by
  unfold value.Value.as_sql
  simp only
  by_cases h24 : U32.max < d.val * 24
  · have hm : d * 24#u32 = fail .integerOverflow := CBTUtil.umul_overflow _ _ (by scalar_tac)
    split <;> split <;> simp [hm]
  · obtain ⟨z, hz, hzv⟩ := CBTUtil.spec_exists_ok (U32.mul_spec (x := d) (y := 24#u32) (by scalar_tac))
    have ha : z + UScalar.cast .U32 h = fail .integerOverflow := uadd_overflow _ _ (by
      rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt (by scalar_tac)]; scalar_tac)
    split <;> split <;> simp [hz, lift, ha]

/-- `as_sql(Bytes b)` for `b` valid UTF-8: the MySQL string literal `quoteSql nbe b`. -/
theorem value.Value.as_sql_bytes_utf8 (b : alloc.vec.Vec U8) (nbe : Bool) (h : IsUtf8 b.val)
    (hlen : (quoteSql nbe b.val).length ≤ Usize.max) :
    value.Value.as_sql (.Bytes b) nbe ⦃ r => utf8 r = quoteSql nbe b.val ⦄ := by
  unfold value.Value.as_sql
  simp only
  step with (show value.convert.trusted.str_from_utf8 (alloc.vec.Vec.deref b) ⦃ o =>
      o = some (alloc.vec.Vec.deref b) ⦄ by
    have : (Trusted.bytesOf (alloc.vec.Vec.deref b).val).IsValidUTF8 := by
      rw [CBTUtil.vec_deref_val, ← isUtf8_iff_valid]; exact h
    simp only [value.convert.trusted.str_from_utf8, this, ↓reduceIte, WP.spec_ok]
    exact rfl) as ⟨o, ho⟩
  subst ho
  simp only
  have := value.escaped_spec (alloc.vec.Vec.deref b) nbe (by rw [CBTUtil.vec_deref_val]; exact h)
    (by rw [CBTUtil.vec_deref_val]; exact hlen)
  rw [CBTUtil.vec_deref_val] at this
  exact this

/-- `as_sql(Bytes b)` for `b` not valid UTF-8: the hexadecimal literal `0x…` of `b` (upper-case
    digits; only the bytes `0`–`9`, `A`–`F`, `x`). -/
theorem value.Value.as_sql_bytes_hex (b : alloc.vec.Vec U8) (nbe : Bool) (h : ¬ IsUtf8 b.val) :
    value.Value.as_sql (.Bytes b) nbe ⦃ r => utf8 r = hexLit b.val ⦄ := by
  unfold value.Value.as_sql
  simp only
  step with (show value.convert.trusted.str_from_utf8 (alloc.vec.Vec.deref b) ⦃ o => o = none ⦄ by
    have : ¬ (Trusted.bytesOf (alloc.vec.Vec.deref b).val).IsValidUTF8 := by
      rw [CBTUtil.vec_deref_val, ← isUtf8_iff_valid]; exact h
    simp [value.convert.trusted.str_from_utf8, this]) as ⟨o, ho⟩
  subst ho
  simp only [str_0x, Std.bind_ok]
  have := as_sql_loop_spec b b.length "0x" 0#usize (by simp) (by simp)
  refine WP.spec_mono this ?_
  intro r hr
  rw [hr]
  rfl

/-- **Security headline.** For `Bytes b` with `b` valid UTF-8, `as_sql` is one SQL string
    literal, read back by the server (in the same `NO_BACKSLASH_ESCAPES` mode `nbe`) as exactly
    `b`, ending exactly where the output ends, whatever SQL text follows it (unless that text
    starts with `'`, which would continue the literal as `''`). So the value cannot terminate
    the literal early or inject SQL. The reading is byte-wise: valid for connection character
    sets in which 0x27 and 0x5C are always `'` and `\` (e.g. utf8mb4, latin1), not for
    `big5`/`cp932`/`gbk`/`gb18030`/`sjis` (see `Defs/SqlText.lean`), and only when `nbe` is the
    server's actual `NO_BACKSLASH_ESCAPES` mode (`Specs/DefsSqlText.lean`:
    `sqlStrLit_mode_mismatch`). -/
theorem value.Value.as_sql_bytes_literal (b : alloc.vec.Vec U8) (nbe : Bool) (h : IsUtf8 b.val)
    (hlen : (quoteSql nbe b.val).length ≤ Usize.max) :
    value.Value.as_sql (.Bytes b) nbe ⦃ r =>
      ∀ rest : List U8, rest.head?.map (·.val) ≠ some 39 →
        sqlStrLit nbe (utf8 r ++ rest) = some (b.val, rest) ⦄ := by
  refine WP.spec_mono (value.Value.as_sql_bytes_utf8 b nbe h hlen) ?_
  intro r hr rest hrest
  rw [hr]
  exact sqlStrLit_quoteSql nbe b.val rest hrest

end mysql_common
