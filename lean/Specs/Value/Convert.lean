import Proofs.Value.Convert.ParseMysqlDatetimeString
import Proofs.Value.Convert.FromValue
import Proofs.Value.Convert.ParseIr
import Proofs.Value.Convert.ParseIrOpt
import Proofs.Value.Convert.ImplFromValueNum
import Proofs.Value.Convert.Bool
import Proofs.Value.Convert.F32
import Proofs.Value.Convert.F64
import Proofs.Value.Convert.MysqlTimeToDuration
import Proofs.Value.Convert.Duration
import Proofs.Value.Convert.String
import Proofs.Value.Convert.VecU8
import Proofs.Value.Convert.OptionIr2
import Proofs.Value.Convert.ValueIr
import Proofs.Value.Convert.FreeFns
import Proofs.Value.Convert.CowSliceU8
import Proofs.Value.Convert.ArrayU8N
import Proofs.Value.Convert.ParseMysqlTimeString
import Proofs.Value.Convert.FromDuration
import Proofs.Value.Convert.ToValue
import Proofs.Value.Convert.FromOption
import Proofs.Value.Convert.IntoValueImpl
import Proofs.Value.Convert.FromFloatBool
import Proofs.Value.Convert.FromBytes

/-!
# `src/value/convert/mod.rs`
    Conversions between `Value` and Rust types: `FromValue` (`from_value`, `from_value_opt`,
    `get_intermediate`) and its intermediates `ParseIr`/`ParseIrOpt`, the impls for the integer
    types, `bool`, `f32`, `f64`, `std::time::Duration`, `String`, `Vec<u8>`, `Cow<[u8]>`,
    `[u8; N]`, `Option<T>` and `Value` itself, the `From<T> for Value` impls, and the text
    date/time parsers they use.

    **Configuration.** As in `Specs/Io.lean` (x86_64-unknown-linux-gnu, the features of
    `scripts/aeneas-translate.sh`, which include `chrono`). No statement here needs `Target64`:
    `isize`/`usize` are stated with Aeneas' `Isize.min`/`Usize.max`.

    **How `FromValue` is stated.** Each impl is stated through the free functions
    `from_value_opt`/`from_value` applied to the impl's instance (they call the trait methods,
    which every impl here takes from the trait's defaults: `from_value_opt` is `try_from` of the
    intermediate followed by `into`, `from_value` panics iff `from_value_opt` is an `Err`; see the
    `FromValue` statements). A conversion error always carries the original value
    (`okPart r = none → r = .Err v`): nothing is lost on failure.

    `¬ f x ⦃ _ => True ⦄` is not used; panics are stated as `f x = fail e`.

    **Definitions used.** `Defs/Convert.lean` (`asciiInt`, `decimalBytes`, `Val.integer`,
    `intConv`, `intIr`, `irView`, `intVal`, `intRecover`, `Val.bytesAscii`, `utf8`, `IsUtf8`,
    `durNanos`, `timeNanos`, `durationTime`, `Val.durationNanos`, `fracRead`, `timeStringRead`,
    `datetimeStringRead`), `Defs/Value.lean` (`Val`, `Val.ofValue`), `Defs/Bytes.lean` (`okPart`,
    `byte`, `cowList`).

    **Trusted axioms these statements rest on** (`lean/MysqlCommon/FunsExternal.lean`, namespace
    `Trusted`; the other `trusted::*` helpers used here — UTF-8 checks, `String` bytes, integer
    `to_string`, `Duration`, `btoi`/`btou` — are exact Lean definitions, not axioms):
    * `Trusted.isMatch`, `Trusted.isMatch_ascii` (the seven regexes, exact on ASCII input): the
      date/time string parsers and everything that reads a date/time from `Bytes`;
    * `Trusted.parseF32`, `Trusted.parseF64` (opaque float parsing): `f32`/`f64` from `Bytes`;
    * `Trusted.f32ToF64` (opaque widening): `f64` from `Float`.

    **Allocation caveat.** Aeneas models allocation as infallible (bounded only by
    `usize::MAX`); real Rust aborts on OOM. "Does not panic" means "does not panic, assuming
    allocation succeeds".

    **Floats** are bit patterns (`F32`/`F64`): `=` on them is bit equality, not Rust's `==`.

    **Not covered.** The conversions from/to `Arc<[u8]>`, `Rc<[u8]>`, `Box<[u8]>`, `Arc<str>`,
    `Rc<str>`, `Box<str>`, `Cow<'static, str>` (excluded from the translation, see Cargo.toml);
    the derived `Clone`/`PartialEq`/`PartialOrd`/`Debug` impls and `Display for FromValueError`;
    `FromValueError` is a plain wrapper of `Value` (`FromValueError := Value`) with nothing to
    state. The private `parse_micros` is covered through the two string parsers.

    **Behaviour to note.**
    * **`mysql_time_to_duration` overflow** (upstream bug): `microseconds * 1000` is computed in
      `u32`, so a `TIME` with more than 4294967 microseconds makes `from_value::<Duration>` panic
      on overflow (debug builds; release builds wrap and return a wrong duration). The binary
      protocol sends microseconds as 4 bytes, so a server can send such a value.
    * **Non-ASCII digits** (upstream bug, confirmed in review): the regexes run in Unicode mode, so
      `\d` also matches non-ASCII decimal digits, which `btou` then rejects; the following
      `.unwrap()` panics, e.g. on `"00:00:00.\u{0660}"`. Only the fractional forms can panic
      (TIME `*_MS`, DATETIME of length 21–26): the fixed lengths 8/9 (TIME) and 10/19
      (DATETIME) force every digit to be one byte, i.e. ASCII. **Non-ASCII `Bytes` inputs to the
      date/time parsers are unspecified** (panic or not): we deliberately add no axiom about the
      regexes off ASCII (`Trusted.isMatch_ascii` is the only one), so every statement that reads a
      date/time from `Bytes` has an explicit ASCII hypothesis.
    * `ParseIrOpt::rollback` of a `Ready` intermediate is `Value::from` of the number, not the
      original value: `UInt 5` read as an `i8` rolls back to `Int 5`, `Int 7` read as a `bool` to
      `Int 1`, a `Float` read as an `f64` to a `Double` (`intRecover`, `recover` statements).
    * `Option<T>`: `Some(x)` whose `Value::from(x)` is `NULL` (e.g. `Some(Value::NULL)`,
      `Some(None)`) reads back as `None`.
    * `From<Duration> for Value` rounds to microseconds without carrying (micros can be
      1000000) and truncates days to `u32` (`durationTime`). The rounding is patch 50's integer
      `(nanos + 500) / 1000`, equal to upstream's `f64` `round` for every `nanos < 10^9`.

    **Semantic patches these statements are about** (each argued behaviour-preserving in its
    header): 47 (`from_value`'s panic message only), 50 (`From<Duration>` rounding in integers),
    55 (`From<i128>`/`From<u128>`: range checks for `to_i64`/`to_u64`), 56 (integer `try_from`:
    range checks for `TryFrom<i64>`/`TryFrom<u64>`). The others (40–46, 48, 49, 51–54, 57–59)
    only route calls through `trusted` or rewrite syntax Aeneas cannot translate.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-! ### `fn parse_mysql_datetime_string` -/

/-- `parse_mysql_datetime_string` (private, used by the chrono conversions): on ASCII input,
    total; the text `DATE`/`DATETIME` literal `datetimeStringRead`. **ASCII hypothesis:** on
    non-ASCII input the Unicode-mode regexes can match non-ASCII digits and the following
    `btou(..).unwrap()` panics (e.g. `"2020-01-01 00:00:00.\u{0660}"`); the regexes are only
    specified on ASCII input, so that case is excluded rather than stated. -/
recall value.convert.parse_mysql_datetime_string_spec (b : Slice U8) (ha : ∀ c ∈ b.val, c.val < 128) :
    value.convert.parse_mysql_datetime_string b ⦃ r =>
      r.map (fun t => (t.1.val, t.2.1.val, t.2.2.1.val, t.2.2.2.1.val, t.2.2.2.2.1.val,
        t.2.2.2.2.2.1.val, t.2.2.2.2.2.2.val)) = datetimeStringRead b.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.parse_mysql_datetime_string_spec`

/-! ### `trait FromValue` -/

/-- `FromValue::from_value` (the default every impl uses): when `from_value_opt` is `Ok x`,
    returns `x`. -/
recall value.convert.FromValue.from_value.default_ok {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) (x : T)
    (h : inst.from_value_opt v = ok (.Ok x)) :
    value.convert.FromValue.from_value.default inst v = ok x

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.FromValue.from_value.default_ok`

/-- `FromValue::from_value` panics exactly when `from_value_opt` is an `Err`. (The panic
    message differs from upstream, patch 47; the condition is the same.) -/
recall value.convert.FromValue.from_value.default_panic {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value)
    (e : value.convert.FromValueError) (h : inst.from_value_opt v = ok (.Err e)) :
    value.convert.FromValue.from_value.default inst v = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.FromValue.from_value.default_panic`

/-- `FromValue::from_value_opt` (the default): `try_from` of the intermediate, then `into`; an
    error from `try_from` is returned unchanged. -/
recall value.convert.FromValue.from_value_opt.default_ok {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) (ir : I) (x : T)
    (h : inst.coreconvertTryFromSelf_IntermediateValueFromValueErrorInst.try_from v = ok (.Ok ir))
    (hx : inst.coreconvertIntoInst.into ir = ok x) :
    value.convert.FromValue.from_value_opt.default inst v = ok (.Ok x)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.FromValue.from_value_opt.default_ok`

/-- `FromValue::from_value_opt` (the default): an error of `try_from` is returned unchanged. -/
recall value.convert.FromValue.from_value_opt.default_err {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value)
    (e : value.convert.FromValueError)
    (h : inst.coreconvertTryFromSelf_IntermediateValueFromValueErrorInst.try_from v = ok (.Err e)) :
    value.convert.FromValue.from_value_opt.default inst v = ok (.Err e)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.FromValue.from_value_opt.default_err`

/-- `FromValue::get_intermediate` (the default): `try_from` of the intermediate. -/
recall value.convert.FromValue.get_intermediate.default_eq {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) :
    value.convert.FromValue.get_intermediate.default inst v =
      inst.coreconvertTryFromSelf_IntermediateValueFromValueErrorInst.try_from v

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.FromValue.get_intermediate.default_eq`

/-! ### `struct ParseIr` -/

/-- `ParseIr::commit`: the converted value. -/
recall value.convert.ParseIr.commit_eq {T : Type} (x : T) (w : value.Value) : value.convert.ParseIr.commit (x, w) = ok x

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIr.commit_eq`

/-- `ParseIr::rollback`: the value it was converted from (every `try_from` producing a `ParseIr`
    stores the original value there, see the `try_from` statements). -/
recall value.convert.ParseIr.rollback_eq {T : Type} (x : T) (w : value.Value) : value.convert.ParseIr.rollback (x, w) = ok w

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIr.rollback_eq`

/-! ### `enum ParseIrOpt` -/

/-- `ParseIrOpt::commit`: the converted value, `Ready` or `Parsed`. -/
recall value.convert.ParseIrOpt.commit_eq {T : Type} (ir : value.convert.ParseIrOpt T) :
    value.convert.ParseIrOpt.commit ir = ok (match ir with | .Ready t => t | .Parsed t _ => t)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOpt.commit_eq`

/-- `ParseIrOpt::rollback`: for `Parsed`, the stored original value; for `Ready`, `t.into()` —
    which need not be the original value (see `intRecover`). -/
recall value.convert.ParseIrOpt.rollback_eq {T : Type} (into : core.convert.Into T value.Value) (ir : value.convert.ParseIrOpt T) :
    value.convert.ParseIrOpt.rollback into ir =
      match ir with | .Ready t => into.into t | .Parsed _ w => ok w

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOpt.rollback_eq`

/-! ### `macro impl_from_value_num! (i8, u8, i16, u16, i32, u32, i64, u64, isize, usize, i128, u128)` -/

/-- `TryFrom<Value> for ParseIrOpt<i8>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
recall value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.I8 => x.val)) = intIr I8.min I8.max (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<i8>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `i8`, with that integer. -/
recall I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 v ⦃ r =>
      (okPart r).map (fun x : Std.I8 => x.val) = intConv I8.min I8.max (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8.from_value_opt_spec`

/-- `from_value::<i8>`: the integer, when it converts. -/
recall I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8.from_value_spec (v : value.Value) (n : ℤ) (h : intConv I8.min I8.max (Val.ofValue v) = some n) :
    value.convert.from_value I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 v ⦃ x => (fun x : Std.I8 => x.val) x = n ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8.from_value_spec`

/-- `from_value::<i8>` panics when the value does not convert. -/
recall I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8.from_value_panic (v : value.Value) (h : intConv I8.min I8.max (Val.ofValue v) = none) :
    value.convert.from_value I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 v = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8.from_value_panic`

/-- `From<ParseIrOpt<i8>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `UInt 5` comes back as `Int 5`). -/
recall value.Value.Insts.CoreConvertFromParseIrOptI8.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptI8.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover I8.min I8.max true (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptI8.recover`

/-- `TryFrom<Value> for ParseIrOpt<u8>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
recall value.convert.ParseIrOptU8.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptU8.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.U8 => (x.val : ℤ))) = intIr 0 (U8.max : ℤ) (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptU8.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<u8>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `u8`, with that integer. -/
recall U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8 v ⦃ r =>
      (okPart r).map (fun x : Std.U8 => (x.val : ℤ)) = intConv 0 (U8.max : ℤ) (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8.from_value_opt_spec`

/-- `from_value::<u8>`: the integer, when it converts. -/
recall U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8.from_value_spec (v : value.Value) (n : ℤ) (h : intConv 0 (U8.max : ℤ) (Val.ofValue v) = some n) :
    value.convert.from_value U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8 v ⦃ x => (fun x : Std.U8 => (x.val : ℤ)) x = n ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8.from_value_spec`

/-- `from_value::<u8>` panics when the value does not convert. -/
recall U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8.from_value_panic (v : value.Value) (h : intConv 0 (U8.max : ℤ) (Val.ofValue v) = none) :
    value.convert.from_value U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8 v = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8.from_value_panic`

/-- `From<ParseIrOpt<u8>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `Int 5` comes back as `UInt 5`). -/
recall value.Value.Insts.CoreConvertFromParseIrOptU8.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptU8.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptU8.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover 0 (U8.max : ℤ) false (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptU8.recover`

/-- `TryFrom<Value> for ParseIrOpt<i16>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
recall value.convert.ParseIrOptI16.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptI16.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.I16 => x.val)) = intIr I16.min I16.max (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptI16.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<i16>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `i16`, with that integer. -/
recall I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16 v ⦃ r =>
      (okPart r).map (fun x : Std.I16 => x.val) = intConv I16.min I16.max (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16.from_value_opt_spec`

/-- `from_value::<i16>`: the integer, when it converts. -/
recall I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16.from_value_spec (v : value.Value) (n : ℤ) (h : intConv I16.min I16.max (Val.ofValue v) = some n) :
    value.convert.from_value I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16 v ⦃ x => (fun x : Std.I16 => x.val) x = n ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16.from_value_spec`

/-- `from_value::<i16>` panics when the value does not convert. -/
recall I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16.from_value_panic (v : value.Value) (h : intConv I16.min I16.max (Val.ofValue v) = none) :
    value.convert.from_value I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16 v = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16.from_value_panic`

/-- `From<ParseIrOpt<i16>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `UInt 5` comes back as `Int 5`). -/
recall value.Value.Insts.CoreConvertFromParseIrOptI16.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptI16.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptI16.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover I16.min I16.max true (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptI16.recover`

/-- `TryFrom<Value> for ParseIrOpt<u16>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
recall value.convert.ParseIrOptU16.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptU16.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.U16 => (x.val : ℤ))) = intIr 0 (U16.max : ℤ) (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptU16.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<u16>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `u16`, with that integer. -/
recall U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16 v ⦃ r =>
      (okPart r).map (fun x : Std.U16 => (x.val : ℤ)) = intConv 0 (U16.max : ℤ) (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16.from_value_opt_spec`

/-- `from_value::<u16>`: the integer, when it converts. -/
recall U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16.from_value_spec (v : value.Value) (n : ℤ) (h : intConv 0 (U16.max : ℤ) (Val.ofValue v) = some n) :
    value.convert.from_value U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16 v ⦃ x => (fun x : Std.U16 => (x.val : ℤ)) x = n ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16.from_value_spec`

/-- `from_value::<u16>` panics when the value does not convert. -/
recall U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16.from_value_panic (v : value.Value) (h : intConv 0 (U16.max : ℤ) (Val.ofValue v) = none) :
    value.convert.from_value U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16 v = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16.from_value_panic`

/-- `From<ParseIrOpt<u16>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `Int 5` comes back as `UInt 5`). -/
recall value.Value.Insts.CoreConvertFromParseIrOptU16.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptU16.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptU16.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover 0 (U16.max : ℤ) false (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptU16.recover`

/-- `TryFrom<Value> for ParseIrOpt<i32>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
recall value.convert.ParseIrOptI32.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptI32.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.I32 => x.val)) = intIr I32.min I32.max (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptI32.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<i32>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `i32`, with that integer. -/
recall I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32 v ⦃ r =>
      (okPart r).map (fun x : Std.I32 => x.val) = intConv I32.min I32.max (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32.from_value_opt_spec`

/-- `from_value::<i32>`: the integer, when it converts. -/
recall I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32.from_value_spec (v : value.Value) (n : ℤ) (h : intConv I32.min I32.max (Val.ofValue v) = some n) :
    value.convert.from_value I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32 v ⦃ x => (fun x : Std.I32 => x.val) x = n ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32.from_value_spec`

/-- `from_value::<i32>` panics when the value does not convert. -/
recall I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32.from_value_panic (v : value.Value) (h : intConv I32.min I32.max (Val.ofValue v) = none) :
    value.convert.from_value I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32 v = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32.from_value_panic`

/-- `From<ParseIrOpt<i32>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `UInt 5` comes back as `Int 5`). -/
recall value.Value.Insts.CoreConvertFromParseIrOptI32.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptI32.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptI32.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover I32.min I32.max true (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptI32.recover`

/-- `TryFrom<Value> for ParseIrOpt<u32>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
recall value.convert.ParseIrOptU32.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptU32.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.U32 => (x.val : ℤ))) = intIr 0 (U32.max : ℤ) (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptU32.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<u32>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `u32`, with that integer. -/
recall U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32 v ⦃ r =>
      (okPart r).map (fun x : Std.U32 => (x.val : ℤ)) = intConv 0 (U32.max : ℤ) (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32.from_value_opt_spec`

/-- `from_value::<u32>`: the integer, when it converts. -/
recall U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32.from_value_spec (v : value.Value) (n : ℤ) (h : intConv 0 (U32.max : ℤ) (Val.ofValue v) = some n) :
    value.convert.from_value U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32 v ⦃ x => (fun x : Std.U32 => (x.val : ℤ)) x = n ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32.from_value_spec`

/-- `from_value::<u32>` panics when the value does not convert. -/
recall U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32.from_value_panic (v : value.Value) (h : intConv 0 (U32.max : ℤ) (Val.ofValue v) = none) :
    value.convert.from_value U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32 v = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32.from_value_panic`

/-- `From<ParseIrOpt<u32>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `Int 5` comes back as `UInt 5`). -/
recall value.Value.Insts.CoreConvertFromParseIrOptU32.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptU32.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptU32.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover 0 (U32.max : ℤ) false (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptU32.recover`

/-- `TryFrom<Value> for ParseIrOpt<i64>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
recall value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.I64 => x.val)) = intIr I64.min I64.max (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<i64>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `i64`, with that integer. -/
recall I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 v ⦃ r =>
      (okPart r).map (fun x : Std.I64 => x.val) = intConv I64.min I64.max (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64.from_value_opt_spec`

/-- `from_value::<i64>`: the integer, when it converts. -/
recall I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64.from_value_spec (v : value.Value) (n : ℤ) (h : intConv I64.min I64.max (Val.ofValue v) = some n) :
    value.convert.from_value I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 v ⦃ x => (fun x : Std.I64 => x.val) x = n ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64.from_value_spec`

/-- `from_value::<i64>` panics when the value does not convert. -/
recall I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64.from_value_panic (v : value.Value) (h : intConv I64.min I64.max (Val.ofValue v) = none) :
    value.convert.from_value I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 v = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64.from_value_panic`

/-- `From<ParseIrOpt<i64>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `UInt 5` comes back as `Int 5`). -/
recall value.Value.Insts.CoreConvertFromParseIrOptI64.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptI64.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover I64.min I64.max true (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptI64.recover`

/-- `TryFrom<Value> for ParseIrOpt<u64>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
recall value.convert.ParseIrOptU64.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptU64.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.U64 => (x.val : ℤ))) = intIr 0 (U64.max : ℤ) (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptU64.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<u64>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `u64`, with that integer. -/
recall U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64 v ⦃ r =>
      (okPart r).map (fun x : Std.U64 => (x.val : ℤ)) = intConv 0 (U64.max : ℤ) (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64.from_value_opt_spec`

/-- `from_value::<u64>`: the integer, when it converts. -/
recall U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64.from_value_spec (v : value.Value) (n : ℤ) (h : intConv 0 (U64.max : ℤ) (Val.ofValue v) = some n) :
    value.convert.from_value U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64 v ⦃ x => (fun x : Std.U64 => (x.val : ℤ)) x = n ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64.from_value_spec`

/-- `from_value::<u64>` panics when the value does not convert. -/
recall U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64.from_value_panic (v : value.Value) (h : intConv 0 (U64.max : ℤ) (Val.ofValue v) = none) :
    value.convert.from_value U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64 v = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64.from_value_panic`

/-- `From<ParseIrOpt<u64>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `Int 5` comes back as `UInt 5`). -/
recall value.Value.Insts.CoreConvertFromParseIrOptU64.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptU64.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptU64.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover 0 (U64.max : ℤ) false (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptU64.recover`

/-- `TryFrom<Value> for ParseIrOpt<isize>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
recall value.convert.ParseIrOptIsize.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptIsize.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.Isize => x.val)) = intIr Isize.min Isize.max (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptIsize.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<isize>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `isize`, with that integer. -/
recall Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize v ⦃ r =>
      (okPart r).map (fun x : Std.Isize => x.val) = intConv Isize.min Isize.max (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize.from_value_opt_spec`

/-- `from_value::<isize>`: the integer, when it converts. -/
recall Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize.from_value_spec (v : value.Value) (n : ℤ) (h : intConv Isize.min Isize.max (Val.ofValue v) = some n) :
    value.convert.from_value Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize v ⦃ x => (fun x : Std.Isize => x.val) x = n ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize.from_value_spec`

/-- `from_value::<isize>` panics when the value does not convert. -/
recall Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize.from_value_panic (v : value.Value) (h : intConv Isize.min Isize.max (Val.ofValue v) = none) :
    value.convert.from_value Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize v = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize.from_value_panic`

/-- `From<ParseIrOpt<isize>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `UInt 5` comes back as `Int 5`). -/
recall value.Value.Insts.CoreConvertFromParseIrOptIsize.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptIsize.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptIsize.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover Isize.min Isize.max true (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptIsize.recover`

/-- `TryFrom<Value> for ParseIrOpt<usize>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
recall value.convert.ParseIrOptUsize.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptUsize.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.Usize => (x.val : ℤ))) = intIr 0 (Usize.max : ℤ) (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptUsize.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<usize>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `usize`, with that integer. -/
recall Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize v ⦃ r =>
      (okPart r).map (fun x : Std.Usize => (x.val : ℤ)) = intConv 0 (Usize.max : ℤ) (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize.from_value_opt_spec`

/-- `from_value::<usize>`: the integer, when it converts. -/
recall Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize.from_value_spec (v : value.Value) (n : ℤ) (h : intConv 0 (Usize.max : ℤ) (Val.ofValue v) = some n) :
    value.convert.from_value Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize v ⦃ x => (fun x : Std.Usize => (x.val : ℤ)) x = n ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize.from_value_spec`

/-- `from_value::<usize>` panics when the value does not convert. -/
recall Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize.from_value_panic (v : value.Value) (h : intConv 0 (Usize.max : ℤ) (Val.ofValue v) = none) :
    value.convert.from_value Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize v = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize.from_value_panic`

/-- `From<ParseIrOpt<usize>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `Int 5` comes back as `UInt 5`). -/
recall value.Value.Insts.CoreConvertFromParseIrOptUsize.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptUsize.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptUsize.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover 0 (Usize.max : ℤ) false (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptUsize.recover`

/-- `TryFrom<Value> for ParseIrOpt<i128>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
recall value.convert.ParseIrOptI128.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptI128.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.I128 => x.val)) = intIr I128.min I128.max (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptI128.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<i128>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `i128`, with that integer. -/
recall I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128 v ⦃ r =>
      (okPart r).map (fun x : Std.I128 => x.val) = intConv I128.min I128.max (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128.from_value_opt_spec`

/-- `from_value::<i128>`: the integer, when it converts. -/
recall I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128.from_value_spec (v : value.Value) (n : ℤ) (h : intConv I128.min I128.max (Val.ofValue v) = some n) :
    value.convert.from_value I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128 v ⦃ x => (fun x : Std.I128 => x.val) x = n ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128.from_value_spec`

/-- `from_value::<i128>` panics when the value does not convert. -/
recall I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128.from_value_panic (v : value.Value) (h : intConv I128.min I128.max (Val.ofValue v) = none) :
    value.convert.from_value I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128 v = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128.from_value_panic`

/-- `From<ParseIrOpt<i128>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `UInt 5` comes back as `Int 5`). -/
recall value.Value.Insts.CoreConvertFromParseIrOptI128.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptI128.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptI128.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover I128.min I128.max true (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptI128.recover`

/-- `TryFrom<Value> for ParseIrOpt<u128>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
recall value.convert.ParseIrOptU128.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptU128.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.U128 => (x.val : ℤ))) = intIr 0 (U128.max : ℤ) (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptU128.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<u128>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `u128`, with that integer. -/
recall U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128 v ⦃ r =>
      (okPart r).map (fun x : Std.U128 => (x.val : ℤ)) = intConv 0 (U128.max : ℤ) (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128.from_value_opt_spec`

/-- `from_value::<u128>`: the integer, when it converts. -/
recall U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128.from_value_spec (v : value.Value) (n : ℤ) (h : intConv 0 (U128.max : ℤ) (Val.ofValue v) = some n) :
    value.convert.from_value U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128 v ⦃ x => (fun x : Std.U128 => (x.val : ℤ)) x = n ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128.from_value_spec`

/-- `from_value::<u128>` panics when the value does not convert. -/
recall U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128.from_value_panic (v : value.Value) (h : intConv 0 (U128.max : ℤ) (Val.ofValue v) = none) :
    value.convert.from_value U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128 v = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128.from_value_panic`

/-- `From<ParseIrOpt<u128>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `Int 5` comes back as `UInt 5`). -/
recall value.Value.Insts.CoreConvertFromParseIrOptU128.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptU128.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptU128.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover 0 (U128.max : ℤ) false (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptU128.recover`

/-! ### `impl FromValue for bool` -/

/-- `TryFrom<Value> for ParseIrOpt<bool>`: total; `Int`/`UInt` are `Ready (x ≠ 0)`, `Bytes "0"` and
    `Bytes "1"` are `Parsed`; anything else (other bytes, `"true"`, floats, `NULL`) is an
    error. -/
recall value.convert.ParseIrOptBool.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrOptBool.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Int x => .Ok (.Ready (decide (x.val ≠ 0)))
      | .UInt x => .Ok (.Ready (decide (x.val ≠ 0)))
      | .Bytes b =>
        if b.val = [byte 48] then .Ok (.Parsed false v)
        else if b.val = [byte 49] then .Ok (.Parsed true v)
        else .Err v
      | _ => .Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptBool.Insts.CoreConvertTryFromValueFromValueError.try_from_eq`

/-- `from_value_opt::<bool>`: total; a nonzero integer is `true`, the text `"0"`/`"1"` is
    `false`/`true`. -/
recall Bool.Insts.Mysql_commonValueConvertFromValueParseIrOptBool.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt Bool.Insts.Mysql_commonValueConvertFromValueParseIrOptBool v = ok (match Val.ofValue v with
      | .int x => .Ok (decide (x ≠ 0))
      | .uint x => .Ok (decide (x ≠ 0))
      | .bytes [c] => if c.val = 48 then .Ok false else if c.val = 49 then .Ok true else .Err v
      | _ => .Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms Bool.Insts.Mysql_commonValueConvertFromValueParseIrOptBool.from_value_opt_eq`

/-- `From<ParseIrOpt<bool>> for Value` after `try_from`: an integer comes back as `Int 0` or
    `Int 1` (so `UInt 7` comes back as `Int 1`); everything else unchanged. -/
recall value.Value.Insts.CoreConvertFromParseIrOptBool.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptBool.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptBool.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = match Val.ofValue v with
        | .int x => .int (if x = 0 then 0 else 1)
        | .uint x => .int (if x = 0 then 0 else 1)
        | u => u ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptBool.recover`

/-! ### `impl FromValue for f32` -/

/-- `TryFrom<Value> for ParseIrOpt<f32>`: total; `Float x` is `Ready x` (bit for bit), valid
    UTF-8 `Bytes` are parsed by Rust's `str::parse::<f32>` (opaque, `Trusted.parseF32`);
    everything else, including `Double` (no narrowing), is an error. -/
recall value.convert.ParseIrOptF32.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrOptF32.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Float x => .Ok (.Ready x)
      | .Bytes b =>
        if IsUtf8 b.val then
          match Trusted.parseF32 (alloc.vec.Vec.deref b) with
          | some x => .Ok (.Parsed x v)
          | none => .Err v
        else .Err v
      | _ => .Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptF32.Insts.CoreConvertTryFromValueFromValueError.try_from_eq`

/-- `From<ParseIrOpt<f32>> for Value` after `try_from` gives back the original value, bit for
    bit. -/
recall value.Value.Insts.CoreConvertFromParseIrOptF32.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptF32.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptF32.from ir
      | .Err e => ok e) = ok v

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptF32.recover`

/-! ### `impl FromValue for f64` -/

/-- `TryFrom<Value> for ParseIrOpt<f64>`: total; `Double x` is `Ready x`, `Float x` is `Ready` of
    its widening (opaque, `Trusted.f32ToF64`), valid UTF-8 `Bytes` are parsed by
    `str::parse::<f64>` (opaque, `Trusted.parseF64`); everything else is an error. -/
recall value.convert.ParseIrOptF64.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    value.convert.ParseIrOptF64.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with
      | .Double x => .Ok (.Ready x)
      | .Float x => .Ok (.Ready (Trusted.f32ToF64 x))
      | .Bytes b =>
        if IsUtf8 b.val then
          match Trusted.parseF64 (alloc.vec.Vec.deref b) with
          | some x => .Ok (.Parsed x v)
          | none => .Err v
        else .Err v
      | _ => .Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptF64.Insts.CoreConvertTryFromValueFromValueError.try_from_eq`

/-- `From<ParseIrOpt<f64>> for Value` after `try_from`: the original value, except that a `Float`
    comes back as a `Double` (of its widening). -/
recall value.Value.Insts.CoreConvertFromParseIrOptF64.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptF64.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptF64.from ir
      | .Err e => ok e) =
      ok (match v with | .Float x => .Double (Trusted.f32ToF64 x) | u => u)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptF64.recover`

/-! ### `fn mysql_time_to_duration` -/

/-- `mysql_time_to_duration` (private): the duration of `days hours:minutes:seconds.micros`
    (`timeNanos`, fields not range-checked), when `microseconds * 1000` fits in a `u32`. -/
recall value.convert.mysql_time_to_duration_spec (d : U32) (h m s : U8) (us : U32) (hus : us.val * 1000 < 2 ^ 32) :
    value.convert.mysql_time_to_duration d h m s us ⦃ x => durNanos x = timeNanos d.val h.val m.val s.val us.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.mysql_time_to_duration_spec`

/-- **Upstream bug.** `mysql_time_to_duration` overflows (`microseconds * 1000` in `u32`) when
    `microseconds > 4294967`: a panic in debug builds (the model), a wrong duration in release
    builds. -/
recall value.convert.mysql_time_to_duration_overflow (d : U32) (h m s : U8) (us : U32) (hus : 2 ^ 32 ≤ us.val * 1000) :
    value.convert.mysql_time_to_duration d h m s us = fail .integerOverflow

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.mysql_time_to_duration_overflow`

/-! ### `impl FromValue for std::time::Duration` -/

/-- `TryFrom<Value> for ParseIrOpt<Duration>`: a non-negative (sign flag false) `TIME`, or `Bytes` holding a
    non-negative text `TIME` literal, is `Parsed` with that duration (`Val.durationNanos`);
    everything else, including every negative `TIME`, is an error. Hypotheses: the `Bytes` are
    ASCII (see the module docstring: the non-ASCII panic), and a non-negative `TIME` has at most 4294967
    microseconds (negative ones are rejected before any arithmetic) (the `mysql_time_to_duration` overflow, stated separately). -/
recall value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii)
    (hus : ∀ d h m s us, v = .Time false d h m s us → us.val ≤ 4294967) :
    value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (fun ir => durNanos (match ir with | .Ready t => t | .Parsed t _ => t)) =
        (Val.ofValue v).durationNanos ∧
      (∀ ir, r = .Ok ir → ∃ t, ir = .Parsed t v) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- **Crash path.** `TryFrom<Value> for ParseIrOpt<Duration>` (and so `from_value_opt::<Duration>`)
    fails on a non-negative `TIME` with more than 4294967 microseconds (the `mysql_time_to_duration`
    overflow). -/
recall value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_overflow (d : U32) (h m s : U8) (us : U32) (hus : 4294967 < us.val) :
    value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from
      (.Time false d h m s us) = fail .integerOverflow

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from_overflow`

/-- `from_value_opt::<Duration>`: as `try_from`, committed (same hypotheses). -/
recall core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration.from_value_opt_spec (v : value.Value) (ha : (Val.ofValue v).bytesAscii)
    (hus : ∀ d h m s us, v = .Time false d h m s us → us.val ≤ 4294967) :
    value.convert.from_value_opt core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration v ⦃ r =>
      (okPart r).map durNanos = (Val.ofValue v).durationNanos ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration.from_value_opt_spec`

/-- `From<ParseIrOpt<Duration>> for Value` after `try_from` gives back the original value (every
    successful conversion is `Parsed`). Same hypotheses. -/
recall value.Value.Insts.CoreConvertFromParseIrOptDuration.recover (v : value.Value) (ha : (Val.ofValue v).bytesAscii)
    (hus : ∀ d h m s us, v = .Time false d h m s us → us.val ≤ 4294967) :
    (do
      let r ← value.convert.ParseIrOptDuration.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptDuration.from ir
      | .Err e => ok e) = ok v

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromParseIrOptDuration.recover`

/-! ### `impl FromValue for String` -/

/-- `TryFrom<Value> for String`: total; succeeds exactly on `Bytes` that are valid UTF-8, with
    the string they encode; on failure the original value (the bytes) is returned. -/
recall alloc.string.String.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    alloc.string.String.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (∀ s, r = .Ok s ↔ Val.ofValue v = .bytes (utf8 s)) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms alloc.string.String.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<String>`: as `try_from`. -/
recall alloc.string.String.Insts.Mysql_commonValueConvertFromValueString.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt alloc.string.String.Insts.Mysql_commonValueConvertFromValueString v ⦃ r =>
      (∀ s, r = .Ok s ↔ Val.ofValue v = .bytes (utf8 s)) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms alloc.string.String.Insts.Mysql_commonValueConvertFromValueString.from_value_opt_spec`

/-! ### `impl FromValue for Vec<u8>` -/

/-- `TryFrom<Value> for Vec<u8>`: the bytes of `Bytes`; an error on anything else (no
    conversion of numbers to text). -/
recall alloc.vec.VecU8.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    alloc.vec.VecU8.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (match v with | .Bytes b => .Ok b | _ => .Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms alloc.vec.VecU8.Insts.CoreConvertTryFromValueFromValueError.try_from_eq`

/-- `from_value_opt::<Vec<u8>>`: as `try_from`. -/
recall alloc.vec.VecU8.Insts.Mysql_commonValueConvertFromValueVecU8.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt alloc.vec.VecU8.Insts.Mysql_commonValueConvertFromValueVecU8 v = ok (match v with | .Bytes b => .Ok b | _ => .Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms alloc.vec.VecU8.Insts.Mysql_commonValueConvertFromValueVecU8.from_value_opt_eq`

/-! ### `enum OptionIr2 and impl FromValue for Option<T>` -/

/-- `TryFrom<Value> for OptionIr2<T>`: `NULL` is `None`. -/
recall value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from_null {T I : Type} (inst : value.convert.FromValue T I) :
    value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from inst .NULL = ok (.Ok .None)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from_null`

/-- `TryFrom<Value> for OptionIr2<T>`: any other value is converted by `T`'s intermediate; its
    result is wrapped in `Some`, its error returned unchanged. -/
recall value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from_ok {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) (hv : v ≠ .NULL) (ir : I)
    (h : inst.coreconvertTryFromSelf_IntermediateValueFromValueErrorInst.try_from v = ok (.Ok ir)) :
    value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from inst v = ok (.Ok (.Some ir))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from_ok`

/-- `TryFrom<Value> for OptionIr2<T>`: errors of `T`'s intermediate are returned unchanged. -/
recall value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from_err {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) (hv : v ≠ .NULL)
    (e : value.convert.FromValueError)
    (h : inst.coreconvertTryFromSelf_IntermediateValueFromValueErrorInst.try_from v = ok (.Err e)) :
    value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from inst v = ok (.Err e)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.OptionIr2.Insts.CoreConvertTryFromValueFromValueError.try_from_err`

/-- `From<OptionIr2<T>> for Option<T>`: `None`, or `Some` of `T`'s `into`. -/
recall core.option.Option.Insts.CoreConvertFromOptionIr2.from_eq {T I : Type} (inst : value.convert.FromValue T I) (ir : value.convert.OptionIr2 T I) :
    core.option.Option.Insts.CoreConvertFromOptionIr2.from inst ir =
      match ir with
      | .None => ok none
      | .Some i => inst.coreconvertIntoInst.into i >>= fun t => ok (some t)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms core.option.Option.Insts.CoreConvertFromOptionIr2.from_eq`

/-- `From<OptionIr2<T>> for Value`: `NULL`, or the rollback of the inner intermediate. -/
recall value.Value.Insts.CoreConvertFromOptionIr2.from_eq {T I : Type} (inst : value.convert.FromValue T I) (into : core.convert.Into I value.Value)
    (ir : value.convert.OptionIr2 T I) :
    value.Value.Insts.CoreConvertFromOptionIr2.from inst into ir =
      match ir with | .None => ok .NULL | .Some i => into.into i

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromOptionIr2.from_eq`

/-- `from_value_opt::<Option<T>>`: `NULL` is `Ok(None)`. -/
recall core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2.from_value_opt_null {T I : Type} (inst : value.convert.FromValue T I) :
    value.convert.from_value_opt (core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2 inst) .NULL = ok (.Ok none)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2.from_value_opt_null`

/-- `from_value_opt::<Option<T>>`: any other value is `T`'s (default) `from_value_opt`, wrapped in
    `Some` (errors unchanged). -/
recall core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2.from_value_opt_some {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) (hv : v ≠ .NULL)
    (r : core.result.Result T value.convert.FromValueError)
    (h : value.convert.FromValue.from_value_opt.default inst v = ok r) :
    value.convert.from_value_opt (core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2 inst) v =
      ok (match r with | .Ok x => .Ok (some x) | .Err e => .Err e)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2.from_value_opt_some`

/-! ### `struct ValueIr and impl FromValue for Value` -/

/-- `TryFrom<Value> for ValueIr`: never fails. -/
recall value.convert.ValueIr.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) : value.convert.ValueIr.Insts.CoreConvertTryFromValueFromValueError.try_from v = ok (.Ok v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ValueIr.Insts.CoreConvertTryFromValueFromValueError.try_from_eq`

/-- `From<ValueIr> for Value`: the value. -/
recall value.Value.Insts.CoreConvertFromValueIr.from_eq (v : value.convert.ValueIr) : value.Value.Insts.CoreConvertFromValueIr.from v = ok v

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromValueIr.from_eq`

/-- `from_value_opt::<Value>`: the value itself, always. -/
recall value.Value.Insts.Mysql_commonValueConvertFromValueValueIr.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt value.Value.Insts.Mysql_commonValueConvertFromValueValueIr v = ok (.Ok v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.Mysql_commonValueConvertFromValueValueIr.from_value_opt_eq`

/-! ### `fn from_value, fn from_value_opt` -/

/-- `from_value::<T>(v)`: `T::from_value(v)`. -/
recall value.convert.from_value_eq {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) :
    value.convert.from_value inst v = inst.from_value v

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.from_value_eq`

/-- `from_value_opt::<T>(v)`: `T::from_value_opt(v)`. -/
recall value.convert.from_value_opt_eq {T I : Type} (inst : value.convert.FromValue T I) (v : value.Value) :
    value.convert.from_value_opt inst v = inst.from_value_opt v

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.from_value_opt_eq`

/-! ### `impl FromValue for Cow<'static, [u8]>` -/

/-- `TryFrom<Value> for Cow<'static, [u8]>`: `Owned` bytes of `Bytes`; an error on anything else. -/
recall alloc.borrow.CowStaticSliceU8VecU8.Insts.CoreConvertTryFromValueFromValueError.try_from_eq (v : value.Value) :
    alloc.borrow.CowStaticSliceU8VecU8.Insts.CoreConvertTryFromValueFromValueError.try_from v =
      ok (match v with | .Bytes b => .Ok (.Owned b) | _ => .Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms alloc.borrow.CowStaticSliceU8VecU8.Insts.CoreConvertTryFromValueFromValueError.try_from_eq`

/-- `from_value_opt::<Cow<'static, [u8]>>`: as `try_from`. -/
recall alloc.borrow.CowStaticSliceU8VecU8.Insts.Mysql_commonValueConvertFromValueCowStaticSliceU8VecU8.from_value_opt_eq (v : value.Value) :
    value.convert.from_value_opt alloc.borrow.CowStaticSliceU8VecU8.Insts.Mysql_commonValueConvertFromValueCowStaticSliceU8VecU8 v = ok (match v with | .Bytes b => .Ok (.Owned b) | _ => .Err v)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms alloc.borrow.CowStaticSliceU8VecU8.Insts.Mysql_commonValueConvertFromValueCowStaticSliceU8VecU8.from_value_opt_eq`

/-! ### `impl FromValue for [u8; N]` -/

/-- `TryFrom<Value> for [u8; N]`: total; succeeds exactly on `Bytes` of length `N`. -/
recall ArrayU8N.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (N : Usize) (v : value.Value) :
    ArrayU8N.Insts.CoreConvertTryFromValueFromValueError.try_from N v ⦃ r =>
      (∀ a : Array U8 N, r = .Ok a ↔ Val.ofValue v = .bytes a.val) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms ArrayU8N.Insts.CoreConvertTryFromValueFromValueError.try_from_spec`

/-- `from_value_opt::<[u8; N]>`: as `try_from`. -/
recall ArrayU8N.Insts.Mysql_commonValueConvertFromValueArrayU8N.from_value_opt_spec (N : Usize) (v : value.Value) :
    value.convert.from_value_opt (ArrayU8N.Insts.Mysql_commonValueConvertFromValueArrayU8N N) v ⦃ r =>
      (∀ a : Array U8 N, r = .Ok a ↔ Val.ofValue v = .bytes a.val) ∧ (okPart r = none → r = .Err v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms ArrayU8N.Insts.Mysql_commonValueConvertFromValueArrayU8N.from_value_opt_spec`

/-! ### `fn parse_mysql_time_string` -/

/-- `parse_mysql_time_string` (private, used by the `Duration`, chrono and time conversions): on
    ASCII input, total; the text `TIME` literal `timeStringRead`, as `(negative, hours, minutes,
    seconds, microseconds)`. **ASCII hypothesis:** on non-ASCII input the Unicode-mode regexes
    can match non-ASCII digits and `btou(..).unwrap()` panics,
    e.g. on `"00:00:00.\u{0660}"`; the regexes are only specified on ASCII input, so that case is
    excluded rather than stated. -/
recall value.convert.parse_mysql_time_string_spec (b : Slice U8) (ha : ∀ c ∈ b.val, c.val < 128) :
    value.convert.parse_mysql_time_string b ⦃ r =>
      r.map (fun t => (t.1, t.2.1.val, t.2.2.1.val, t.2.2.2.1.val, t.2.2.2.2.val)) =
        timeStringRead b.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.parse_mysql_time_string_spec`

/-! ### `impl From<Duration> for Value` -/

/-- `From<Duration> for Value`: the non-negative `TIME` `durationTime` (microseconds rounded half
    up, not carried; days truncated to `u32`). The rounding `(nanos + 500) / 1000` is patch 50's;
    it equals upstream's `(nanos as f64 / 1000.0).round()` for every `nanos < 10^9`. -/
recall value.Value.Insts.CoreConvertFromDuration.from_spec (d : core.time.Duration) :
    value.Value.Insts.CoreConvertFromDuration.from d ⦃ w =>
      Val.ofValue w = durationTime d.secs.val d.nanos.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromDuration.from_spec`

/-- Round trip: `from_value_opt::<Duration>(Value::from(d))` is `d` rounded to the nearest
    microsecond (half up), modulo `2^32` days. -/
recall value.Value.Insts.CoreConvertFromDuration.roundtrip (d : core.time.Duration) :
    (do let w ← value.Value.Insts.CoreConvertFromDuration.from d; value.convert.from_value_opt core.time.Duration.Insts.Mysql_commonValueConvertFromValueParseIrOptDuration w) ⦃ r =>
      ∃ d', r = .Ok d' ∧
        durNanos d' = (d.secs.val % (86400 * 2 ^ 32)) * 10 ^ 9 + (d.nanos.val + 500) / 1000 * 1000 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromDuration.roundtrip`

/-! ### `trait ToValue and impl From<&T> for Value` -/

/-- `ToValue for T: Into<Value> + Clone`: `self.clone().into()`. -/
recall value.convert.ToValue.Blanket.to_value_eq {T : Type} (into : core.convert.Into T value.Value) (clone : core.clone.Clone T) (x : T) :
    value.convert.ToValue.Blanket.to_value into clone x = (clone.clone x >>= into.into)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.convert.ToValue.Blanket.to_value_eq`

/-- `From<&T> for Value`: `x.to_value()`. -/
recall value.Value.Insts.CoreConvertFromSharedAT.from_eq {T : Type} (inst : value.convert.ToValue T) (x : T) :
    value.Value.Insts.CoreConvertFromSharedAT.from inst x = inst.to_value x

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromSharedAT.from_eq`

/-! ### `impl From<Option<T>> for Value` -/

/-- `From<Option<T>> for Value`: `None` is `NULL`, `Some(x)` is `x.into()`. -/
recall value.Value.Insts.CoreConvertFromOption.from_eq {T : Type} (into : core.convert.Into T value.Value) (x : Option T) :
    value.Value.Insts.CoreConvertFromOption.from into x =
      match x with | none => ok .NULL | some y => into.into y

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromOption.from_eq`

/-- Round trip for `Option<T>`: `None` reads back as `None`. -/
recall value.Value.Insts.CoreConvertFromOption.roundtrip_none {T I : Type} (inst : value.convert.FromValue T I) (into : core.convert.Into T value.Value) :
    (do let w ← value.Value.Insts.CoreConvertFromOption.from into none; value.convert.from_value_opt (core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2 inst) w) =
      ok (.Ok none)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromOption.roundtrip_none`

/-- Round trip for `Option<T>`: `Some(x)` reads back as `Some(x)` when `x` round-trips through
    `T` and `Value::from(x)` is not `NULL`. -/
recall value.Value.Insts.CoreConvertFromOption.roundtrip_some {T I : Type} (inst : value.convert.FromValue T I) (into : core.convert.Into T value.Value)
    (x : T) (w : value.Value) (hw : into.into x = ok w) (hn : w ≠ .NULL)
    (hx : value.convert.FromValue.from_value_opt.default inst w = ok (.Ok x)) :
    (do let w ← value.Value.Insts.CoreConvertFromOption.from into (some x); value.convert.from_value_opt (core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2 inst) w) =
      ok (.Ok (some x))

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromOption.roundtrip_some`

/-- **Quirk.** `Some(x)` whose `Value::from(x)` is `NULL` (e.g. `Some(Value::NULL)`,
    `Some(None::<U>)`) reads back as `None`. -/
recall value.Value.Insts.CoreConvertFromOption.roundtrip_some_null {T I : Type} (inst : value.convert.FromValue T I) (into : core.convert.Into T value.Value)
    (x : T) (hw : into.into x = ok .NULL) :
    (do let w ← value.Value.Insts.CoreConvertFromOption.from into (some x); value.convert.from_value_opt (core.option.Option.Insts.Mysql_commonValueConvertFromValueOptionIr2 inst) w) =
      ok (.Ok none)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromOption.roundtrip_some_null`

/-! ### `macro into_value_impl! (i8, i16, i32, i64, isize, u8, u16, u32, u64, usize), impl From<i128>, From<u128> for Value` -/

/-- `From<i8> for Value`: `Int` of the number. -/
recall value.Value.Insts.CoreConvertFromI8.from_spec (x : Std.I8) :
    value.Value.Insts.CoreConvertFromI8.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromI8.from_spec`

/-- Round trip: `from_value_opt::<i8>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromI8.from_roundtrip (x : Std.I8) :
    (do let w ← value.Value.Insts.CoreConvertFromI8.from x; value.convert.from_value_opt I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 w) ⦃ r => r = .Ok x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromI8.from_roundtrip`

/-- `From<u8> for Value`: `UInt` of the number. -/
recall value.Value.Insts.CoreConvertFromU8.from_spec (x : Std.U8) :
    value.Value.Insts.CoreConvertFromU8.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromU8.from_spec`

/-- Round trip: `from_value_opt::<u8>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromU8.from_roundtrip (x : Std.U8) :
    (do let w ← value.Value.Insts.CoreConvertFromU8.from x; value.convert.from_value_opt U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8 w) ⦃ r => r = .Ok x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromU8.from_roundtrip`

/-- `From<i16> for Value`: `Int` of the number. -/
recall value.Value.Insts.CoreConvertFromI16.from_spec (x : Std.I16) :
    value.Value.Insts.CoreConvertFromI16.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromI16.from_spec`

/-- Round trip: `from_value_opt::<i16>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromI16.from_roundtrip (x : Std.I16) :
    (do let w ← value.Value.Insts.CoreConvertFromI16.from x; value.convert.from_value_opt I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16 w) ⦃ r => r = .Ok x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromI16.from_roundtrip`

/-- `From<u16> for Value`: `UInt` of the number. -/
recall value.Value.Insts.CoreConvertFromU16.from_spec (x : Std.U16) :
    value.Value.Insts.CoreConvertFromU16.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromU16.from_spec`

/-- Round trip: `from_value_opt::<u16>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromU16.from_roundtrip (x : Std.U16) :
    (do let w ← value.Value.Insts.CoreConvertFromU16.from x; value.convert.from_value_opt U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16 w) ⦃ r => r = .Ok x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromU16.from_roundtrip`

/-- `From<i32> for Value`: `Int` of the number. -/
recall value.Value.Insts.CoreConvertFromI32.from_spec (x : Std.I32) :
    value.Value.Insts.CoreConvertFromI32.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromI32.from_spec`

/-- Round trip: `from_value_opt::<i32>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromI32.from_roundtrip (x : Std.I32) :
    (do let w ← value.Value.Insts.CoreConvertFromI32.from x; value.convert.from_value_opt I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32 w) ⦃ r => r = .Ok x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromI32.from_roundtrip`

/-- `From<u32> for Value`: `UInt` of the number. -/
recall value.Value.Insts.CoreConvertFromU32.from_spec (x : Std.U32) :
    value.Value.Insts.CoreConvertFromU32.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromU32.from_spec`

/-- Round trip: `from_value_opt::<u32>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromU32.from_roundtrip (x : Std.U32) :
    (do let w ← value.Value.Insts.CoreConvertFromU32.from x; value.convert.from_value_opt U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32 w) ⦃ r => r = .Ok x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromU32.from_roundtrip`

/-- `From<i64> for Value`: `Int` of the number. -/
recall value.Value.Insts.CoreConvertFromI64.from_spec (x : Std.I64) :
    value.Value.Insts.CoreConvertFromI64.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromI64.from_spec`

/-- Round trip: `from_value_opt::<i64>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromI64.from_roundtrip (x : Std.I64) :
    (do let w ← value.Value.Insts.CoreConvertFromI64.from x; value.convert.from_value_opt I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 w) ⦃ r => r = .Ok x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromI64.from_roundtrip`

/-- `From<u64> for Value`: `UInt` of the number. -/
recall value.Value.Insts.CoreConvertFromU64.from_spec (x : Std.U64) :
    value.Value.Insts.CoreConvertFromU64.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromU64.from_spec`

/-- Round trip: `from_value_opt::<u64>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromU64.from_roundtrip (x : Std.U64) :
    (do let w ← value.Value.Insts.CoreConvertFromU64.from x; value.convert.from_value_opt U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64 w) ⦃ r => r = .Ok x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromU64.from_roundtrip`

/-- `From<isize> for Value`: `Int` of the number. -/
recall value.Value.Insts.CoreConvertFromIsize.from_spec (x : Std.Isize) :
    value.Value.Insts.CoreConvertFromIsize.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromIsize.from_spec`

/-- Round trip: `from_value_opt::<isize>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromIsize.from_roundtrip (x : Std.Isize) :
    (do let w ← value.Value.Insts.CoreConvertFromIsize.from x; value.convert.from_value_opt Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize w) ⦃ r => r = .Ok x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromIsize.from_roundtrip`

/-- `From<usize> for Value`: `UInt` of the number. -/
recall value.Value.Insts.CoreConvertFromUsize.from_spec (x : Std.Usize) :
    value.Value.Insts.CoreConvertFromUsize.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromUsize.from_spec`

/-- Round trip: `from_value_opt::<usize>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromUsize.from_roundtrip (x : Std.Usize) :
    (do let w ← value.Value.Insts.CoreConvertFromUsize.from x; value.convert.from_value_opt Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize w) ⦃ r => r = .Ok x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromUsize.from_roundtrip`

/-- `From<i128> for Value`: `Int` if the number fits in an `i64`, else `UInt` if it fits in a `u64`, else `Bytes` of its decimal representation (`intVal`). -/
recall value.Value.Insts.CoreConvertFromI128.from_spec (x : Std.I128) :
    value.Value.Insts.CoreConvertFromI128.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromI128.from_spec`

/-- Round trip: `from_value_opt::<i128>(Value::from(x)) = Ok(x)` (through the decimal text for values outside the 64-bit ranges). -/
recall value.Value.Insts.CoreConvertFromI128.from_roundtrip (x : Std.I128) :
    (do let w ← value.Value.Insts.CoreConvertFromI128.from x; value.convert.from_value_opt I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128 w) ⦃ r => r = .Ok x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromI128.from_roundtrip`

/-- `From<u128> for Value`: `UInt` if the number fits in a `u64`, else `Bytes` of its decimal representation (`intVal`). -/
recall value.Value.Insts.CoreConvertFromU128.from_spec (x : Std.U128) :
    value.Value.Insts.CoreConvertFromU128.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromU128.from_spec`

/-- Round trip: `from_value_opt::<u128>(Value::from(x)) = Ok(x)` (through the decimal text for values outside the 64-bit ranges). -/
recall value.Value.Insts.CoreConvertFromU128.from_roundtrip (x : Std.U128) :
    (do let w ← value.Value.Insts.CoreConvertFromU128.from x; value.convert.from_value_opt U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128 w) ⦃ r => r = .Ok x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromU128.from_roundtrip`

/-! ### `impl From<f32>, From<f64>, From<bool> for Value` -/

/-- `From<f32> for Value`: `Float`, bit for bit. -/
recall value.Value.Insts.CoreConvertFromF32.from_eq (x : F32) : value.Value.Insts.CoreConvertFromF32.from x = ok (.Float x)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromF32.from_eq`

/-- Round trip: `from_value_opt::<f32>(Value::from(x)) = Ok(x)`, bit for bit (also for NaNs). -/
recall value.Value.Insts.CoreConvertFromF32.roundtrip (x : F32) :
    (do let w ← value.Value.Insts.CoreConvertFromF32.from x; value.convert.from_value_opt F32.Insts.Mysql_commonValueConvertFromValueParseIrOptF32 w) = ok (.Ok x)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromF32.roundtrip`

/-- `From<f64> for Value`: `Double`, bit for bit. -/
recall value.Value.Insts.CoreConvertFromF64.from_eq (x : F64) : value.Value.Insts.CoreConvertFromF64.from x = ok (.Double x)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromF64.from_eq`

/-- Round trip: `from_value_opt::<f64>(Value::from(x)) = Ok(x)`, bit for bit. -/
recall value.Value.Insts.CoreConvertFromF64.roundtrip (x : F64) :
    (do let w ← value.Value.Insts.CoreConvertFromF64.from x; value.convert.from_value_opt F64.Insts.Mysql_commonValueConvertFromValueParseIrOptF64 w) = ok (.Ok x)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromF64.roundtrip`

/-- `From<bool> for Value`: `Int 1` or `Int 0`. -/
recall value.Value.Insts.CoreConvertFromBool.from_spec (x : Bool) :
    value.Value.Insts.CoreConvertFromBool.from x ⦃ w => Val.ofValue w = .int (if x then 1 else 0) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromBool.from_spec`

/-- Round trip: `from_value_opt::<bool>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromBool.roundtrip (x : Bool) :
    (do let w ← value.Value.Insts.CoreConvertFromBool.from x; value.convert.from_value_opt Bool.Insts.Mysql_commonValueConvertFromValueParseIrOptBool w) = ok (.Ok x)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromBool.roundtrip`

/-! ### `impl From<&[u8]>, From<Vec<u8>>, From<&str>, From<Cow<T>>, From<String>, From<[u8; N]> for Value` -/

/-- `From<&[u8]> for Value`: `Bytes` of a copy. -/
recall value.Value.Insts.CoreConvertFromSharedASliceU8.from_spec (x : Slice U8) :
    value.Value.Insts.CoreConvertFromSharedASliceU8.from x ⦃ w => Val.ofValue w = .bytes x.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromSharedASliceU8.from_spec`

/-- `From<Vec<u8>> for Value`: `Bytes`. -/
recall value.Value.Insts.CoreConvertFromVecU8.from_eq (x : alloc.vec.Vec U8) : value.Value.Insts.CoreConvertFromVecU8.from x = ok (.Bytes x)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromVecU8.from_eq`

/-- Round trip: `from_value_opt::<Vec<u8>>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromVecU8.roundtrip (x : alloc.vec.Vec U8) :
    (do let w ← value.Value.Insts.CoreConvertFromVecU8.from x; value.convert.from_value_opt alloc.vec.VecU8.Insts.Mysql_commonValueConvertFromValueVecU8 w) = ok (.Ok x)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromVecU8.roundtrip`

/-- `From<&str> for Value`: `Bytes` of the string's (UTF-8) bytes. -/
recall value.Value.Insts.CoreConvertFromSharedAStr.from_spec (x : Str) :
    value.Value.Insts.CoreConvertFromSharedAStr.from x ⦃ w => Val.ofValue w = .bytes x.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromSharedAStr.from_spec`

/-- Round trip: a `&str` reads back as a `String` with the same bytes. (A Rust `&str` is always
    valid UTF-8; Aeneas' `Str` is any byte slice, hence the hypothesis.) -/
recall value.Value.Insts.CoreConvertFromSharedAStr.roundtrip (x : Str) (hx : IsUtf8 x.val) :
    (do let w ← value.Value.Insts.CoreConvertFromSharedAStr.from x; value.convert.from_value_opt alloc.string.String.Insts.Mysql_commonValueConvertFromValueString w) ⦃ r =>
      ∃ s, r = .Ok s ∧ utf8 s = x.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromSharedAStr.roundtrip`

/-- `From<Cow<'a, T>> for Value`: `Borrowed(x)` is `(&x).into()`, `Owned(x)` is `x.into()`. -/
recall value.Value.Insts.CoreConvertFromCow.from_eq {T O : Type} (toOwned : alloc.borrow.ToOwned T O) (intoO : core.convert.Into O value.Value)
    (intoB : core.convert.Into T value.Value) (x : alloc.borrow.Cow T O) :
    value.Value.Insts.CoreConvertFromCow.from toOwned intoO intoB x =
      match x with | .Borrowed b => intoB.into b | .Owned o => intoO.into o

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromCow.from_eq`

/-- `From<Cow<[u8]>> for Value`: `Bytes` of the contents, borrowed or owned. -/
recall value.Value.Insts.CoreConvertFromCow.from_slice_u8_spec (x : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    value.Value.Insts.CoreConvertFromCow.from (Slice.Insts.AllocBorrowToOwnedVec core.clone.CloneU8)
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromVecU8)
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromSharedASliceU8) x ⦃ w =>
        Val.ofValue w = .bytes (cowList x) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromCow.from_slice_u8_spec`

/-- Round trip: a `Cow<[u8]>` reads back (owned) with the same contents. -/
recall value.Value.Insts.CoreConvertFromCow.roundtrip_slice_u8 (x : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) :
    (do
      let w ← value.Value.Insts.CoreConvertFromCow.from (Slice.Insts.AllocBorrowToOwnedVec core.clone.CloneU8)
        (core.convert.IntoFrom value.Value.Insts.CoreConvertFromVecU8)
        (core.convert.IntoFrom value.Value.Insts.CoreConvertFromSharedASliceU8) x
      value.convert.from_value_opt alloc.borrow.CowStaticSliceU8VecU8.Insts.Mysql_commonValueConvertFromValueCowStaticSliceU8VecU8 w) ⦃ r => ∃ c, r = .Ok c ∧ cowList c = cowList x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromCow.roundtrip_slice_u8`

/-- `From<String> for Value`: `Bytes` of its UTF-8 encoding. (The hypothesis holds for every
    Rust `String`; Lean strings are unbounded.) -/
recall value.Value.Insts.CoreConvertFromString.from_spec (s : String) (h : (utf8 s).length ≤ Usize.max) :
    value.Value.Insts.CoreConvertFromString.from s ⦃ w => Val.ofValue w = .bytes (utf8 s) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromString.from_spec`

/-- Round trip: `from_value_opt::<String>(Value::from(s)) = Ok(s)`. -/
recall value.Value.Insts.CoreConvertFromString.roundtrip (s : String) (h : (utf8 s).length ≤ Usize.max) :
    (do let w ← value.Value.Insts.CoreConvertFromString.from s; value.convert.from_value_opt alloc.string.String.Insts.Mysql_commonValueConvertFromValueString w) ⦃ r => r = .Ok s ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromString.roundtrip`

/-- `From<[u8; N]> for Value`: `Bytes` of the array. -/
recall value.Value.Insts.CoreConvertFromArrayU8N.from_spec {N : Usize} (x : Array U8 N) :
    value.Value.Insts.CoreConvertFromArrayU8N.from x ⦃ w => Val.ofValue w = .bytes x.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromArrayU8N.from_spec`

/-- Round trip: `from_value_opt::<[u8; N]>(Value::from(x)) = Ok(x)`. -/
recall value.Value.Insts.CoreConvertFromArrayU8N.roundtrip {N : Usize} (x : Array U8 N) :
    (do let w ← value.Value.Insts.CoreConvertFromArrayU8N.from x; value.convert.from_value_opt (ArrayU8N.Insts.Mysql_commonValueConvertFromValueArrayU8N N) w) ⦃ r => r = .Ok x ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms value.Value.Insts.CoreConvertFromArrayU8N.roundtrip`

end mysql_common
