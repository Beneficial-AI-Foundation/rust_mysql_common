import Defs
import Proofs.Util.ConvInts

/-! Statements for `macro impl_from_value_num! (i8, u8, i16, u16, i32, u32, i64, u64, isize, usize, i128, u128)` (spec file: `Specs/Value/Convert.lean`). Helper lemmas: `Proofs/Util/ConvInts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `TryFrom<Value> for ParseIrOpt<i8>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
theorem value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.I8 => x.val)) = intIr I8.min I8.max (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    have hb := ConvInts.bytes_post (fun x : Std.I8 => x.val) (Trusted.btoiSigned .I8 (alloc.vec.Vec.deref b)) b I8.min I8.max (by
      rw [ConvInts.btoiSigned_map]
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val])
    simp only [value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from, value.convert.trusted.btoi_i8, bind_ok]
    split <;> rw [WP.spec_ok]
    · exact hb.1 ‹_›
    · exact hb.2 _ ‹_›
  | Int x =>
    simp only [value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | UInt x =>
    simp only [value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | _ => simp [value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from, okPart, intIr, intConv, Val.integer, Val.ofValue]

/-- `from_value_opt::<i8>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `i8`, with that integer. -/
theorem I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 v ⦃ r =>
      (okPart r).map (fun x : Std.I8 => x.val) = intConv I8.min I8.max (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  exact ConvInts.from_value_opt_of_try I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 (fun _ => rfl) _ _ _ v
    (value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)

/-- `from_value::<i8>`: the integer, when it converts. -/
theorem I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8.from_value_spec (v : value.Value) (n : ℤ) (h : intConv I8.min I8.max (Val.ofValue v) = some n) :
    value.convert.from_value I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 v ⦃ x => (fun x : Std.I8 => x.val) x = n ⦄ := by
  exact ConvInts.from_value_of_opt I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 _ _ _ v n
    (I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8.from_value_opt_spec v) h

/-- `from_value::<i8>` panics when the value does not convert. -/
theorem I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8.from_value_panic (v : value.Value) (h : intConv I8.min I8.max (Val.ofValue v) = none) :
    value.convert.from_value I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 v = fail .panic := by
  exact ConvInts.from_value_panic_of_opt I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 _ _ _ v
    (I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8.from_value_opt_spec v) h

/-- `From<ParseIrOpt<i8>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `UInt 5` comes back as `Int 5`). -/
theorem value.Value.Insts.CoreConvertFromParseIrOptI8.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptI8.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover I8.min I8.max true (Val.ofValue v) ⦄ := by
  obtain ⟨r, hr, hpost⟩ := ConvInts.spec_eq_ok
    (value.convert.ParseIrOptI8.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)
  rw [hr, bind_ok]
  rcases r with ir | e
  · exact ConvInts.recover_ok value.Value.Insts.CoreConvertFromParseIrOptI8.from
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromI8) (fun _ => rfl) _ _ _ _ v ir hpost
      ConvInts.fromI8_spec
  · rw [WP.spec_ok]; exact ConvInts.recover_err _ _ _ _ v e hpost

/-- `TryFrom<Value> for ParseIrOpt<u8>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
theorem value.convert.ParseIrOptU8.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptU8.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.U8 => (x.val : ℤ))) = intIr 0 (U8.max : ℤ) (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    have hb := ConvInts.bytes_post (fun x : Std.U8 => (x.val : ℤ)) (Trusted.btoiUnsigned .U8 (alloc.vec.Vec.deref b)) b 0 (U8.max : ℤ) (by
      rw [ConvInts.btoiUnsigned_map]
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val])
    simp only [value.convert.ParseIrOptU8.Insts.CoreConvertTryFromValueFromValueError.try_from, value.convert.trusted.btoi_u8, bind_ok]
    split <;> rw [WP.spec_ok]
    · exact hb.1 ‹_›
    · exact hb.2 _ ‹_›
  | Int x =>
    simp only [value.convert.ParseIrOptU8.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | UInt x =>
    simp only [value.convert.ParseIrOptU8.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | _ => simp [value.convert.ParseIrOptU8.Insts.CoreConvertTryFromValueFromValueError.try_from, okPart, intIr, intConv, Val.integer, Val.ofValue]

/-- `from_value_opt::<u8>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `u8`, with that integer. -/
theorem U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8 v ⦃ r =>
      (okPart r).map (fun x : Std.U8 => (x.val : ℤ)) = intConv 0 (U8.max : ℤ) (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  exact ConvInts.from_value_opt_of_try U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8 (fun _ => rfl) _ _ _ v
    (value.convert.ParseIrOptU8.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)

/-- `from_value::<u8>`: the integer, when it converts. -/
theorem U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8.from_value_spec (v : value.Value) (n : ℤ) (h : intConv 0 (U8.max : ℤ) (Val.ofValue v) = some n) :
    value.convert.from_value U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8 v ⦃ x => (fun x : Std.U8 => (x.val : ℤ)) x = n ⦄ := by
  exact ConvInts.from_value_of_opt U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8 _ _ _ v n
    (U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8.from_value_opt_spec v) h

/-- `from_value::<u8>` panics when the value does not convert. -/
theorem U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8.from_value_panic (v : value.Value) (h : intConv 0 (U8.max : ℤ) (Val.ofValue v) = none) :
    value.convert.from_value U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8 v = fail .panic := by
  exact ConvInts.from_value_panic_of_opt U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8 _ _ _ v
    (U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8.from_value_opt_spec v) h

/-- `From<ParseIrOpt<u8>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `Int 5` comes back as `UInt 5`). -/
theorem value.Value.Insts.CoreConvertFromParseIrOptU8.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptU8.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptU8.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover 0 (U8.max : ℤ) false (Val.ofValue v) ⦄ := by
  obtain ⟨r, hr, hpost⟩ := ConvInts.spec_eq_ok
    (value.convert.ParseIrOptU8.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)
  rw [hr, bind_ok]
  rcases r with ir | e
  · exact ConvInts.recover_ok value.Value.Insts.CoreConvertFromParseIrOptU8.from
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromU8) (fun _ => rfl) _ _ _ _ v ir hpost
      ConvInts.fromU8_spec
  · rw [WP.spec_ok]; exact ConvInts.recover_err _ _ _ _ v e hpost

/-- `TryFrom<Value> for ParseIrOpt<i16>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
theorem value.convert.ParseIrOptI16.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptI16.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.I16 => x.val)) = intIr I16.min I16.max (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    have hb := ConvInts.bytes_post (fun x : Std.I16 => x.val) (Trusted.btoiSigned .I16 (alloc.vec.Vec.deref b)) b I16.min I16.max (by
      rw [ConvInts.btoiSigned_map]
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val])
    simp only [value.convert.ParseIrOptI16.Insts.CoreConvertTryFromValueFromValueError.try_from, value.convert.trusted.btoi_i16, bind_ok]
    split <;> rw [WP.spec_ok]
    · exact hb.1 ‹_›
    · exact hb.2 _ ‹_›
  | Int x =>
    simp only [value.convert.ParseIrOptI16.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | UInt x =>
    simp only [value.convert.ParseIrOptI16.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | _ => simp [value.convert.ParseIrOptI16.Insts.CoreConvertTryFromValueFromValueError.try_from, okPart, intIr, intConv, Val.integer, Val.ofValue]

/-- `from_value_opt::<i16>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `i16`, with that integer. -/
theorem I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16 v ⦃ r =>
      (okPart r).map (fun x : Std.I16 => x.val) = intConv I16.min I16.max (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  exact ConvInts.from_value_opt_of_try I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16 (fun _ => rfl) _ _ _ v
    (value.convert.ParseIrOptI16.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)

/-- `from_value::<i16>`: the integer, when it converts. -/
theorem I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16.from_value_spec (v : value.Value) (n : ℤ) (h : intConv I16.min I16.max (Val.ofValue v) = some n) :
    value.convert.from_value I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16 v ⦃ x => (fun x : Std.I16 => x.val) x = n ⦄ := by
  exact ConvInts.from_value_of_opt I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16 _ _ _ v n
    (I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16.from_value_opt_spec v) h

/-- `from_value::<i16>` panics when the value does not convert. -/
theorem I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16.from_value_panic (v : value.Value) (h : intConv I16.min I16.max (Val.ofValue v) = none) :
    value.convert.from_value I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16 v = fail .panic := by
  exact ConvInts.from_value_panic_of_opt I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16 _ _ _ v
    (I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16.from_value_opt_spec v) h

/-- `From<ParseIrOpt<i16>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `UInt 5` comes back as `Int 5`). -/
theorem value.Value.Insts.CoreConvertFromParseIrOptI16.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptI16.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptI16.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover I16.min I16.max true (Val.ofValue v) ⦄ := by
  obtain ⟨r, hr, hpost⟩ := ConvInts.spec_eq_ok
    (value.convert.ParseIrOptI16.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)
  rw [hr, bind_ok]
  rcases r with ir | e
  · exact ConvInts.recover_ok value.Value.Insts.CoreConvertFromParseIrOptI16.from
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromI16) (fun _ => rfl) _ _ _ _ v ir hpost
      ConvInts.fromI16_spec
  · rw [WP.spec_ok]; exact ConvInts.recover_err _ _ _ _ v e hpost

/-- `TryFrom<Value> for ParseIrOpt<u16>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
theorem value.convert.ParseIrOptU16.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptU16.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.U16 => (x.val : ℤ))) = intIr 0 (U16.max : ℤ) (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    have hb := ConvInts.bytes_post (fun x : Std.U16 => (x.val : ℤ)) (Trusted.btoiUnsigned .U16 (alloc.vec.Vec.deref b)) b 0 (U16.max : ℤ) (by
      rw [ConvInts.btoiUnsigned_map]
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val])
    simp only [value.convert.ParseIrOptU16.Insts.CoreConvertTryFromValueFromValueError.try_from, value.convert.trusted.btoi_u16, bind_ok]
    split <;> rw [WP.spec_ok]
    · exact hb.1 ‹_›
    · exact hb.2 _ ‹_›
  | Int x =>
    simp only [value.convert.ParseIrOptU16.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | UInt x =>
    simp only [value.convert.ParseIrOptU16.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | _ => simp [value.convert.ParseIrOptU16.Insts.CoreConvertTryFromValueFromValueError.try_from, okPart, intIr, intConv, Val.integer, Val.ofValue]

/-- `from_value_opt::<u16>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `u16`, with that integer. -/
theorem U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16 v ⦃ r =>
      (okPart r).map (fun x : Std.U16 => (x.val : ℤ)) = intConv 0 (U16.max : ℤ) (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  exact ConvInts.from_value_opt_of_try U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16 (fun _ => rfl) _ _ _ v
    (value.convert.ParseIrOptU16.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)

/-- `from_value::<u16>`: the integer, when it converts. -/
theorem U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16.from_value_spec (v : value.Value) (n : ℤ) (h : intConv 0 (U16.max : ℤ) (Val.ofValue v) = some n) :
    value.convert.from_value U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16 v ⦃ x => (fun x : Std.U16 => (x.val : ℤ)) x = n ⦄ := by
  exact ConvInts.from_value_of_opt U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16 _ _ _ v n
    (U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16.from_value_opt_spec v) h

/-- `from_value::<u16>` panics when the value does not convert. -/
theorem U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16.from_value_panic (v : value.Value) (h : intConv 0 (U16.max : ℤ) (Val.ofValue v) = none) :
    value.convert.from_value U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16 v = fail .panic := by
  exact ConvInts.from_value_panic_of_opt U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16 _ _ _ v
    (U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16.from_value_opt_spec v) h

/-- `From<ParseIrOpt<u16>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `Int 5` comes back as `UInt 5`). -/
theorem value.Value.Insts.CoreConvertFromParseIrOptU16.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptU16.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptU16.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover 0 (U16.max : ℤ) false (Val.ofValue v) ⦄ := by
  obtain ⟨r, hr, hpost⟩ := ConvInts.spec_eq_ok
    (value.convert.ParseIrOptU16.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)
  rw [hr, bind_ok]
  rcases r with ir | e
  · exact ConvInts.recover_ok value.Value.Insts.CoreConvertFromParseIrOptU16.from
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromU16) (fun _ => rfl) _ _ _ _ v ir hpost
      ConvInts.fromU16_spec
  · rw [WP.spec_ok]; exact ConvInts.recover_err _ _ _ _ v e hpost

/-- `TryFrom<Value> for ParseIrOpt<i32>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
theorem value.convert.ParseIrOptI32.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptI32.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.I32 => x.val)) = intIr I32.min I32.max (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    have hb := ConvInts.bytes_post (fun x : Std.I32 => x.val) (Trusted.btoiSigned .I32 (alloc.vec.Vec.deref b)) b I32.min I32.max (by
      rw [ConvInts.btoiSigned_map]
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val])
    simp only [value.convert.ParseIrOptI32.Insts.CoreConvertTryFromValueFromValueError.try_from, value.convert.trusted.btoi_i32, bind_ok]
    split <;> rw [WP.spec_ok]
    · exact hb.1 ‹_›
    · exact hb.2 _ ‹_›
  | Int x =>
    simp only [value.convert.ParseIrOptI32.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | UInt x =>
    simp only [value.convert.ParseIrOptI32.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | _ => simp [value.convert.ParseIrOptI32.Insts.CoreConvertTryFromValueFromValueError.try_from, okPart, intIr, intConv, Val.integer, Val.ofValue]

/-- `from_value_opt::<i32>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `i32`, with that integer. -/
theorem I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32 v ⦃ r =>
      (okPart r).map (fun x : Std.I32 => x.val) = intConv I32.min I32.max (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  exact ConvInts.from_value_opt_of_try I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32 (fun _ => rfl) _ _ _ v
    (value.convert.ParseIrOptI32.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)

/-- `from_value::<i32>`: the integer, when it converts. -/
theorem I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32.from_value_spec (v : value.Value) (n : ℤ) (h : intConv I32.min I32.max (Val.ofValue v) = some n) :
    value.convert.from_value I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32 v ⦃ x => (fun x : Std.I32 => x.val) x = n ⦄ := by
  exact ConvInts.from_value_of_opt I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32 _ _ _ v n
    (I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32.from_value_opt_spec v) h

/-- `from_value::<i32>` panics when the value does not convert. -/
theorem I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32.from_value_panic (v : value.Value) (h : intConv I32.min I32.max (Val.ofValue v) = none) :
    value.convert.from_value I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32 v = fail .panic := by
  exact ConvInts.from_value_panic_of_opt I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32 _ _ _ v
    (I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32.from_value_opt_spec v) h

/-- `From<ParseIrOpt<i32>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `UInt 5` comes back as `Int 5`). -/
theorem value.Value.Insts.CoreConvertFromParseIrOptI32.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptI32.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptI32.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover I32.min I32.max true (Val.ofValue v) ⦄ := by
  obtain ⟨r, hr, hpost⟩ := ConvInts.spec_eq_ok
    (value.convert.ParseIrOptI32.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)
  rw [hr, bind_ok]
  rcases r with ir | e
  · exact ConvInts.recover_ok value.Value.Insts.CoreConvertFromParseIrOptI32.from
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromI32) (fun _ => rfl) _ _ _ _ v ir hpost
      ConvInts.fromI32_spec
  · rw [WP.spec_ok]; exact ConvInts.recover_err _ _ _ _ v e hpost

/-- `TryFrom<Value> for ParseIrOpt<u32>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
theorem value.convert.ParseIrOptU32.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptU32.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.U32 => (x.val : ℤ))) = intIr 0 (U32.max : ℤ) (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    have hb := ConvInts.bytes_post (fun x : Std.U32 => (x.val : ℤ)) (Trusted.btoiUnsigned .U32 (alloc.vec.Vec.deref b)) b 0 (U32.max : ℤ) (by
      rw [ConvInts.btoiUnsigned_map]
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val])
    simp only [value.convert.ParseIrOptU32.Insts.CoreConvertTryFromValueFromValueError.try_from, value.convert.trusted.btoi_u32, bind_ok]
    split <;> rw [WP.spec_ok]
    · exact hb.1 ‹_›
    · exact hb.2 _ ‹_›
  | Int x =>
    simp only [value.convert.ParseIrOptU32.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | UInt x =>
    simp only [value.convert.ParseIrOptU32.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | _ => simp [value.convert.ParseIrOptU32.Insts.CoreConvertTryFromValueFromValueError.try_from, okPart, intIr, intConv, Val.integer, Val.ofValue]

/-- `from_value_opt::<u32>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `u32`, with that integer. -/
theorem U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32 v ⦃ r =>
      (okPart r).map (fun x : Std.U32 => (x.val : ℤ)) = intConv 0 (U32.max : ℤ) (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  exact ConvInts.from_value_opt_of_try U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32 (fun _ => rfl) _ _ _ v
    (value.convert.ParseIrOptU32.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)

/-- `from_value::<u32>`: the integer, when it converts. -/
theorem U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32.from_value_spec (v : value.Value) (n : ℤ) (h : intConv 0 (U32.max : ℤ) (Val.ofValue v) = some n) :
    value.convert.from_value U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32 v ⦃ x => (fun x : Std.U32 => (x.val : ℤ)) x = n ⦄ := by
  exact ConvInts.from_value_of_opt U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32 _ _ _ v n
    (U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32.from_value_opt_spec v) h

/-- `from_value::<u32>` panics when the value does not convert. -/
theorem U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32.from_value_panic (v : value.Value) (h : intConv 0 (U32.max : ℤ) (Val.ofValue v) = none) :
    value.convert.from_value U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32 v = fail .panic := by
  exact ConvInts.from_value_panic_of_opt U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32 _ _ _ v
    (U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32.from_value_opt_spec v) h

/-- `From<ParseIrOpt<u32>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `Int 5` comes back as `UInt 5`). -/
theorem value.Value.Insts.CoreConvertFromParseIrOptU32.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptU32.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptU32.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover 0 (U32.max : ℤ) false (Val.ofValue v) ⦄ := by
  obtain ⟨r, hr, hpost⟩ := ConvInts.spec_eq_ok
    (value.convert.ParseIrOptU32.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)
  rw [hr, bind_ok]
  rcases r with ir | e
  · exact ConvInts.recover_ok value.Value.Insts.CoreConvertFromParseIrOptU32.from
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromU32) (fun _ => rfl) _ _ _ _ v ir hpost
      ConvInts.fromU32_spec
  · rw [WP.spec_ok]; exact ConvInts.recover_err _ _ _ _ v e hpost

/-- `TryFrom<Value> for ParseIrOpt<i64>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
theorem value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.I64 => x.val)) = intIr I64.min I64.max (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    have hb := ConvInts.bytes_post (fun x : Std.I64 => x.val) (Trusted.btoiSigned .I64 (alloc.vec.Vec.deref b)) b I64.min I64.max (by
      rw [ConvInts.btoiSigned_map]
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val])
    simp only [value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from, value.convert.trusted.btoi_i64, bind_ok]
    split <;> rw [WP.spec_ok]
    · exact hb.1 ‹_›
    · exact hb.2 _ ‹_›
  | Int x =>
    simp only [value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | UInt x =>
    simp only [value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | _ => simp [value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from, okPart, intIr, intConv, Val.integer, Val.ofValue]

/-- `from_value_opt::<i64>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `i64`, with that integer. -/
theorem I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 v ⦃ r =>
      (okPart r).map (fun x : Std.I64 => x.val) = intConv I64.min I64.max (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  exact ConvInts.from_value_opt_of_try I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 (fun _ => rfl) _ _ _ v
    (value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)

/-- `from_value::<i64>`: the integer, when it converts. -/
theorem I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64.from_value_spec (v : value.Value) (n : ℤ) (h : intConv I64.min I64.max (Val.ofValue v) = some n) :
    value.convert.from_value I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 v ⦃ x => (fun x : Std.I64 => x.val) x = n ⦄ := by
  exact ConvInts.from_value_of_opt I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 _ _ _ v n
    (I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64.from_value_opt_spec v) h

/-- `from_value::<i64>` panics when the value does not convert. -/
theorem I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64.from_value_panic (v : value.Value) (h : intConv I64.min I64.max (Val.ofValue v) = none) :
    value.convert.from_value I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 v = fail .panic := by
  exact ConvInts.from_value_panic_of_opt I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 _ _ _ v
    (I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64.from_value_opt_spec v) h

/-- `From<ParseIrOpt<i64>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `UInt 5` comes back as `Int 5`). -/
theorem value.Value.Insts.CoreConvertFromParseIrOptI64.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptI64.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover I64.min I64.max true (Val.ofValue v) ⦄ := by
  obtain ⟨r, hr, hpost⟩ := ConvInts.spec_eq_ok
    (value.convert.ParseIrOptI64.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)
  rw [hr, bind_ok]
  rcases r with ir | e
  · exact ConvInts.recover_ok value.Value.Insts.CoreConvertFromParseIrOptI64.from
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromI64) (fun _ => rfl) _ _ _ _ v ir hpost
      ConvInts.fromI64_spec
  · rw [WP.spec_ok]; exact ConvInts.recover_err _ _ _ _ v e hpost

/-- `TryFrom<Value> for ParseIrOpt<u64>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
theorem value.convert.ParseIrOptU64.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptU64.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.U64 => (x.val : ℤ))) = intIr 0 (U64.max : ℤ) (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    have hb := ConvInts.bytes_post (fun x : Std.U64 => (x.val : ℤ)) (Trusted.btoiUnsigned .U64 (alloc.vec.Vec.deref b)) b 0 (U64.max : ℤ) (by
      rw [ConvInts.btoiUnsigned_map]
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val])
    simp only [value.convert.ParseIrOptU64.Insts.CoreConvertTryFromValueFromValueError.try_from, value.convert.trusted.btoi_u64, bind_ok]
    split <;> rw [WP.spec_ok]
    · exact hb.1 ‹_›
    · exact hb.2 _ ‹_›
  | Int x =>
    simp only [value.convert.ParseIrOptU64.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | UInt x =>
    simp only [value.convert.ParseIrOptU64.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | _ => simp [value.convert.ParseIrOptU64.Insts.CoreConvertTryFromValueFromValueError.try_from, okPart, intIr, intConv, Val.integer, Val.ofValue]

/-- `from_value_opt::<u64>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `u64`, with that integer. -/
theorem U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64 v ⦃ r =>
      (okPart r).map (fun x : Std.U64 => (x.val : ℤ)) = intConv 0 (U64.max : ℤ) (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  exact ConvInts.from_value_opt_of_try U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64 (fun _ => rfl) _ _ _ v
    (value.convert.ParseIrOptU64.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)

/-- `from_value::<u64>`: the integer, when it converts. -/
theorem U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64.from_value_spec (v : value.Value) (n : ℤ) (h : intConv 0 (U64.max : ℤ) (Val.ofValue v) = some n) :
    value.convert.from_value U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64 v ⦃ x => (fun x : Std.U64 => (x.val : ℤ)) x = n ⦄ := by
  exact ConvInts.from_value_of_opt U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64 _ _ _ v n
    (U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64.from_value_opt_spec v) h

/-- `from_value::<u64>` panics when the value does not convert. -/
theorem U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64.from_value_panic (v : value.Value) (h : intConv 0 (U64.max : ℤ) (Val.ofValue v) = none) :
    value.convert.from_value U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64 v = fail .panic := by
  exact ConvInts.from_value_panic_of_opt U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64 _ _ _ v
    (U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64.from_value_opt_spec v) h

/-- `From<ParseIrOpt<u64>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `Int 5` comes back as `UInt 5`). -/
theorem value.Value.Insts.CoreConvertFromParseIrOptU64.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptU64.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptU64.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover 0 (U64.max : ℤ) false (Val.ofValue v) ⦄ := by
  obtain ⟨r, hr, hpost⟩ := ConvInts.spec_eq_ok
    (value.convert.ParseIrOptU64.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)
  rw [hr, bind_ok]
  rcases r with ir | e
  · exact ConvInts.recover_ok value.Value.Insts.CoreConvertFromParseIrOptU64.from
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromU64) (fun _ => rfl) _ _ _ _ v ir hpost
      ConvInts.fromU64_spec
  · rw [WP.spec_ok]; exact ConvInts.recover_err _ _ _ _ v e hpost

/-- `TryFrom<Value> for ParseIrOpt<isize>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
theorem value.convert.ParseIrOptIsize.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptIsize.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.Isize => x.val)) = intIr Isize.min Isize.max (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    have hb := ConvInts.bytes_post (fun x : Std.Isize => x.val) (Trusted.btoiSigned .Isize (alloc.vec.Vec.deref b)) b Isize.min Isize.max (by
      rw [ConvInts.btoiSigned_map]
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val, IScalar.min_ISize_eq, IScalar.max_ISize_eq])
    simp only [value.convert.ParseIrOptIsize.Insts.CoreConvertTryFromValueFromValueError.try_from, value.convert.trusted.btoi_isize, bind_ok]
    split <;> rw [WP.spec_ok]
    · exact hb.1 ‹_›
    · exact hb.2 _ ‹_›
  | Int x =>
    simp only [value.convert.ParseIrOptIsize.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | UInt x =>
    simp only [value.convert.ParseIrOptIsize.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | _ => simp [value.convert.ParseIrOptIsize.Insts.CoreConvertTryFromValueFromValueError.try_from, okPart, intIr, intConv, Val.integer, Val.ofValue]

/-- `from_value_opt::<isize>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `isize`, with that integer. -/
theorem Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize v ⦃ r =>
      (okPart r).map (fun x : Std.Isize => x.val) = intConv Isize.min Isize.max (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  exact ConvInts.from_value_opt_of_try Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize (fun _ => rfl) _ _ _ v
    (value.convert.ParseIrOptIsize.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)

/-- `from_value::<isize>`: the integer, when it converts. -/
theorem Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize.from_value_spec (v : value.Value) (n : ℤ) (h : intConv Isize.min Isize.max (Val.ofValue v) = some n) :
    value.convert.from_value Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize v ⦃ x => (fun x : Std.Isize => x.val) x = n ⦄ := by
  exact ConvInts.from_value_of_opt Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize _ _ _ v n
    (Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize.from_value_opt_spec v) h

/-- `from_value::<isize>` panics when the value does not convert. -/
theorem Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize.from_value_panic (v : value.Value) (h : intConv Isize.min Isize.max (Val.ofValue v) = none) :
    value.convert.from_value Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize v = fail .panic := by
  exact ConvInts.from_value_panic_of_opt Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize _ _ _ v
    (Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize.from_value_opt_spec v) h

/-- `From<ParseIrOpt<isize>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `UInt 5` comes back as `Int 5`). -/
theorem value.Value.Insts.CoreConvertFromParseIrOptIsize.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptIsize.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptIsize.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover Isize.min Isize.max true (Val.ofValue v) ⦄ := by
  obtain ⟨r, hr, hpost⟩ := ConvInts.spec_eq_ok
    (value.convert.ParseIrOptIsize.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)
  rw [hr, bind_ok]
  rcases r with ir | e
  · exact ConvInts.recover_ok value.Value.Insts.CoreConvertFromParseIrOptIsize.from
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromIsize) (fun _ => rfl) _ _ _ _ v ir hpost
      ConvInts.fromIsize_spec
  · rw [WP.spec_ok]; exact ConvInts.recover_err _ _ _ _ v e hpost

/-- `TryFrom<Value> for ParseIrOpt<usize>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
theorem value.convert.ParseIrOptUsize.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptUsize.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.Usize => (x.val : ℤ))) = intIr 0 (Usize.max : ℤ) (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    have hb := ConvInts.bytes_post (fun x : Std.Usize => (x.val : ℤ)) (Trusted.btoiUnsigned .Usize (alloc.vec.Vec.deref b)) b 0 (Usize.max : ℤ) (by
      rw [ConvInts.btoiUnsigned_map]
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val, UScalar.max_USize_eq])
    simp only [value.convert.ParseIrOptUsize.Insts.CoreConvertTryFromValueFromValueError.try_from, value.convert.trusted.btoi_usize, bind_ok]
    split <;> rw [WP.spec_ok]
    · exact hb.1 ‹_›
    · exact hb.2 _ ‹_›
  | Int x =>
    simp only [value.convert.ParseIrOptUsize.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | UInt x =>
    simp only [value.convert.ParseIrOptUsize.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | _ => simp [value.convert.ParseIrOptUsize.Insts.CoreConvertTryFromValueFromValueError.try_from, okPart, intIr, intConv, Val.integer, Val.ofValue]

/-- `from_value_opt::<usize>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `usize`, with that integer. -/
theorem Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize v ⦃ r =>
      (okPart r).map (fun x : Std.Usize => (x.val : ℤ)) = intConv 0 (Usize.max : ℤ) (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  exact ConvInts.from_value_opt_of_try Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize (fun _ => rfl) _ _ _ v
    (value.convert.ParseIrOptUsize.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)

/-- `from_value::<usize>`: the integer, when it converts. -/
theorem Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize.from_value_spec (v : value.Value) (n : ℤ) (h : intConv 0 (Usize.max : ℤ) (Val.ofValue v) = some n) :
    value.convert.from_value Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize v ⦃ x => (fun x : Std.Usize => (x.val : ℤ)) x = n ⦄ := by
  exact ConvInts.from_value_of_opt Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize _ _ _ v n
    (Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize.from_value_opt_spec v) h

/-- `from_value::<usize>` panics when the value does not convert. -/
theorem Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize.from_value_panic (v : value.Value) (h : intConv 0 (Usize.max : ℤ) (Val.ofValue v) = none) :
    value.convert.from_value Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize v = fail .panic := by
  exact ConvInts.from_value_panic_of_opt Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize _ _ _ v
    (Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize.from_value_opt_spec v) h

/-- `From<ParseIrOpt<usize>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `Int 5` comes back as `UInt 5`). -/
theorem value.Value.Insts.CoreConvertFromParseIrOptUsize.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptUsize.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptUsize.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover 0 (Usize.max : ℤ) false (Val.ofValue v) ⦄ := by
  obtain ⟨r, hr, hpost⟩ := ConvInts.spec_eq_ok
    (value.convert.ParseIrOptUsize.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)
  rw [hr, bind_ok]
  rcases r with ir | e
  · exact ConvInts.recover_ok value.Value.Insts.CoreConvertFromParseIrOptUsize.from
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromUsize) (fun _ => rfl) _ _ _ _ v ir hpost
      ConvInts.fromUsize_spec
  · rw [WP.spec_ok]; exact ConvInts.recover_err _ _ _ _ v e hpost

/-- `TryFrom<Value> for ParseIrOpt<i128>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
theorem value.convert.ParseIrOptI128.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptI128.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.I128 => x.val)) = intIr I128.min I128.max (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    have hb := ConvInts.bytes_post (fun x : Std.I128 => x.val) (Trusted.btoiSigned .I128 (alloc.vec.Vec.deref b)) b I128.min I128.max (by
      rw [ConvInts.btoiSigned_map]
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val])
    simp only [value.convert.ParseIrOptI128.Insts.CoreConvertTryFromValueFromValueError.try_from, value.convert.trusted.btoi_i128, bind_ok]
    split <;> rw [WP.spec_ok]
    · exact hb.1 ‹_›
    · exact hb.2 _ ‹_›
  | Int x =>
    simp only [value.convert.ParseIrOptI128.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | UInt x =>
    simp only [value.convert.ParseIrOptI128.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | _ => simp [value.convert.ParseIrOptI128.Insts.CoreConvertTryFromValueFromValueError.try_from, okPart, intIr, intConv, Val.integer, Val.ofValue]

/-- `from_value_opt::<i128>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `i128`, with that integer. -/
theorem I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128 v ⦃ r =>
      (okPart r).map (fun x : Std.I128 => x.val) = intConv I128.min I128.max (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  exact ConvInts.from_value_opt_of_try I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128 (fun _ => rfl) _ _ _ v
    (value.convert.ParseIrOptI128.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)

/-- `from_value::<i128>`: the integer, when it converts. -/
theorem I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128.from_value_spec (v : value.Value) (n : ℤ) (h : intConv I128.min I128.max (Val.ofValue v) = some n) :
    value.convert.from_value I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128 v ⦃ x => (fun x : Std.I128 => x.val) x = n ⦄ := by
  exact ConvInts.from_value_of_opt I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128 _ _ _ v n
    (I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128.from_value_opt_spec v) h

/-- `from_value::<i128>` panics when the value does not convert. -/
theorem I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128.from_value_panic (v : value.Value) (h : intConv I128.min I128.max (Val.ofValue v) = none) :
    value.convert.from_value I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128 v = fail .panic := by
  exact ConvInts.from_value_panic_of_opt I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128 _ _ _ v
    (I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128.from_value_opt_spec v) h

/-- `From<ParseIrOpt<i128>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `UInt 5` comes back as `Int 5`). -/
theorem value.Value.Insts.CoreConvertFromParseIrOptI128.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptI128.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptI128.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover I128.min I128.max true (Val.ofValue v) ⦄ := by
  obtain ⟨r, hr, hpost⟩ := ConvInts.spec_eq_ok
    (value.convert.ParseIrOptI128.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)
  rw [hr, bind_ok]
  rcases r with ir | e
  · exact ConvInts.recover_ok value.Value.Insts.CoreConvertFromParseIrOptI128.from
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromI128) (fun _ => rfl) _ _ _ _ v ir hpost
      ConvInts.fromI128_spec
  · rw [WP.spec_ok]; exact ConvInts.recover_err _ _ _ _ v e hpost

/-- `TryFrom<Value> for ParseIrOpt<u128>` (= `FromValue::get_intermediate`): total. `Int`/`UInt`
    in range give `Ready n`; `Bytes` holding an ASCII decimal integer in range (`asciiInt`, per
    btoi: optional sign, digits, nothing else) give `Parsed n v`; everything else is an error
    carrying `v` (`intIr`). -/
theorem value.convert.ParseIrOptU128.Insts.CoreConvertTryFromValueFromValueError.try_from_spec (v : value.Value) :
    value.convert.ParseIrOptU128.Insts.CoreConvertTryFromValueFromValueError.try_from v ⦃ r =>
      (okPart r).map (irView (fun x : Std.U128 => (x.val : ℤ))) = intIr 0 (U128.max : ℤ) (Val.ofValue v) ∧
      (∀ t w, r = .Ok (.Parsed t w) → w = v) ∧ (okPart r = none → r = .Err v) ⦄ := by
  cases v with
  | Bytes b =>
    have hb := ConvInts.bytes_post (fun x : Std.U128 => (x.val : ℤ)) (Trusted.btoiUnsigned .U128 (alloc.vec.Vec.deref b)) b 0 (U128.max : ℤ) (by
      rw [ConvInts.btoiUnsigned_map]
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val])
    simp only [value.convert.ParseIrOptU128.Insts.CoreConvertTryFromValueFromValueError.try_from, value.convert.trusted.btoi_u128, bind_ok]
    split <;> rw [WP.spec_ok]
    · exact hb.1 ‹_›
    · exact hb.2 _ ‹_›
  | Int x =>
    simp only [value.convert.ParseIrOptU128.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | UInt x =>
    simp only [value.convert.ParseIrOptU128.Insts.CoreConvertTryFromValueFromValueError.try_from]
    step*
    all_goals int_close
  | _ => simp [value.convert.ParseIrOptU128.Insts.CoreConvertTryFromValueFromValueError.try_from, okPart, intIr, intConv, Val.integer, Val.ofValue]

/-- `from_value_opt::<u128>`: total; succeeds exactly when the value denotes an integer
    (`Val.integer`: `Int`, `UInt`, or `Bytes` per btoi) in the range of `u128`, with that integer. -/
theorem U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128.from_value_opt_spec (v : value.Value) :
    value.convert.from_value_opt U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128 v ⦃ r =>
      (okPart r).map (fun x : Std.U128 => (x.val : ℤ)) = intConv 0 (U128.max : ℤ) (Val.ofValue v) ∧
      (okPart r = none → r = .Err v) ⦄ := by
  exact ConvInts.from_value_opt_of_try U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128 (fun _ => rfl) _ _ _ v
    (value.convert.ParseIrOptU128.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)

/-- `from_value::<u128>`: the integer, when it converts. -/
theorem U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128.from_value_spec (v : value.Value) (n : ℤ) (h : intConv 0 (U128.max : ℤ) (Val.ofValue v) = some n) :
    value.convert.from_value U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128 v ⦃ x => (fun x : Std.U128 => (x.val : ℤ)) x = n ⦄ := by
  exact ConvInts.from_value_of_opt U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128 _ _ _ v n
    (U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128.from_value_opt_spec v) h

/-- `from_value::<u128>` panics when the value does not convert. -/
theorem U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128.from_value_panic (v : value.Value) (h : intConv 0 (U128.max : ℤ) (Val.ofValue v) = none) :
    value.convert.from_value U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128 v = fail .panic := by
  exact ConvInts.from_value_panic_of_opt U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128 _ _ _ v
    (U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128.from_value_opt_spec v) h

/-- `From<ParseIrOpt<u128>> for Value` after `try_from` (the error value on failure): the
    original value, except that an `Int`/`UInt` in range comes back as `Value::from` of the number
    (`intRecover`: e.g. `Int 5` comes back as `UInt 5`). -/
theorem value.Value.Insts.CoreConvertFromParseIrOptU128.recover (v : value.Value) :
    (do
      let r ← value.convert.ParseIrOptU128.Insts.CoreConvertTryFromValueFromValueError.try_from v
      match r with
      | .Ok ir => value.Value.Insts.CoreConvertFromParseIrOptU128.from ir
      | .Err e => ok e) ⦃ w => Val.ofValue w = intRecover 0 (U128.max : ℤ) false (Val.ofValue v) ⦄ := by
  obtain ⟨r, hr, hpost⟩ := ConvInts.spec_eq_ok
    (value.convert.ParseIrOptU128.Insts.CoreConvertTryFromValueFromValueError.try_from_spec v)
  rw [hr, bind_ok]
  rcases r with ir | e
  · exact ConvInts.recover_ok value.Value.Insts.CoreConvertFromParseIrOptU128.from
      (core.convert.IntoFrom value.Value.Insts.CoreConvertFromU128) (fun _ => rfl) _ _ _ _ v ir hpost
      ConvInts.fromU128_spec
  · rw [WP.spec_ok]; exact ConvInts.recover_err _ _ _ _ v e hpost

end mysql_common
