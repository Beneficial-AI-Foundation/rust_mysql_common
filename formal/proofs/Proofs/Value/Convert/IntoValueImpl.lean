import Defs
import Proofs.Util.ConvInts
import Proofs.Value.Convert.ImplFromValueNum

/-! Statements for `macro into_value_impl! (i8, i16, i32, i64, isize, u8, u16, u32, u64, usize), impl From<i128>, From<u128> for Value` (spec file: `Specs/Value/Convert.lean`). Helper lemmas: `Proofs/Util/ConvInts.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs Classical

namespace mysql_common

/-- `From<i8> for Value`: `Int` of the number. -/
theorem value.Value.Insts.CoreConvertFromI8.from_spec (x : Std.I8) :
    value.Value.Insts.CoreConvertFromI8.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄ := by
  exact ConvInts.fromI8_spec x

/-- Round trip: `from_value_opt::<i8>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromI8.from_roundtrip (x : Std.I8) :
    (do let w ← value.Value.Insts.CoreConvertFromI8.from x; value.convert.from_value_opt I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 w) ⦃ r => r = .Ok x ⦄ := by
  exact ConvInts.roundtrip_of _ I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8 (fun x : Std.I8 => x.val) I8.min I8.max true x
    (ConvInts.fromI8_spec x) I8.Insts.Mysql_commonValueConvertFromValueParseIrOptI8.from_value_opt_spec (fun a b h => IScalar.eq_of_val_eq h)
    (by have := x.hBounds; scalar_tac)

/-- `From<u8> for Value`: `UInt` of the number. -/
theorem value.Value.Insts.CoreConvertFromU8.from_spec (x : Std.U8) :
    value.Value.Insts.CoreConvertFromU8.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄ := by
  exact ConvInts.fromU8_spec x

/-- Round trip: `from_value_opt::<u8>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromU8.from_roundtrip (x : Std.U8) :
    (do let w ← value.Value.Insts.CoreConvertFromU8.from x; value.convert.from_value_opt U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8 w) ⦃ r => r = .Ok x ⦄ := by
  exact ConvInts.roundtrip_of _ U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8 (fun x : Std.U8 => (x.val : ℤ)) 0 (U8.max : ℤ) false x
    (ConvInts.fromU8_spec x) U8.Insts.Mysql_commonValueConvertFromValueParseIrOptU8.from_value_opt_spec (fun a b h => UScalar.eq_of_val_eq (by simpa using h))
    (by have := x.hBounds; scalar_tac)

/-- `From<i16> for Value`: `Int` of the number. -/
theorem value.Value.Insts.CoreConvertFromI16.from_spec (x : Std.I16) :
    value.Value.Insts.CoreConvertFromI16.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄ := by
  exact ConvInts.fromI16_spec x

/-- Round trip: `from_value_opt::<i16>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromI16.from_roundtrip (x : Std.I16) :
    (do let w ← value.Value.Insts.CoreConvertFromI16.from x; value.convert.from_value_opt I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16 w) ⦃ r => r = .Ok x ⦄ := by
  exact ConvInts.roundtrip_of _ I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16 (fun x : Std.I16 => x.val) I16.min I16.max true x
    (ConvInts.fromI16_spec x) I16.Insts.Mysql_commonValueConvertFromValueParseIrOptI16.from_value_opt_spec (fun a b h => IScalar.eq_of_val_eq h)
    (by have := x.hBounds; scalar_tac)

/-- `From<u16> for Value`: `UInt` of the number. -/
theorem value.Value.Insts.CoreConvertFromU16.from_spec (x : Std.U16) :
    value.Value.Insts.CoreConvertFromU16.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄ := by
  exact ConvInts.fromU16_spec x

/-- Round trip: `from_value_opt::<u16>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromU16.from_roundtrip (x : Std.U16) :
    (do let w ← value.Value.Insts.CoreConvertFromU16.from x; value.convert.from_value_opt U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16 w) ⦃ r => r = .Ok x ⦄ := by
  exact ConvInts.roundtrip_of _ U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16 (fun x : Std.U16 => (x.val : ℤ)) 0 (U16.max : ℤ) false x
    (ConvInts.fromU16_spec x) U16.Insts.Mysql_commonValueConvertFromValueParseIrOptU16.from_value_opt_spec (fun a b h => UScalar.eq_of_val_eq (by simpa using h))
    (by have := x.hBounds; scalar_tac)

/-- `From<i32> for Value`: `Int` of the number. -/
theorem value.Value.Insts.CoreConvertFromI32.from_spec (x : Std.I32) :
    value.Value.Insts.CoreConvertFromI32.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄ := by
  exact ConvInts.fromI32_spec x

/-- Round trip: `from_value_opt::<i32>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromI32.from_roundtrip (x : Std.I32) :
    (do let w ← value.Value.Insts.CoreConvertFromI32.from x; value.convert.from_value_opt I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32 w) ⦃ r => r = .Ok x ⦄ := by
  exact ConvInts.roundtrip_of _ I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32 (fun x : Std.I32 => x.val) I32.min I32.max true x
    (ConvInts.fromI32_spec x) I32.Insts.Mysql_commonValueConvertFromValueParseIrOptI32.from_value_opt_spec (fun a b h => IScalar.eq_of_val_eq h)
    (by have := x.hBounds; scalar_tac)

/-- `From<u32> for Value`: `UInt` of the number. -/
theorem value.Value.Insts.CoreConvertFromU32.from_spec (x : Std.U32) :
    value.Value.Insts.CoreConvertFromU32.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄ := by
  exact ConvInts.fromU32_spec x

/-- Round trip: `from_value_opt::<u32>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromU32.from_roundtrip (x : Std.U32) :
    (do let w ← value.Value.Insts.CoreConvertFromU32.from x; value.convert.from_value_opt U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32 w) ⦃ r => r = .Ok x ⦄ := by
  exact ConvInts.roundtrip_of _ U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32 (fun x : Std.U32 => (x.val : ℤ)) 0 (U32.max : ℤ) false x
    (ConvInts.fromU32_spec x) U32.Insts.Mysql_commonValueConvertFromValueParseIrOptU32.from_value_opt_spec (fun a b h => UScalar.eq_of_val_eq (by simpa using h))
    (by have := x.hBounds; scalar_tac)

/-- `From<i64> for Value`: `Int` of the number. -/
theorem value.Value.Insts.CoreConvertFromI64.from_spec (x : Std.I64) :
    value.Value.Insts.CoreConvertFromI64.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄ := by
  exact ConvInts.fromI64_spec x

/-- Round trip: `from_value_opt::<i64>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromI64.from_roundtrip (x : Std.I64) :
    (do let w ← value.Value.Insts.CoreConvertFromI64.from x; value.convert.from_value_opt I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 w) ⦃ r => r = .Ok x ⦄ := by
  exact ConvInts.roundtrip_of _ I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64 (fun x : Std.I64 => x.val) I64.min I64.max true x
    (ConvInts.fromI64_spec x) I64.Insts.Mysql_commonValueConvertFromValueParseIrOptI64.from_value_opt_spec (fun a b h => IScalar.eq_of_val_eq h)
    (by have := x.hBounds; scalar_tac)

/-- `From<u64> for Value`: `UInt` of the number. -/
theorem value.Value.Insts.CoreConvertFromU64.from_spec (x : Std.U64) :
    value.Value.Insts.CoreConvertFromU64.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄ := by
  exact ConvInts.fromU64_spec x

/-- Round trip: `from_value_opt::<u64>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromU64.from_roundtrip (x : Std.U64) :
    (do let w ← value.Value.Insts.CoreConvertFromU64.from x; value.convert.from_value_opt U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64 w) ⦃ r => r = .Ok x ⦄ := by
  exact ConvInts.roundtrip_of _ U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64 (fun x : Std.U64 => (x.val : ℤ)) 0 (U64.max : ℤ) false x
    (ConvInts.fromU64_spec x) U64.Insts.Mysql_commonValueConvertFromValueParseIrOptU64.from_value_opt_spec (fun a b h => UScalar.eq_of_val_eq (by simpa using h))
    (by have := x.hBounds; scalar_tac)

/-- `From<isize> for Value`: `Int` of the number. -/
theorem value.Value.Insts.CoreConvertFromIsize.from_spec (x : Std.Isize) :
    value.Value.Insts.CoreConvertFromIsize.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄ := by
  exact ConvInts.fromIsize_spec x

/-- Round trip: `from_value_opt::<isize>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromIsize.from_roundtrip (x : Std.Isize) :
    (do let w ← value.Value.Insts.CoreConvertFromIsize.from x; value.convert.from_value_opt Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize w) ⦃ r => r = .Ok x ⦄ := by
  exact ConvInts.roundtrip_of _ Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize (fun x : Std.Isize => x.val) Isize.min Isize.max true x
    (ConvInts.fromIsize_spec x) Isize.Insts.Mysql_commonValueConvertFromValueParseIrOptIsize.from_value_opt_spec (fun a b h => IScalar.eq_of_val_eq h)
    (by have := x.hBounds; scalar_tac)

/-- `From<usize> for Value`: `UInt` of the number. -/
theorem value.Value.Insts.CoreConvertFromUsize.from_spec (x : Std.Usize) :
    value.Value.Insts.CoreConvertFromUsize.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄ := by
  exact ConvInts.fromUsize_spec x

/-- Round trip: `from_value_opt::<usize>(Value::from(x)) = Ok(x)`. -/
theorem value.Value.Insts.CoreConvertFromUsize.from_roundtrip (x : Std.Usize) :
    (do let w ← value.Value.Insts.CoreConvertFromUsize.from x; value.convert.from_value_opt Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize w) ⦃ r => r = .Ok x ⦄ := by
  exact ConvInts.roundtrip_of _ Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize (fun x : Std.Usize => (x.val : ℤ)) 0 (Usize.max : ℤ) false x
    (ConvInts.fromUsize_spec x) Usize.Insts.Mysql_commonValueConvertFromValueParseIrOptUsize.from_value_opt_spec (fun a b h => UScalar.eq_of_val_eq (by simpa using h))
    (by have := x.hBounds; scalar_tac)

/-- `From<i128> for Value`: `Int` if the number fits in an `i64`, else `UInt` if it fits in a `u64`, else `Bytes` of its decimal representation (`intVal`). -/
theorem value.Value.Insts.CoreConvertFromI128.from_spec (x : Std.I128) :
    value.Value.Insts.CoreConvertFromI128.from x ⦃ w => Val.ofValue w = intVal true x.val ⦄ := by
  exact ConvInts.fromI128_spec x

/-- Round trip: `from_value_opt::<i128>(Value::from(x)) = Ok(x)` (through the decimal text for values outside the 64-bit ranges). -/
theorem value.Value.Insts.CoreConvertFromI128.from_roundtrip (x : Std.I128) :
    (do let w ← value.Value.Insts.CoreConvertFromI128.from x; value.convert.from_value_opt I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128 w) ⦃ r => r = .Ok x ⦄ := by
  exact ConvInts.roundtrip_of _ I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128 (fun x : Std.I128 => x.val) I128.min I128.max true x
    (ConvInts.fromI128_spec x) I128.Insts.Mysql_commonValueConvertFromValueParseIrOptI128.from_value_opt_spec (fun a b h => IScalar.eq_of_val_eq h)
    (by have := x.hBounds; scalar_tac)

/-- `From<u128> for Value`: `UInt` if the number fits in a `u64`, else `Bytes` of its decimal representation (`intVal`). -/
theorem value.Value.Insts.CoreConvertFromU128.from_spec (x : Std.U128) :
    value.Value.Insts.CoreConvertFromU128.from x ⦃ w => Val.ofValue w = intVal false (x.val : ℤ) ⦄ := by
  exact ConvInts.fromU128_spec x

/-- Round trip: `from_value_opt::<u128>(Value::from(x)) = Ok(x)` (through the decimal text for values outside the 64-bit ranges). -/
theorem value.Value.Insts.CoreConvertFromU128.from_roundtrip (x : Std.U128) :
    (do let w ← value.Value.Insts.CoreConvertFromU128.from x; value.convert.from_value_opt U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128 w) ⦃ r => r = .Ok x ⦄ := by
  exact ConvInts.roundtrip_of _ U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128 (fun x : Std.U128 => (x.val : ℤ)) 0 (U128.max : ℤ) false x
    (ConvInts.fromU128_spec x) U128.Insts.Mysql_commonValueConvertFromValueParseIrOptU128.from_value_opt_spec (fun a b h => UScalar.eq_of_val_eq (by simpa using h))
    (by have := x.hBounds; scalar_tac)

end mysql_common
