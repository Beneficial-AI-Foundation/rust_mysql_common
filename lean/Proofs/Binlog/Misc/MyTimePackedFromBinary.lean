import Defs
import Proofs.Util.BinlogValue

/-! Statements for `fn my_time_packed_from_binary` (spec file: `Specs/Binlog/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `my_time_packed_from_binary(input, dec)`: exact on any input outside the bug below: MySQL's packed TIME2 value (`time2Read`) and the rest of the input, or an error with the input emptied when it is shorter than `3 + fracBytes dec` bytes. -/
theorem binlog.misc.my_time_packed_from_binary_spec (input : io.ParseBuf) (dec : U32)
    (hbug : ¬ time2NegFracBug dec.val input.val) :
    binlog.misc.my_time_packed_from_binary input dec ⦃ r rest =>
      ((okPart r).map (·.val), rest.val) =
        (match time2Read dec.val input.val with
         | some (p, t) => (some p, t)
         | none => (none, [])) ⦄ := by
  sorry

/-- **Bug (crash path).** With 1 or 2 fractional digits, a negative integer part and a non-zero fraction byte (`time2NegFracBug`: every negative TIME(1)/TIME(2) value with a fraction, see `Defs.time2NegFracBug_time2Bin`), the crate computes MySQL's `frac -= 0x100` (an `int` in MySQL) in `u32` and panics: in debug builds only; release builds wrap and return a wrong value (e.g. `42949672460000` as the fraction term). -/
theorem binlog.misc.my_time_packed_from_binary_neg_frac (input : io.ParseBuf) (dec : U32)
    (h : time2NegFracBug dec.val input.val) :
    binlog.misc.my_time_packed_from_binary input dec = fail .integerOverflow := 
  BinlogUtil.time_neg_frac input dec h

/-- Round trip: `my_time_packed_from_binary` reads back MySQL's encoding (`my_time_packed_to_binary`, `time2Bin`) of every packed TIME value in range (integer part in 23 bits plus sign, fraction a multiple of the unit of `dec` and below `10^6`), except the bug's: negative values with a fraction at 1–2 digits. -/
theorem binlog.misc.my_time_packed_from_binary_roundtrip (dec : U32) (p : Int)
    (hp : -2 ^ 47 ≤ p ∧ p < 2 ^ 47)
    (hf : packedFracPart p % (fracUnit dec.val : Int) = 0 ∧ (packedFracPart p).natAbs < 10 ^ 6)
    (hbug : ¬((dec.val = 1 ∨ dec.val = 2) ∧ p < 0 ∧ packedFracPart p ≠ 0))
    (tail : List U8) (input : io.ParseBuf) (h : input.val = time2Bin dec.val p ++ tail) :
    binlog.misc.my_time_packed_from_binary input dec ⦃ r rest =>
      (okPart r).map (·.val) = some p ∧ rest.val = tail ⦄ := 
  BinlogUtil.time_roundtrip dec p hp hf hbug tail input h

end mysql_common
