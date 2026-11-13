import Defs
import Proofs.Util.BinlogValue

/-! Statements for `fn my_datetime_packed_from_binary` (spec file: `Specs/Binlog/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `my_datetime_packed_from_binary(input, dec)`: exact when the packed value fits in `i64`: MySQL's packed DATETIME2 value (`datetime2Read`) and the rest, or an error with the input emptied when it is shorter than `5 + fracBytes dec` bytes. -/
theorem binlog.misc.my_datetime_packed_from_binary_spec (input : io.ParseBuf) (dec : U32)
    (h : ∀ p t, datetime2Read dec.val input.val = some (p, t) → -2 ^ 63 ≤ p) :
    binlog.misc.my_datetime_packed_from_binary input dec ⦃ r rest =>
      ((okPart r).map (·.val), rest.val) =
        (match datetime2Read dec.val input.val with
         | some (p, t) => (some p, t)
         | none => (none, [])) ⦄ := by
  sorry

/-- `my_datetime_packed_from_binary` panics (`i64` overflow) when the packed value is below `-2^63`: an integer part of five zero bytes (invalid: MySQL always sets the top bit) with a negative fraction. -/
theorem binlog.misc.my_datetime_packed_from_binary_overflow (input : io.ParseBuf) (dec : U32)
    (h : ∃ p t, datetime2Read dec.val input.val = some (p, t) ∧ p < -2 ^ 63) :
    binlog.misc.my_datetime_packed_from_binary input dec = fail .integerOverflow := 
  BinlogUtil.datetime_overflow input dec h

/-- Round trip: `my_datetime_packed_from_binary` reads back MySQL's encoding (`my_datetime_packed_to_binary`, `datetime2Bin`) of every non-negative packed DATETIME value below `2^63` whose fraction is a multiple of the unit of `dec` and below `10^6`. -/
theorem binlog.misc.my_datetime_packed_from_binary_roundtrip (dec : U32) (p : Int)
    (hp : 0 ≤ p ∧ p < 2 ^ 63)
    (hf : packedFracPart p % (fracUnit dec.val : Int) = 0 ∧ packedFracPart p < 10 ^ 6)
    (tail : List U8) (input : io.ParseBuf) (h : input.val = datetime2Bin dec.val p ++ tail) :
    binlog.misc.my_datetime_packed_from_binary input dec ⦃ r rest =>
      (okPart r).map (·.val) = some p ∧ rest.val = tail ⦄ := 
  BinlogUtil.datetime_roundtrip dec p hp hf tail input h

end mysql_common
