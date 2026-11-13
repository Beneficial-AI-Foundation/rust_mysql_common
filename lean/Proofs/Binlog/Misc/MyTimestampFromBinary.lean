import Defs
import Proofs.Util.BinlogValue

/-! Statements for `fn my_timestamp_from_binary` (spec file: `Specs/Binlog/Misc.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `my_timestamp_from_binary(input, dec)`: total; the seconds and microseconds (`timestamp2Read`) and the rest, or an error with the input emptied when it is shorter than `4 + fracBytes dec` bytes. -/
theorem binlog.misc.my_timestamp_from_binary_spec (input : io.ParseBuf) (dec : U8) :
    binlog.misc.my_timestamp_from_binary input dec ⦃ r rest =>
      ((okPart r).map (fun x => (x.1.val, x.2.val)), rest.val) =
        (match timestamp2Read dec.val input.val with
         | some (x, t) => (some x, t)
         | none => (none, [])) ⦄ := 
  BinlogUtil.timestamp_spec input dec

/-- Round trip: `my_timestamp_from_binary` reads back MySQL's encoding (`my_timestamp_to_binary`, `timestamp2Bin`) of every TIMESTAMP in range (seconds below `2^31`, MySQL's 2038 limit; fraction a multiple of the unit of `dec` and below `10^6`). -/
theorem binlog.misc.my_timestamp_from_binary_roundtrip (dec : U8) (sec usec : Nat) (hs : sec < 2 ^ 31)
    (hu : usec < 10 ^ 6 ∧ usec % fracUnit dec.val = 0)
    (tail : List U8) (input : io.ParseBuf) (h : input.val = timestamp2Bin dec.val sec usec ++ tail) :
    binlog.misc.my_timestamp_from_binary input dec ⦃ r rest =>
      (okPart r).map (fun x => (x.1.val, x.2.val)) = some ((sec : Int), (usec : Int)) ∧
        rest.val = tail ⦄ := 
  BinlogUtil.timestamp_roundtrip dec sec usec hs hu tail input h

end mysql_common
