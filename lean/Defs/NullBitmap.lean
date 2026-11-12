import Defs.Bytes

/-!
# NULL bitmaps

From the protocol, "NULL-Bitmap"
(<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_binary_resultset.html>,
binary result set rows and `COM_STMT_EXECUTE`): a NULL bitmap for `n` fields with bit offset
`off` has `(n + 7 + off) / 8` bytes; field `i` is NULL iff bit `(i + off) % 8` of byte
`(i + off) / 8` is set (bit 0 is the least significant). The offset is 2 in binary result-set rows
(`ServerSide`) and 0 in `COM_STMT_EXECUTE` (`ClientSide`).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- The number of bytes of a NULL bitmap for `n` fields with bit offset `off`. -/
def nullBitmapLen (off n : Nat) : Nat := (n + 7 + off) / 8

/-- Bit `pos` of the byte string `bm`, counting from bit 0 of byte 0 (`false` past the end). -/
def bitAt (bm : List U8) (pos : Nat) : Bool := (bm.getD (pos / 8) (byte 0)).val.testBit (pos % 8)

/-- Whether field `i` is marked NULL in the bitmap `bm` with bit offset `off`. -/
def bitmapBit (off : Nat) (bm : List U8) (i : Nat) : Bool := bitAt bm (i + off)

/-- The number whose bits, least significant first, are `bs`. -/
def bitsToNat : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

/-- The NULL bitmap with bit offset `off` of fields whose NULL-ness is `nulls`:
    `nullBitmapLen off nulls.length` bytes, the first `off` bits and the padding bits clear, and
    bit `i + off` set iff `nulls[i]`. -/
def nullBitmap (off : Nat) (nulls : List Bool) : List U8 :=
  let bits := List.replicate off false ++ nulls
  (List.range (nullBitmapLen off nulls.length)).map fun j => byte (bitsToNat ((bits.drop (8 * j)).take 8))

end Defs
