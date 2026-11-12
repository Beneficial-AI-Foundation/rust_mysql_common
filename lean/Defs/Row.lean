import Defs.Value
import Defs.NullBitmap

/-!
# Result-set rows

From the protocol:

* Text row (<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_com_query_response_text_resultset_row.html>):
  one value per column, each either `0xFB` (NULL) or a length-encoded string.
* Binary row (<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_binary_resultset.html>,
  `ProtocolBinary::ResultsetRow`): a header byte `0x00`, a NULL bitmap with bit offset 2 for the
  columns, then the binary value (`binEnc`) of every non-NULL column, in column order, each in the
  format of its column type.

The decoders below describe the crate's readers, which build on the value decoders `textRead` and
`binRead` of `Defs/Value.lean`; where they accept input the protocol does not define, the
docstrings say so.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- The type of a column and whether it has `UNSIGNED_FLAG`: what the binary decoder of a value
    needs to know about its column. -/
def colInfo (c : packets.Column) : constants.ColumnType × Bool :=
  (c.column_type.1, isUnsigned c.flags.1)

/-- The values of a row, as the specs describe them (`None` for a cell taken out with `take`). -/
def rowVals (r : row.Row) : List (Option Val) := r.values.val.map (Option.map Val.ofValue)

/-- Puts `v` in front of a decoded list, keeping a failure. -/
def consRead {α : Type} (v : α) : Option (List α) × List U8 → Option (List α) × List U8
  | (some vs, rest) => (some (v :: vs), rest)
  | (none, rest) => (none, rest)

/-! ## Text rows -/

/-- The crate's reader of a text row of `n` columns: `n` values read one after the other by
    `textRead`, stopping at the first failure (with what that read left of the input). Bytes after
    the `n` values are left unread. -/
def textRowRead : Nat → List U8 → Option (List Val) × List U8
  | 0, bs => (some [], bs)
  | n + 1, bs =>
    match textRead bs with
    | (some v, rest) => consRead v (textRowRead n rest)
    | (none, rest) => (none, rest)

/-- The text-protocol encoding of a value that has one: `NULL` is `0xFB`, `Bytes s` is the
    length-encoded string `s`. (Other values are sent as their text form, a `Bytes`.) -/
def textEnc : Val → List U8
  | .null => [byte 0xFB]
  | .bytes s => lenencStr s
  | _ => []

/-- Whether a value is sent as is in a text row: `NULL` or `Bytes`. -/
def isTextVal : Val → Bool
  | .null | .bytes _ => true
  | _ => false

/-! ## Binary rows -/

/-- Whether a value is `NULL`. -/
def isNullVal : Val → Bool
  | .null => true
  | _ => false

/-- The crate's reader of the values of a binary row, for the columns `cols` (type and
    `UNSIGNED_FLAG`) starting at column index `i`, with NULL bitmap `bm` (bit offset `off`): a
    column marked NULL gives `NULL` and reads nothing; any other column is read by `binRead` at its
    type, stopping at the first failure. -/
def binValuesRead (off : Nat) (bm : List U8) :
    List (constants.ColumnType × Bool) → Nat → List U8 → Option (List Val) × List U8
  | [], _, bs => (some [], bs)
  | (ct, u) :: cols, i, bs =>
    if bitmapBit off bm i then consRead .null (binValuesRead off bm cols (i + 1) bs)
    else match binRead ct u bs with
      | (some v, rest) => consRead v (binValuesRead off bm cols (i + 1) rest)
      | (none, rest) => (none, rest)

/-- The crate's reader of a binary row for the columns `cols`, NULL bitmap offset `off`.
    **Crate behaviour**: the header byte is read but not checked (the protocol says `0x00`; any
    byte is accepted). `none` if the input is empty (nothing consumed) or the bitmap is truncated
    (the header consumed); otherwise `binValuesRead`. -/
def binRowRead (off : Nat) (cols : List (constants.ColumnType × Bool)) :
    List U8 → Option (List Val) × List U8
  | [] => (none, [])
  | _header :: rest =>
    let k := nullBitmapLen off cols.length
    if rest.length < k then (none, rest)
    else binValuesRead off (rest.take k) cols 0 (rest.drop k)

/-- The protocol's binary row of the values `vs` with NULL bitmap offset `off`: `0x00`, the NULL
    bitmap, then the binary encodings of the non-NULL values (`binEnc .null` is empty). -/
def binRowEnc (off : Nat) (vs : List Val) : List U8 :=
  byte 0 :: nullBitmap off (vs.map isNullVal) ++ (vs.map binEnc).flatten

end Defs
