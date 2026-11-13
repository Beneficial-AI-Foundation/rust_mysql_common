import Defs.BinlogCore
import Defs.Convert

/-!
# Binlog row values

How a value of a row event (`WRITE_ROWS`, `UPDATE_ROWS`, ...) is laid out, per column type and its
table-map metadata, from MySQL's `Field::pack`/`Field::save_field_metadata` (`sql/field.cc`) and
`log_event_print_value` (`sql/log_event.cc`, the reference decoder of `mysqlbinlog`):

| column type                         | metadata (bytes)                     | value bytes                                     |
|-------------------------------------|--------------------------------------|-------------------------------------------------|
| TINY, SHORT, INT24, LONG, LONGLONG  | none                                 | 1, 2, 3, 4, 8-byte little-endian integer        |
| FLOAT, DOUBLE                       | 1 (pack length, unused)              | 4, 8-byte IEEE-754                              |
| TIMESTAMP                           | none                                 | 4-byte LE seconds since the epoch               |
| TIME (pre-5.6.4)                    | none                                 | 3-byte LE signed `±HHMMSS`                      |
| DATETIME (pre-5.6.4)                | none                                 | 8-byte LE `YYYYMMDDhhmmss`                      |
| YEAR                                | none                                 | 1 byte, `year - 1900` (0 for year `0000`)       |
| NEWDATE                             | none                                 | 3-byte LE `day + 32 * month + 512 * year`       |
| BIT                                 | 2: `bits % 8`, `bits / 8`            | `⌈bits / 8⌉` bytes                              |
| TIMESTAMP2, DATETIME2, TIME2        | 1: `dec`, the fractional digits      | `timestamp2Read`, `datetime2Read`, `time2Read`  |
| JSON                                | 1 (pack length)                      | 4-byte LE length, then the binary JSON          |
| NEWDECIMAL                          | 2: precision, scale                  | MySQL's packed decimal                          |
| ENUM                                | 2: real type, pack length (1 or 2)   | 1 or 2-byte LE index                            |
| SET                                 | 2: real type, pack length (1–4, 8)   | that many bytes (the bitmap)                    |
| BLOB types, GEOMETRY, VECTOR        | 1: length bytes `k` (1–4)            | `k`-byte LE length, then the bytes              |
| VARCHAR, VAR_STRING                 | 2: LE maximum length in bytes        | 1-byte length if max < 256, else 2-byte LE      |
| STRING                              | 2: see `stringFieldLen`              | 1-byte length if max < 256, else 2-byte LE      |

The crate (`MyDeserialize for BinlogValue`) represents some of these as text, by its own choice:
YEAR as the decimal year, TIMESTAMP2 as the decimal seconds (with a fraction `.uuuuuu` when there
is one); TIMESTAMP as an `Int` of seconds; BIT, SET and NEWDECIMAL as `Bytes`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

open constants.ColumnType

/-- The `Val` a `BinlogValue` holds, if it holds a plain value (`none` for `Jsonb`, `JsonDiff`). -/
def binlogValView : binlog.value.BinlogValue → Option Val
  | .Value v => some (Val.ofValue v)
  | _ => none

/-- A `Result` with its `Ok` value mapped. -/
def resMap {α β E : Type} (f : α → β) : core.result.Result α E → core.result.Result β E
  | .Ok x => .Ok (f x)
  | .Err e => .Err e

/-- The column type a value is decoded as: a `TYPED_ARRAY` column is decoded as the type whose code
    is its first metadata byte, or stays `TYPED_ARRAY` (unsupported) if that byte is not a type
    code. (Typed arrays are MySQL-internal, for multi-valued indexes; MySQL does not log them as
    such.) -/
def binlogEffType : constants.ColumnType → List U8 → constants.ColumnType
  | MYSQL_TYPE_TYPED_ARRAY, b :: _ => (columnTypeOfCode b.val).getD MYSQL_TYPE_TYPED_ARRAY
  | ct, _ => ct

/-- The number of metadata bytes the decoder reads for a column type (see the table). -/
def binlogMetaLen : constants.ColumnType → Nat
  | MYSQL_TYPE_STRING | MYSQL_TYPE_BIT | MYSQL_TYPE_NEWDECIMAL | MYSQL_TYPE_ENUM | MYSQL_TYPE_SET
  | MYSQL_TYPE_VARCHAR | MYSQL_TYPE_VAR_STRING => 2
  | MYSQL_TYPE_TIMESTAMP2 | MYSQL_TYPE_DATETIME2 | MYSQL_TYPE_TIME2 | MYSQL_TYPE_TINY_BLOB
  | MYSQL_TYPE_MEDIUM_BLOB | MYSQL_TYPE_LONG_BLOB | MYSQL_TYPE_BLOB | MYSQL_TYPE_GEOMETRY
  | MYSQL_TYPE_VECTOR => 1
  | _ => 0

/-- The maximum length in bytes of a `STRING` (`CHAR`) column from its two metadata bytes. MySQL
    (`Field_string::save_field_metadata`) stores `b0 = real_type ^ ((length & 0x300) >> 4)` and
    `b1 = length & 0xFF` (bug #37426: lengths up to 1023), and reads `meta = b0 << 8 | b1`: if
    `b0 & 0x30 ≠ 0x30` the length is `b1 | (((b0 & 0x30) ^ 0x30) << 4)`, else `b1`.
    **Crate behaviour when `b0 = 0`** (no real type; MySQL never writes it, and would then take
    `meta = b1` as the length): the crate reads the two bytes as a little-endian `u16`, giving
    `256 * b1`. -/
def stringFieldLen (b0 b1 : Nat) : Nat :=
  if 1 ≤ b0 then (if b0 &&& 0x30 ≠ 0x30 then b1 ||| (((b0 &&& 0x30) ^^^ 0x30) <<< 4) else b1)
  else b0 + 256 * b1

/-- The kind of panic when the metadata is too short: indexing a missing byte, except for a
    `STRING` column with the single metadata byte `0`, where the crate's `u16` read of the two
    bytes panics. -/
def binlogMetaPanic : constants.ColumnType → List U8 → Error
  | MYSQL_TYPE_STRING, [b] => if b.val = 0 then .panic else .arrayOutOfBounds
  | _, _ => .arrayOutOfBounds

/-- What decoding one binlog value does. -/
inductive BinlogOut where
  /-- `Ok(BinlogValue::Value(v))`, leaving `rest`. -/
  | ok (v : Val) (rest : List U8)
  /-- `Err(..)`, leaving `rest`. -/
  | err (rest : List U8)
  /-- A panic, with the Aeneas label of its kind (`arrayOutOfBounds` for a missing metadata
      byte, `integerOverflow` for an arithmetic overflow, `panic` otherwise). -/
  | panic (e : Error)
  /-- The value is decoded by an opaque (untranslated) helper: JSON (`jsonb`/`jsondiff`),
      NEWDECIMAL (`decimal`), or a TIMESTAMP2 with a non-zero fraction (`format!`). The statements
      for these cases are separate. -/
  | opaque

/-- A reader result as a `BinlogOut`. -/
def BinlogOut.ofRead : Option Val × List U8 → BinlogOut
  | (some v, rest) => .ok v rest
  | (none, rest) => .err rest

/-- A `k`-byte little-endian number, turned into a value by `f`; an error with the input unchanged
    if there are fewer than `k` bytes. -/
def binlogNum (k : Nat) (bs : List U8) (f : Nat → Val) : BinlogOut :=
  match readLE k bs with
  | none => .err bs
  | some (n, rest) => .ok (f n) rest

/-- `n` bytes as `Bytes`; an error with the input unchanged if there are fewer. -/
def binlogTake (n : Nat) (bs : List U8) : BinlogOut :=
  if n ≤ bs.length then .ok (.bytes (bs.take n)) (bs.drop n) else .err bs

/-- A string with a `k`-byte little-endian length prefix (`checkedLenPrefixed`) as `Bytes`. -/
def binlogStr (k : Nat) (bs : List U8) : BinlogOut :=
  match checkedLenPrefixed k bs with
  | (some s, rest) => .ok (.bytes s) rest
  | (none, rest) => .err rest

/-- The intended value of a pre-5.6.4 TIME (3-byte LE signed `±HHMMSS`, MySQL `sint3korr`), in the
    crate's representation of this type (days 0, all hours in `hours`). -/
def oldTimeVal (n : Nat) : Val :=
  let x := toSigned 24 n
  let a := x.natAbs
  .time (decide (x < 0)) 0 (a / 10000) (a % 10000 / 100) (a % 100) 0

/-- The decoder of one binlog value (`MyDeserialize for BinlogValue`, context
    `(column type, metadata, is_unsigned, is_partial)`), on input `bs`, written from the formats in
    the module docstring. Errors leave the input as the crate's readers do: unchanged when a
    fixed-size field or the value's bytes are missing, after the length prefix when the bytes
    after it are missing, and **empty** for the three `*2` temporal types (their readers follow
    `Read::read_exact`, which consumes what is left before failing).
    * **Panics** (index out of bounds) when the metadata is shorter than the type needs
      (`binlogMetaLen`, and a `TYPED_ARRAY` needs one byte); a DATETIME2 whose packed value is at
      most `-2^63` (`i64` overflow in `my_packed_time_make`, or negating `i64::MIN`; only the
      invalid integer part 0, i.e. 5 zero bytes, with a non-positive fraction gives this) panics.
    * Integers, floats: as in the binary protocol (`binRead`); INT24 is a 3-byte integer,
      sign-extended if signed (**the crate does not sign-extend**: see the bug statements; the
      main statements exclude that input with `binlogBug`).
    * TIME (pre-5.6.4): `oldTimeVal` (**the crate reads the field unsigned**: see `binlogBug`).
    * DATETIME (pre-5.6.4): the decimal digits of `YYYYMMDDhhmmss`; the year is taken mod `2^16`
      (`as u16`; only a year past 65535 is affected).
    * YEAR: the text of `1900 + byte`. **Quirk**: the byte 0, which MySQL uses for the year
      `0000`, gives `"1900"` (as `mysqlbinlog` prints it).
    * TIMESTAMP2 without fraction: the text of the seconds (`decimalBytes`).
    * DATETIME2, TIME2: `datetimeFromPacked`, `timeFromPacked` of the packed value.
    * ENUM with a pack length other than 1, 2; BLOB types with a length-bytes count other than
      1–4; DECIMAL, NULL, DATE, UNKNOWN and an unresolved TYPED_ARRAY: an error, input unchanged. -/
def binlogRead (ct : constants.ColumnType) (md : List U8) (uns : Bool) (bs : List U8) :
    BinlogOut :=
  match ct, md with
  | MYSQL_TYPE_TYPED_ARRAY, [] => .panic .arrayOutOfBounds
  | _, _ =>
  let t := binlogEffType ct md
  if md.length < binlogMetaLen t then .panic (binlogMetaPanic t md) else
  let m (i : Nat) : Nat := (md.getD i (byte 0)).val
  match t with
  | MYSQL_TYPE_TINY | MYSQL_TYPE_SHORT | MYSQL_TYPE_LONG | MYSQL_TYPE_LONGLONG
  | MYSQL_TYPE_FLOAT | MYSQL_TYPE_DOUBLE => .ofRead (binRead t uns bs)
  | MYSQL_TYPE_TIMESTAMP => binlogNum 4 bs (fun n => .int n)
  | MYSQL_TYPE_INT24 => binlogNum 3 bs (fun n => .int (if uns then n else toSigned 24 n))
  | MYSQL_TYPE_TIME => binlogNum 3 bs oldTimeVal
  | MYSQL_TYPE_DATETIME => binlogNum 8 bs (fun n =>
      let d := n / 10 ^ 6
      let s := n % 10 ^ 6
      .date (d / 10000 % 2 ^ 16) (d % 10000 / 100) (d % 100) (s / 10000) (s % 10000 / 100)
        (s % 100) 0)
  | MYSQL_TYPE_YEAR => binlogNum 1 bs (fun y => .bytes (decimalBytes (1900 + (y : Int))))
  | MYSQL_TYPE_NEWDATE => binlogNum 3 bs (fun n => .date (n / 2 ^ 9) (n / 2 ^ 5 % 2 ^ 4) (n % 2 ^ 5)
      0 0 0 0)
  | MYSQL_TYPE_BIT => binlogTake ((m 1 * 8 + m 0 + 7) / 8) bs
  | MYSQL_TYPE_TIMESTAMP2 =>
    (match timestamp2Read (m 0) bs with
     | none => .err []
     | some ((sec, us), rest) => if us = 0 then .ok (.bytes (decimalBytes sec)) rest else .opaque)
  | MYSQL_TYPE_DATETIME2 =>
    (match datetime2Read (m 0) bs with
     | none => .err []
     | some (p, rest) => if p ≤ -2 ^ 63 then .panic .integerOverflow else .ok (datetimeFromPacked p) rest)
  | MYSQL_TYPE_TIME2 =>
    (match time2Read (m 0) bs with
     | none => .err []
     | some (p, rest) => .ok (timeFromPacked p) rest)
  | MYSQL_TYPE_JSON | MYSQL_TYPE_NEWDECIMAL => .opaque
  | MYSQL_TYPE_ENUM =>
    if m 1 = 1 then binlogNum 1 bs (fun n => .int n)
    else if m 1 = 2 then binlogNum 2 bs (fun n => .int n)
    else .err bs
  | MYSQL_TYPE_SET => binlogTake (m 1) bs
  | MYSQL_TYPE_TINY_BLOB | MYSQL_TYPE_MEDIUM_BLOB | MYSQL_TYPE_LONG_BLOB | MYSQL_TYPE_BLOB
  | MYSQL_TYPE_GEOMETRY | MYSQL_TYPE_VECTOR =>
    if 1 ≤ m 0 ∧ m 0 ≤ 4 then binlogStr (m 0) bs else .err bs
  | MYSQL_TYPE_VARCHAR | MYSQL_TYPE_VAR_STRING =>
    binlogStr (if m 0 + 256 * m 1 < 256 then 1 else 2) bs
  | MYSQL_TYPE_STRING => binlogStr (if stringFieldLen (m 0) (m 1) < 256 then 1 else 2) bs
  | _ => .err bs

/-- The inputs on which the crate departs from `binlogRead` on data MySQL writes (upstream bugs;
    the actual behaviour is stated separately):
    * a signed INT24 with bit 23 set (a negative MEDIUMINT): the crate does not sign-extend;
    * a pre-5.6.4 TIME that is negative or has 256 hours or more (MySQL's range is
      ±838:59:59): the crate reads it unsigned and takes the hours mod 256;
    * a TIME2 with 1–2 fractional digits that is negative with a non-zero fraction: the crate
      panics (`u32` underflow). -/
def binlogBug (ct : constants.ColumnType) (md : List U8) (uns : Bool) (bs : List U8) : Prop :=
  match binlogEffType ct md with
  | MYSQL_TYPE_INT24 => uns = false ∧ 3 ≤ bs.length ∧ 2 ^ 23 ≤ leNat (bs.take 3)
  | MYSQL_TYPE_TIME =>
    3 ≤ bs.length ∧ (2 ^ 23 ≤ leNat (bs.take 3) ∨ 256 ≤ leNat (bs.take 3) / 10000)
  | MYSQL_TYPE_TIME2 => time2NegFracBug (md.getD 0 (byte 0)).val bs
  | _ => False

/-! ## Encoding (for the round trips)

`binlogEnc ct md uns v` is the binlog encoding of the value `v` in a column of type `ct` with
metadata `meta` and signedness `uns` (MySQL's `Field::pack`), when `v` is a value such a column
holds, in the crate's representation; `none` otherwise. It covers the types whose values the crate
represents as `Val`s other than text (not YEAR, TIMESTAMP2: see their own round trips; not JSON,
NEWDECIMAL). -/

/-- The encoding of an integer column of `w` bytes: `Int x` in the column's range (unsigned:
    `[0, 2^(8w))`, with LONGLONG values from `2^63` as `UInt`; signed: two's complement). -/
def binlogIntEnc (w : Nat) (uns : Bool) : Val → Option (List U8)
  | .int x =>
    if (uns = true ∧ 0 ≤ x ∧ x < 2 ^ (8 * w) ∧ (w = 8 → x < 2 ^ 63)) ∨
        (uns = false ∧ -2 ^ (8 * w - 1) ≤ x ∧ x < 2 ^ (8 * w - 1)) then some (leBytesI w x)
    else none
  | .uint x => if w = 8 ∧ uns = true ∧ 2 ^ 63 ≤ x ∧ x < 2 ^ 64 then some (leBytes 8 x) else none
  | _ => none

/-- `binlogEnc`: see the section docstring. Field ranges are MySQL's: TIME (pre-5.6.4) up to
    ±838:59:59; DATETIME years up to 9999; TIME2 up to 1023 hours in total (`days * 24 + hours`),
    DATETIME2 years up to 9999, fractions `< 10^6` and a multiple of `fracUnit dec`; a negative
    zero time is not a value (MySQL normalises it). -/
def binlogEnc (ct : constants.ColumnType) (md : List U8) (uns : Bool) (v : Val) :
    Option (List U8) :=
  if md.length < binlogMetaLen ct then none else
  let m (i : Nat) : Nat := (md.getD i (byte 0)).val
  match ct, v with
  | MYSQL_TYPE_TINY, v => binlogIntEnc 1 uns v
  | MYSQL_TYPE_SHORT, v => binlogIntEnc 2 uns v
  | MYSQL_TYPE_INT24, v => binlogIntEnc 3 uns v
  | MYSQL_TYPE_LONG, v => binlogIntEnc 4 uns v
  | MYSQL_TYPE_LONGLONG, v => binlogIntEnc 8 uns v
  | MYSQL_TYPE_FLOAT, .float b => if b < 2 ^ 32 then some (leBytes 4 b) else none
  | MYSQL_TYPE_DOUBLE, .double b => if b < 2 ^ 64 then some (leBytes 8 b) else none
  | MYSQL_TYPE_TIMESTAMP, .int x => if 0 ≤ x ∧ x < 2 ^ 32 then some (leBytes 4 x.toNat) else none
  | MYSQL_TYPE_TIME, .time neg 0 h mi s 0 =>
    if h ≤ 838 ∧ mi < 60 ∧ s < 60 ∧ ¬(neg = true ∧ h = 0 ∧ mi = 0 ∧ s = 0) then
      some (leBytesI 3 ((if neg then -1 else 1) * ((h * 10000 + mi * 100 + s : Nat) : Int)))
    else none
  | MYSQL_TYPE_DATETIME, .date y mo d h mi s 0 =>
    if y ≤ 9999 ∧ mo < 100 ∧ d < 100 ∧ h < 100 ∧ mi < 100 ∧ s < 100 then
      some (leBytes 8 ((y * 10000 + mo * 100 + d) * 10 ^ 6 + h * 10000 + mi * 100 + s))
    else none
  | MYSQL_TYPE_NEWDATE, .date y mo d 0 0 0 0 =>
    if y < 2 ^ 15 ∧ mo < 16 ∧ d < 32 then some (leBytes 3 (y * 512 + mo * 32 + d)) else none
  | MYSQL_TYPE_BIT, .bytes s => if s.length = (m 1 * 8 + m 0 + 7) / 8 then some s else none
  | MYSQL_TYPE_ENUM, .int x =>
    if (m 1 = 1 ∨ m 1 = 2) ∧ 0 ≤ x ∧ x < 2 ^ (8 * m 1) then some (leBytes (m 1) x.toNat) else none
  | MYSQL_TYPE_SET, .bytes s => if s.length = m 1 then some s else none
  | MYSQL_TYPE_TINY_BLOB, .bytes s | MYSQL_TYPE_MEDIUM_BLOB, .bytes s
  | MYSQL_TYPE_LONG_BLOB, .bytes s | MYSQL_TYPE_BLOB, .bytes s | MYSQL_TYPE_GEOMETRY, .bytes s
  | MYSQL_TYPE_VECTOR, .bytes s =>
    if 1 ≤ m 0 ∧ m 0 ≤ 4 ∧ s.length < 2 ^ (8 * m 0) then some (leBytes (m 0) s.length ++ s)
    else none
  | MYSQL_TYPE_VARCHAR, .bytes s | MYSQL_TYPE_VAR_STRING, .bytes s =>
    if s.length ≤ m 0 + 256 * m 1 then
      some (leBytes (if m 0 + 256 * m 1 < 256 then 1 else 2) s.length ++ s)
    else none
  | MYSQL_TYPE_STRING, .bytes s =>
    if 1 ≤ m 0 ∧ s.length ≤ stringFieldLen (m 0) (m 1) then
      some (leBytes (if stringFieldLen (m 0) (m 1) < 256 then 1 else 2) s.length ++ s)
    else none
  | MYSQL_TYPE_TIME2, .time neg d h mi s us =>
    if h < 24 ∧ mi < 60 ∧ s < 60 ∧ d * 24 + h < 1024 ∧ us < 10 ^ 6 ∧ us % fracUnit (m 0) = 0 ∧
        ¬(neg = true ∧ d = 0 ∧ h = 0 ∧ mi = 0 ∧ s = 0 ∧ us = 0) then
      some (time2Bin (m 0) (timePack neg d h mi s us))
    else none
  | MYSQL_TYPE_DATETIME2, .date y mo d h mi s us =>
    if y ≤ 9999 ∧ mo ≤ 12 ∧ d < 32 ∧ h < 24 ∧ mi < 60 ∧ s < 60 ∧ us < 10 ^ 6 ∧
        us % fracUnit (m 0) = 0 then
      some (datetime2Bin (m 0) (datetimePack y mo d h mi s us))
    else none
  | _, _ => none

/-- The encoded values the crate does not read back (`binlogBug`): a negative signed INT24; a
    negative pre-5.6.4 TIME or one with 256 hours or more; a negative TIME2 with 1–2 fractional
    digits and a non-zero fraction. -/
def binlogEncBug (ct : constants.ColumnType) (md : List U8) (uns : Bool) : Val → Prop
  | .int x => ct = MYSQL_TYPE_INT24 ∧ uns = false ∧ x < 0
  | .time neg _ h _ _ us =>
    (ct = MYSQL_TYPE_TIME ∧ (neg = true ∨ 256 ≤ h)) ∨
    (ct = MYSQL_TYPE_TIME2 ∧ ((md.getD 0 (byte 0)).val = 1 ∨ (md.getD 0 (byte 0)).val = 2) ∧
      neg = true ∧ us ≠ 0)
  | _ => False

/-! ## Rows -/

/-- The value in cell `i` of a binlog row with cells `cells`: `none` when there is no cell `i` or
    its value was taken. -/
def binlogCellAt (cells : List (Option binlog.value.BinlogValue)) (i : Nat) :
    Option binlog.value.BinlogValue :=
  match cells[i]? with
  | some (some v) => some v
  | _ => none

end Defs
