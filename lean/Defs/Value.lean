import Defs.LenEnc

/-!
# MySQL values on the wire

`Val` is a mathematical copy of `mysql_common::value::Value`. `binEnc` is the binary-protocol
encoding of a value and `binRead` the binary-protocol decoder for a column type, both from
<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_binary_resultset.html>
("Binary Protocol Value"); `textRead` is the text-protocol decoder, from
<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_com_query_response_text_resultset_row.html>.
Where the crate's decoders accept input the protocol does not define, the docstrings below say what
they do with it.

Binary protocol (per column type):

| column type                                             | bytes                                  |
|---------------------------------------------------------|----------------------------------------|
| STRING, VARCHAR, VAR_STRING, ENUM, SET, LONG_BLOB, MEDIUM_BLOB, BLOB, TINY_BLOB, GEOMETRY, BIT, DECIMAL, NEWDECIMAL, JSON, VECTOR | length-encoded string |
| LONGLONG                                                | 8-byte integer                         |
| LONG, INT24                                             | 4-byte integer                         |
| SHORT, YEAR                                             | 2-byte integer                         |
| TINY                                                    | 1-byte integer                         |
| DOUBLE                                                  | 8-byte IEEE-754 double                 |
| FLOAT                                                   | 4-byte IEEE-754 single                 |
| DATE, DATETIME, TIMESTAMP (and NEWDATE)                 | length byte 0, 4, 7 or 11, then fields |
| TIME                                                    | length byte 0, 8 or 12, then fields    |
| NULL                                                    | nothing (NULLs are in the row bitmap)  |

All integers are little-endian; integer columns are signed or unsigned by the column's
`UNSIGNED_FLAG`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-- A MySQL value, as the specs describe it: the variants of `mysql_common::value::Value`, with
    numbers for fields and floats as their IEEE-754 bit patterns. -/
inductive Val where
  | null
  | bytes (b : List U8)
  | int (x : Int)
  | uint (x : Nat)
  | float (bits : Nat)
  | double (bits : Nat)
  /-- year, month, day, hour, minute, second, microsecond -/
  | date (year month day hour minute second micro : Nat)
  /-- is negative, days, hours, minutes, seconds, microseconds -/
  | time (neg : Bool) (days hours minutes seconds micro : Nat)
deriving DecidableEq

/-- The `Val` of a Rust `Value`. -/
def Val.ofValue : value.Value → Val
  | .NULL => .null
  | .Bytes v => .bytes v.val
  | .Int x => .int x.val
  | .UInt x => .uint x.val
  | .Float f => .float f.bits.val
  | .Double f => .double f.bits.val
  | .Date y mo d h mi s us => .date y.val mo.val d.val h.val mi.val s.val us.val
  | .Time n d h mi s us => .time n d.val h.val mi.val s.val us.val

/-! ## Binary encoding -/

/-- The binary-protocol encoding of a value. Temporal values use the shortest form the protocol
    allows: a DATE/DATETIME is sent with length 0 if all its fields are 0, else with length 4 if
    its time and microseconds are 0, else with length 7 if its microseconds are 0, else with length
    11; a TIME with length 0 if days to microseconds are all 0, else 8 if its microseconds are 0,
    else 12. (The protocol page states the length-4 condition as "hour, seconds and micro_seconds
    are all 0", omitting the minutes; MySQL itself, and the crate, also require minutes = 0.) The
    sign of a TIME is a byte, 1 for negative and 0 otherwise. `NULL` has no bytes. -/
def binEnc : Val → List U8
  | .null => []
  | .bytes b => lenencStr b
  | .int x => leBytesI 8 x
  | .uint x => leBytes 8 x
  | .float bits => leBytes 4 bits
  | .double bits => leBytes 8 bits
  | .date y mo d h mi s us =>
    if y = 0 ∧ mo = 0 ∧ d = 0 ∧ h = 0 ∧ mi = 0 ∧ s = 0 ∧ us = 0 then [byte 0]
    else if h = 0 ∧ mi = 0 ∧ s = 0 ∧ us = 0 then byte 4 :: leBytes 2 y ++ [byte mo, byte d]
    else if us = 0 then byte 7 :: leBytes 2 y ++ [byte mo, byte d, byte h, byte mi, byte s]
    else byte 11 :: leBytes 2 y ++ [byte mo, byte d, byte h, byte mi, byte s] ++ leBytes 4 us
  | .time neg d h mi s us =>
    if d = 0 ∧ h = 0 ∧ mi = 0 ∧ s = 0 ∧ us = 0 then [byte 0]
    else if us = 0 then
      byte 8 :: byte (if neg then 1 else 0) :: leBytes 4 d ++ [byte h, byte mi, byte s]
    else
      byte 12 :: byte (if neg then 1 else 0) :: leBytes 4 d ++ [byte h, byte mi, byte s]
        ++ leBytes 4 us

/-! ## Column types -/

open constants.ColumnType in
/-- The column types whose binary values are length-encoded strings (decoded as `Bytes`). -/
def isLenencStrType : constants.ColumnType → Bool
  | MYSQL_TYPE_STRING | MYSQL_TYPE_VAR_STRING | MYSQL_TYPE_BLOB | MYSQL_TYPE_TINY_BLOB
  | MYSQL_TYPE_MEDIUM_BLOB | MYSQL_TYPE_LONG_BLOB | MYSQL_TYPE_SET | MYSQL_TYPE_ENUM
  | MYSQL_TYPE_DECIMAL | MYSQL_TYPE_VARCHAR | MYSQL_TYPE_BIT | MYSQL_TYPE_NEWDECIMAL
  | MYSQL_TYPE_GEOMETRY | MYSQL_TYPE_VECTOR | MYSQL_TYPE_JSON => true
  | _ => false

open constants.ColumnType in
/-- The column types the crate's binary decoder supports. The other five (`TIMESTAMP2`,
    `DATETIME2`, `TIME2`, `TYPED_ARRAY`, `UNKNOWN`) are internal server types that do not appear in
    binary result sets, and the decoder panics on them (`unimplemented!`): a column definition
    from the server naming one of them crashes the client. -/
def binSupported : constants.ColumnType → Bool
  | MYSQL_TYPE_TIMESTAMP2 | MYSQL_TYPE_DATETIME2 | MYSQL_TYPE_TIME2 | MYSQL_TYPE_TYPED_ARRAY
  | MYSQL_TYPE_UNKNOWN => false
  | _ => true

/-- Whether the column flags have `UNSIGNED_FLAG` (bit 5, value 32). -/
def isUnsigned (flags : constants.ColumnFlags) : Bool := flags.val.testBit 5

/-! ## Binary decoding -/

/-- Reads a `k`-byte little-endian integer as an `Int` value: unsigned, or two's complement.
    On a short input: `none`, input unchanged. -/
def readIntVal (k : Nat) (unsigned : Bool) (bs : List U8) : Option Val × List U8 :=
  match readLE k bs with
  | none => (none, bs)
  | some (n, rest) => (some (.int (if unsigned then n else toSigned (8 * k) n)), rest)

/-- Binary DATE/DATETIME/TIMESTAMP. A length byte `len`, then `len` bytes. The protocol defines
    `len` = 0 (all fields 0), 4 (year as 2 bytes, month, day), 7 (also hour, minute, second) and
    11 (also microseconds as 4 bytes).
    **Crate behaviour on other lengths** (not defined by the protocol): it reads the fields of the
    largest of 0, 4, 7 that is at most `len`, reads microseconds only if `len = 11`, and skips the
    remaining bytes of the `len`; e.g. `len = 12` gives a value without microseconds.
    `none` if the input is empty (nothing consumed) or has fewer than `len` bytes after the length
    byte (the length byte consumed). -/
def dateRead : List U8 → Option Val × List U8
  | [] => (none, [])
  | l :: rest =>
    if rest.length < l.val then (none, rest) else
    let p := rest.take l.val
    let b (i : Nat) : Nat := (p.getD i (byte 0)).val
    let v : Val :=
      if l.val < 4 then .date 0 0 0 0 0 0 0
      else if l.val < 7 then .date (b 0 + 256 * b 1) (b 2) (b 3) 0 0 0 0
      else if l.val ≠ 11 then .date (b 0 + 256 * b 1) (b 2) (b 3) (b 4) (b 5) (b 6) 0
      else .date (b 0 + 256 * b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (leNat ((p.drop 7).take 4))
    (some v, rest.drop l.val)

/-- Binary TIME. A length byte `len`, then `len` bytes. The protocol defines `len` = 0 (all fields
    0, positive), 8 (sign byte, days as 4 bytes, hours, minutes, seconds) and 12 (also
    microseconds as 4 bytes).
    **Crate behaviour on input the protocol does not define**: lengths 1–7 give the zero time,
    9–11 and 13–255 a time without microseconds, the rest of the `len` bytes skipped; a sign byte
    other than 0 or 1 means positive.
    `none` as for `dateRead`. -/
def timeRead : List U8 → Option Val × List U8
  | [] => (none, [])
  | l :: rest =>
    if rest.length < l.val then (none, rest) else
    let p := rest.take l.val
    let b (i : Nat) : Nat := (p.getD i (byte 0)).val
    let v : Val :=
      if l.val < 8 then .time false 0 0 0 0 0
      else if l.val ≠ 12 then
        .time (b 0 = 1) (leNat ((p.drop 1).take 4)) (b 5) (b 6) (b 7) 0
      else .time (b 0 = 1) (leNat ((p.drop 1).take 4)) (b 5) (b 6) (b 7) (leNat ((p.drop 8).take 4))
    (some v, rest.drop l.val)

open constants.ColumnType in
/-- The crate's binary-protocol decoder for one value of a column of type `ct` (with `unsigned`
    = the column's `UNSIGNED_FLAG`), with what it leaves of the input.
    * String types: a length-encoded string, read by `checkedLenencStr` (so the crate's lenenc
      quirk applies: a value starting with `0xFB` or `0xFF` decodes as the empty string).
    * Integer types: `Int` of the signed or unsigned value, except an unsigned LONGLONG above
      `i64::MAX`, which is `UInt`.
    * Floats: the bit pattern.
    * Temporal types: `dateRead`, `timeRead`.
    * NULL: the null value, nothing consumed.
    Unsupported types (`binSupported`) are not described: the decoder panics on them. -/
def binRead (ct : constants.ColumnType) (unsigned : Bool) (bs : List U8) : Option Val × List U8 :=
  if isLenencStrType ct then
    match checkedLenencStr bs with
    | (some s, rest) => (some (.bytes s), rest)
    | (none, rest) => (none, rest)
  else match ct with
  | MYSQL_TYPE_TINY => readIntVal 1 unsigned bs
  | MYSQL_TYPE_SHORT | MYSQL_TYPE_YEAR => readIntVal 2 unsigned bs
  | MYSQL_TYPE_LONG | MYSQL_TYPE_INT24 => readIntVal 4 unsigned bs
  | MYSQL_TYPE_LONGLONG =>
    match readLE 8 bs with
    | none => (none, bs)
    | some (n, rest) =>
      (some (if ¬unsigned then .int (toSigned 64 n) else if n < 2 ^ 63 then .int n else .uint n),
        rest)
  | MYSQL_TYPE_FLOAT =>
    match readLE 4 bs with
    | none => (none, bs)
    | some (n, rest) => (some (.float n), rest)
  | MYSQL_TYPE_DOUBLE =>
    match readLE 8 bs with
    | none => (none, bs)
    | some (n, rest) => (some (.double n), rest)
  | MYSQL_TYPE_TIMESTAMP | MYSQL_TYPE_DATE | MYSQL_TYPE_NEWDATE | MYSQL_TYPE_DATETIME => dateRead bs
  | MYSQL_TYPE_TIME => timeRead bs
  | MYSQL_TYPE_NULL => (some .null, bs)
  | _ => (none, bs)

/-! ## Round trip: which column types fit a value, and what comes back -/

open constants.ColumnType in
/-- The column types at which the binary encoding of `v` is meant to be decoded: `NULL` at NULL,
    `Bytes` at a string type, `Int` and `UInt` at LONGLONG (the encoding is always 8 bytes),
    `Float` at FLOAT, `Double` at DOUBLE, `Date` at DATE/DATETIME/TIMESTAMP/NEWDATE, `Time` at
    TIME. -/
def binCompatible : Val → constants.ColumnType → Prop
  | .null, ct => ct = MYSQL_TYPE_NULL
  | .bytes _, ct => isLenencStrType ct = true
  | .int _, ct => ct = MYSQL_TYPE_LONGLONG
  | .uint _, ct => ct = MYSQL_TYPE_LONGLONG
  | .float _, ct => ct = MYSQL_TYPE_FLOAT
  | .double _, ct => ct = MYSQL_TYPE_DOUBLE
  | .date .., ct =>
    ct = MYSQL_TYPE_DATE ∨ ct = MYSQL_TYPE_DATETIME ∨ ct = MYSQL_TYPE_TIMESTAMP
      ∨ ct = MYSQL_TYPE_NEWDATE
  | .time .., ct => ct = MYSQL_TYPE_TIME

/-- What binary decoding gives back for an encoded value, at a compatible column with the given
    `UNSIGNED_FLAG`. Everything comes back unchanged except:
    * an 8-byte integer is reinterpreted by the column's signedness: at an unsigned column, values
      `≤ i64::MAX` come back as `Int` and the others as `UInt` (so `Int x` with `x < 0` comes back as
      `UInt (x + 2^64)`); at a signed column, everything comes back as `Int` (so `UInt x` with
      `x > i64::MAX` comes back as `Int (x - 2^64)`);
    * a zero TIME is sent without its sign, so a negative zero time comes back positive. -/
def binNorm (unsigned : Bool) : Val → Val
  | .int x =>
    if unsigned then (if 0 ≤ x then .int x else .uint (x + 2 ^ 64).toNat) else .int x
  | .uint x => if unsigned then (if x < 2 ^ 63 then .int x else .uint x) else .int (toSigned 64 x)
  | .time _ 0 0 0 0 0 => .time false 0 0 0 0 0
  | v => v

/-! ## Text decoding -/

/-- The crate's text-protocol decoder for one value of a row, with what it leaves of the input: a
    `0xFB` byte is `NULL`; anything else is a length-encoded string, read by `checkedLenencStr` (so
    a value starting with `0xFF` -- an ERR packet header, not a value -- decodes as the empty
    string). `none` on an empty input (nothing consumed) or a malformed string. -/
def textRead : List U8 → Option Val × List U8
  | [] => (none, [])
  | b :: rest =>
    if b.val = 0xFB then (some .null, rest)
    else match checkedLenencStr (b :: rest) with
      | (some s, rest') => (some (.bytes s), rest')
      | (none, rest') => (none, rest')

end Defs
