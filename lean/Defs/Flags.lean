import Defs.Bytes

/-!
# Column types and flag words

The numeric codes of the column types and the flag bits that the protocol defines, from the MySQL
source (`include/field_types.h` `enum_field_types`, `include/mysql_com.h`) and the protocol pages
<https://dev.mysql.com/doc/dev/mysql-server/latest/group__group__cs__capabilities__flags.html>,
<https://dev.mysql.com/doc/dev/mysql-server/latest/mysql__com_8h.html> (server status and column
definition flags).

Flag words are plain numbers here: a set of flags is the number with those bits set, and the set
operations are the bitwise operations on `Nat` (`&&&`, `|||`, `^^^`).
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ## Column types (`enum_field_types`) -/

open constants.ColumnType in
/-- The protocol code of a column type (the `type` byte of a column definition, and of a
    `COM_STMT_EXECUTE` parameter type). `MYSQL_TYPE_UNKNOWN` is the crate's name for MySQL's
    `MYSQL_TYPE_INVALID` (243). MySQL's `MYSQL_TYPE_BOOL` (244, documented as "currently just a
    placeholder") has no crate counterpart. -/
def columnTypeCode : constants.ColumnType → Nat
  | MYSQL_TYPE_DECIMAL => 0
  | MYSQL_TYPE_TINY => 1
  | MYSQL_TYPE_SHORT => 2
  | MYSQL_TYPE_LONG => 3
  | MYSQL_TYPE_FLOAT => 4
  | MYSQL_TYPE_DOUBLE => 5
  | MYSQL_TYPE_NULL => 6
  | MYSQL_TYPE_TIMESTAMP => 7
  | MYSQL_TYPE_LONGLONG => 8
  | MYSQL_TYPE_INT24 => 9
  | MYSQL_TYPE_DATE => 10
  | MYSQL_TYPE_TIME => 11
  | MYSQL_TYPE_DATETIME => 12
  | MYSQL_TYPE_YEAR => 13
  | MYSQL_TYPE_NEWDATE => 14
  | MYSQL_TYPE_VARCHAR => 15
  | MYSQL_TYPE_BIT => 16
  | MYSQL_TYPE_TIMESTAMP2 => 17
  | MYSQL_TYPE_DATETIME2 => 18
  | MYSQL_TYPE_TIME2 => 19
  | MYSQL_TYPE_TYPED_ARRAY => 20
  | MYSQL_TYPE_VECTOR => 242
  | MYSQL_TYPE_UNKNOWN => 243
  | MYSQL_TYPE_JSON => 245
  | MYSQL_TYPE_NEWDECIMAL => 246
  | MYSQL_TYPE_ENUM => 247
  | MYSQL_TYPE_SET => 248
  | MYSQL_TYPE_TINY_BLOB => 249
  | MYSQL_TYPE_MEDIUM_BLOB => 250
  | MYSQL_TYPE_LONG_BLOB => 251
  | MYSQL_TYPE_BLOB => 252
  | MYSQL_TYPE_VAR_STRING => 253
  | MYSQL_TYPE_STRING => 254
  | MYSQL_TYPE_GEOMETRY => 255

open constants.ColumnType in
/-- Every column type. -/
def allColumnTypes : List constants.ColumnType :=
  [MYSQL_TYPE_DECIMAL, MYSQL_TYPE_TINY, MYSQL_TYPE_SHORT, MYSQL_TYPE_LONG, MYSQL_TYPE_FLOAT,
   MYSQL_TYPE_DOUBLE, MYSQL_TYPE_NULL, MYSQL_TYPE_TIMESTAMP, MYSQL_TYPE_LONGLONG, MYSQL_TYPE_INT24,
   MYSQL_TYPE_DATE, MYSQL_TYPE_TIME, MYSQL_TYPE_DATETIME, MYSQL_TYPE_YEAR, MYSQL_TYPE_NEWDATE,
   MYSQL_TYPE_VARCHAR, MYSQL_TYPE_BIT, MYSQL_TYPE_TIMESTAMP2, MYSQL_TYPE_DATETIME2, MYSQL_TYPE_TIME2,
   MYSQL_TYPE_TYPED_ARRAY, MYSQL_TYPE_VECTOR, MYSQL_TYPE_UNKNOWN, MYSQL_TYPE_JSON,
   MYSQL_TYPE_NEWDECIMAL, MYSQL_TYPE_ENUM, MYSQL_TYPE_SET, MYSQL_TYPE_TINY_BLOB,
   MYSQL_TYPE_MEDIUM_BLOB, MYSQL_TYPE_LONG_BLOB, MYSQL_TYPE_BLOB, MYSQL_TYPE_VAR_STRING,
   MYSQL_TYPE_STRING, MYSQL_TYPE_GEOMETRY]

/-- The column type with code `n`, if any (codes 21–241 and 244 have none). -/
def columnTypeOfCode (n : Nat) : Option constants.ColumnType :=
  allColumnTypes.find? (fun ct => columnTypeCode ct = n)

/-! ## Flag words -/

/-- Whether the flag word `flags` has all the bits of `bit`. -/
def hasFlag (flags bit : Nat) : Bool := flags &&& bit = bit

/-- The bits of `x` that are not bits of `y`, for `w`-bit words (`x & !y`). -/
def andNot (w x y : Nat) : Nat := x &&& (2 ^ w - 1 - y % 2 ^ w)

/-- The bits of the `w`-bit word `x` flipped (`!x`). -/
def complementBits (w x : Nat) : Nat := 2 ^ w - 1 - x % 2 ^ w

/-- The server status flags (`SERVER_STATUS_*`, `u16`) the crate knows: `IN_TRANS` (1),
    `AUTOCOMMIT` (2), `MORE_RESULTS_EXISTS` (8), `NO_GOOD_INDEX_USED` (16), `NO_INDEX_USED` (32),
    `CURSOR_EXISTS` (64), `LAST_ROW_SENT` (128), `DB_DROPPED` (256), `NO_BACKSLASH_ESCAPES` (512),
    `METADATA_CHANGED` (1024), `QUERY_WAS_SLOW` (2048), `PS_OUT_PARAMS` (4096),
    `IN_TRANS_READONLY` (8192), `SESSION_STATE_CHANGED` (16384), and bit 15 (32768, MariaDB's
    `ANSI_QUOTES`). Bit 2 (value 4) is unassigned in MySQL and unknown to the crate. -/
def statusFlagsAll : Nat := 0xFFFB

/-- The capability flags (`CLIENT_*`, `u32`): the crate names all 32 bits. -/
def capabilityFlagsAll : Nat := 2 ^ 32 - 1

/-- The column definition flags (`*_FLAG`, `u16`): the crate names all 16 bits. -/
def columnFlagsAll : Nat := 2 ^ 16 - 1

/-- `CLIENT_PROTOCOL_41` (bit 9). -/
def CLIENT_PROTOCOL_41 : Nat := 512

/-- `CLIENT_SESSION_TRACK` (bit 23). -/
def CLIENT_SESSION_TRACK : Nat := 2 ^ 23

/-- `CLIENT_PROGRESS_OBSOLETE` (bit 29; MariaDB's `CLIENT_PROGRESS`). -/
def CLIENT_PROGRESS_OBSOLETE : Nat := 2 ^ 29

/-- `SERVER_SESSION_STATE_CHANGED` (bit 14). -/
def SERVER_SESSION_STATE_CHANGED : Nat := 2 ^ 14

end Defs
