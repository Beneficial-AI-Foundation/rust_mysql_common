import Defs.Row
import Defs.Flags
import Defs.Framing

/-!
# `COM_STMT_EXECUTE`

From the protocol, <https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_com_stmt_execute.html>
(without `CLIENT_QUERY_ATTRIBUTES`, which the crate does not use here):

| field                   | bytes                                                        |
|-------------------------|--------------------------------------------------------------|
| status                  | `0x17` (`COM_STMT_EXECUTE`)                                  |
| statement id            | 4-byte little-endian                                         |
| flags                   | 1 byte (cursor type; `0x00` = `CURSOR_TYPE_NO_CURSOR`)       |
| iteration count         | 4-byte little-endian, always 1                               |
| if there are parameters:|                                                              |
| NULL bitmap             | `(num_params + 7) / 8` bytes, bit offset 0                   |
| new params bound flag   | 1 byte (1: types follow)                                     |
| parameter types         | 2 bytes per parameter: the type code, then `0x80` if unsigned, else `0x00` |
| parameter values        | the binary encoding of each non-NULL parameter                |

Values sent separately with `COM_STMT_SEND_LONG_DATA` are left out of the values.
The type sent for each `Value` variant is the crate's choice; it is listed in `paramType`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

open constants.ColumnType in
/-- The two type bytes sent for a parameter: `NULL` as `MYSQL_TYPE_NULL`, `Bytes` as
    `MYSQL_TYPE_VAR_STRING`, `Int` as signed and `UInt` as unsigned `MYSQL_TYPE_LONGLONG`, `Float`
    as `MYSQL_TYPE_FLOAT`, `Double` as `MYSQL_TYPE_DOUBLE`, `Date` as `MYSQL_TYPE_DATETIME`, `Time`
    as `MYSQL_TYPE_TIME`. The second byte is `0x80` for unsigned, else `0`. -/
def paramType : Val → List U8
  | .null => [byte (columnTypeCode MYSQL_TYPE_NULL), byte 0]
  | .bytes _ => [byte (columnTypeCode MYSQL_TYPE_VAR_STRING), byte 0]
  | .int _ => [byte (columnTypeCode MYSQL_TYPE_LONGLONG), byte 0]
  | .uint _ => [byte (columnTypeCode MYSQL_TYPE_LONGLONG), byte 0x80]
  | .float _ => [byte (columnTypeCode MYSQL_TYPE_FLOAT), byte 0]
  | .double _ => [byte (columnTypeCode MYSQL_TYPE_DOUBLE), byte 0]
  | .date .. => [byte (columnTypeCode MYSQL_TYPE_DATETIME), byte 0]
  | .time .. => [byte (columnTypeCode MYSQL_TYPE_TIME), byte 0]

/-- The value bytes sent for a parameter: its binary encoding (nothing for `NULL`), except that a
    `Bytes` value is left out when `longData` (it is sent with `COM_STMT_SEND_LONG_DATA`). -/
def paramValue (longData : Bool) : Val → List U8
  | .bytes s => if longData then [] else binEnc (.bytes s)
  | v => binEnc v

/-- A `COM_STMT_EXECUTE` packet with the given field values (`bitmap` is the NULL bitmap as
    sent): the layout of the table above. -/
def stmtExecuteBytes (stmtId cursor : Nat) (bitmap : List U8) (newParamsBound : Nat)
    (params : List Val) (longData : Bool) : List U8 :=
  byte 0x17 :: leBytes 4 stmtId ++ [byte cursor] ++ leBytes 4 1 ++
    (if params = [] then []
     else bitmap ++ [byte newParamsBound] ++ (params.map paramType).flatten
       ++ (params.map (paramValue longData)).flatten)

/-- The `COM_STMT_EXECUTE` packet for statement `stmtId` and parameters `params`: no cursor, the
    NULL bitmap of the parameters, new-params-bound flag 1. -/
def comStmtExecute (stmtId : Nat) (params : List Val) (longData : Bool) : List U8 :=
  stmtExecuteBytes stmtId 0 (nullBitmap 0 (params.map isNullVal)) 1 params longData

/-- The length the builder computes for the packet (`10 + bitmap + 1 + 2 * n + values`): the
    length of `comStmtExecute stmtId params false` when there are parameters. -/
def stmtExecuteLen (params : List Val) : Nat :=
  10 + nullBitmapLen 0 params.length + 1 + 2 * params.length + (params.map (fun v => (binEnc v).length)).sum

end Defs
