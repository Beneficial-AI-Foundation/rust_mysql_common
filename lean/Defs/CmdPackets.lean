import Defs.Packets
import Defs.Convert
import Defs.VarLen

/-!
# Prepared-statement command packets (`COM_STMT_PREPARE` OK, `COM_STMT_SEND_LONG_DATA`,
  `COM_STMT_CLOSE`, MariaDB's `COM_STMT_BULK_EXECUTE`)

From the protocol pages:

* `COM_STMT_PREPARE_OK`
  (<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_com_stmt_prepare.html>):
  `status` `0x00`, `statement_id` (4 bytes), `num_columns` (2), `num_params` (2),
  `reserved_1` (1, `0x00`), `warning_count` (2; "if packet length > 12", always sent by current
  servers), then, with `CLIENT_OPTIONAL_RESULTSET_METADATA`, `metadata_follows` (1).
* `COM_STMT_SEND_LONG_DATA`
  (<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_com_stmt_send_long_data.html>):
  `0x18`, `statement_id` (4), `param_id` (2), `data` (the rest of the packet).
* `COM_STMT_CLOSE`
  (<https://dev.mysql.com/doc/dev/mysql-server/latest/page_protocol_com_stmt_close.html>):
  `0x19`, `statement_id` (4).
* MariaDB `COM_STMT_BULK_EXECUTE`
  (<https://mariadb.com/kb/en/com_stmt_bulk_execute/>): `0xFA`, `statement_id` (4),
  `bulk_flags` (2: `SEND_UNIT_RESULTS` = 64, `SEND_TYPES_TO_SERVER` = 128); if
  `SEND_TYPES_TO_SERVER`, for each parameter its type (1 byte) and a flag byte (128 = unsigned);
  then, for each row and each parameter of the row, an indicator byte (`NONE` 0, `NULL` 1,
  `DEFAULT` 2, `IGNORE` 3) followed, **only for `NONE`**, by the value in the binary protocol
  encoding.

All integers are little-endian.

This file also holds `ReadOut`, the result type of the readers below that may panic or that the
model cannot fully determine, and `LossyUtf8Valid`, the statement form of the lossy `*_str`
accessors.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

/-! ## Reader outcomes, lossy strings -/

/-- What a reader does with an input:
    * `done r rest`: it returns, with the result (`none` for an error) and what is left of the
      input;
    * `panic e`: it panics (`e` is the Aeneas label of the panic);
    * `unknown`: the translation does not determine it (meant for where the crate reaches an
      Aeneas-library function without a model). Since translation-patches/156 no reader of
      these files gives it (the `*_ne_unknown` lemmas); the readers only pass it on. -/
inductive ReadOut (α : Type) where
  | done (r : Option α) (rest : List U8)
  | panic (e : Error)
  | unknown

/-- The bytes of a `Cow<str>`: a borrowed `&str` is its bytes (`Str = Slice U8`), an owned
    `String` its UTF-8 encoding. -/
def strCowBytes : alloc.borrow.Cow Str String → List U8
  | .Borrowed s => s.val
  | .Owned s => utf8 s

/-- `c` is what `String::from_utf8_lossy(bs)` returns, as far as the trusted model determines it:
    if `bs` is valid UTF-8 (`IsUtf8`), the borrowed `bs` itself. (Otherwise std replaces invalid
    sequences by U+FFFD, which the trusted model leaves opaque.) -/
def LossyUtf8Valid (bs : List U8) (c : alloc.borrow.Cow Str String) : Prop :=
  IsUtf8 bs → ∃ s : Str, c = .Borrowed s ∧ s.val = bs

/-! ## `COM_STMT_PREPARE_OK` -/

/-- The fields of a `COM_STMT_PREPARE_OK` packet, as the specs describe it. -/
structure StmtOk where
  stmtId : Nat
  numColumns : Nat
  numParams : Nat
  warnings : Nat
deriving DecidableEq

/-- The `StmtOk` of a `StmtPacket`. -/
def StmtOk.of (p : packets.StmtPacket) : StmtOk :=
  ⟨p.statement_id.1.val, p.num_columns.1.val, p.num_params.1.val, p.warning_count.1.val⟩

/-- The protocol's `COM_STMT_PREPARE_OK` (its first 12 bytes; without `metadata_follows`). -/
def stmtOkEnc (s : StmtOk) : List U8 :=
  byte 0 :: leBytes 4 s.stmtId ++ leBytes 2 s.numColumns ++ leBytes 2 s.numParams ++ [byte 0]
    ++ leBytes 2 s.warnings

/-- The crate's reader of a `COM_STMT_PREPARE_OK` packet (`StmtPacket::deserialize`): 12 bytes
    (`none`, nothing consumed, if fewer), consumed whatever they hold; `none` if the status byte
    is not `0x00`. **Crate behaviour**: `reserved_1` is not checked; bytes after the 12 (such as
    `metadata_follows`) are left unread; a packet without `warning_count` (10 bytes, allowed by
    the protocol page) is rejected. -/
def stmtOkRead (bs : List U8) : Option StmtOk × List U8 :=
  if bs.length < 12 then (none, bs)
  else
    let f := bs.take 12
    (if (f.getD 0 (byte 0)).val = 0 then
      some ⟨leNat ((f.drop 1).take 4), leNat ((f.drop 5).take 2), leNat ((f.drop 7).take 2),
        leNat ((f.drop 10).take 2)⟩
     else none, bs.drop 12)

/-! ## `COM_STMT_SEND_LONG_DATA`, `COM_STMT_CLOSE` -/

/-- The protocol's `COM_STMT_SEND_LONG_DATA`. -/
def sendLongDataEnc (stmtId paramId : Nat) (data : List U8) : List U8 :=
  byte 0x18 :: leBytes 4 stmtId ++ leBytes 2 paramId ++ data

/-- The protocol's `COM_STMT_CLOSE`. -/
def stmtCloseEnc (stmtId : Nat) : List U8 := byte 0x19 :: leBytes 4 stmtId

/-! ## `COM_STMT_BULK_EXECUTE` -/

/-- `SEND_UNIT_RESULTS`. -/
def SEND_UNIT_RESULTS : Nat := 64

/-- `SEND_TYPES_TO_SERVER`. -/
def SEND_TYPES_TO_SERVER : Nat := 128

/-- The code of a MariaDB bulk indicator: `NONE` 0, `NULL` 1, `DEFAULT` 2, `IGNORE` 3. -/
def bulkIndicatorCode : constants.MariadbBulkIndicator → Nat
  | .BULK_INDICATOR_NONE => 0
  | .BULK_INDICATOR_NULL => 1
  | .BULK_INDICATOR_DEFAULT => 2
  | .BULK_INDICATOR_IGNORE => 3

/-- The indicator the crate sends with a value: `NULL` (1) for `NULL`, else `NONE` (0). -/
def bulkInd (v : Val) : Nat := match v with | .null => 1 | _ => 0

open constants.ColumnType in
/-- The type sent for a parameter value, as (type code, flag byte): the crate's choice, the same
    as for `COM_STMT_EXECUTE` (`paramType`): `NULL` as `MYSQL_TYPE_NULL`, `Bytes` as
    `MYSQL_TYPE_VAR_STRING`, `Int` as signed and `UInt` as unsigned (flag 128)
    `MYSQL_TYPE_LONGLONG`, `Float` as `MYSQL_TYPE_FLOAT`, `Double` as `MYSQL_TYPE_DOUBLE`, `Date`
    as `MYSQL_TYPE_DATETIME`, `Time` as `MYSQL_TYPE_TIME`. -/
def bulkTy : Val → Nat × Nat
  | .null => (columnTypeCode MYSQL_TYPE_NULL, 0)
  | .bytes _ => (columnTypeCode MYSQL_TYPE_VAR_STRING, 0)
  | .int _ => (columnTypeCode MYSQL_TYPE_LONGLONG, 0)
  | .uint _ => (columnTypeCode MYSQL_TYPE_LONGLONG, 128)
  | .float _ => (columnTypeCode MYSQL_TYPE_FLOAT, 0)
  | .double _ => (columnTypeCode MYSQL_TYPE_DOUBLE, 0)
  | .date .. => (columnTypeCode MYSQL_TYPE_DATETIME, 0)
  | .time .. => (columnTypeCode MYSQL_TYPE_TIME, 0)

open constants.ColumnType in
/-- Combines the type `l` chosen so far for a parameter with the type `r` of its value in another
    row (the crate's intent: "the type that covers param values in all rows; `MYSQL_TYPE_NULL` is a
    proper type only if all the values for the given param are NULLs"): a `NULL` type gives way to
    the other; for the same type the flags are united ("if flag is required by a single param
    value, then it must be given for the whole batch"). **Crate behaviour** for two different
    non-`NULL` types (a `TODO` in the source): the first is kept, and the server may reject the
    batch or misread the other values. -/
def bulkMerge (l r : Nat × Nat) : Nat × Nat :=
  if l = r then l
  else if l.1 = columnTypeCode MYSQL_TYPE_NULL then r
  else if l.1 = r.1 then (r.1, l.2 ||| r.2)
  else l

/-- The parameter types of a batch of rows (all of the same length): the first row's types,
    combined (`bulkMerge`) with each row's types in turn, from the first row on. -/
def bulkTypes : List (List Val) → List (Nat × Nat)
  | [] => []
  | r0 :: rs => (r0 :: rs).foldl (fun ts row => List.zipWith bulkMerge ts (row.map bulkTy))
      (r0.map bulkTy)

/-- A `COM_STMT_BULK_EXECUTE` request, as the specs describe it: the statement id, the flag word,
    the parameter types as (type code, flag byte), and the values of all rows in row-major order,
    each with its indicator code. -/
structure BulkReq where
  stmtId : Nat
  flags : Nat
  types : List (Nat × Nat)
  values : List (Nat × Val)

/-- The `BulkReq` of a `ComStmtBulkExecuteRequest`. -/
def BulkReq.of (q : packets.ComStmtBulkExecuteRequest) : BulkReq :=
  ⟨q.stmt_id.1.val, q.bulk_flags.1.val,
   (cowList q.types.1).map (fun t => (columnTypeCode t.type.1, t.flags.1.val)),
   q.values.values.val.map (fun v => (bulkIndicatorCode v.indicator.1, Val.ofValue v.value))⟩

/-- The request the crate builds from a batch of rows (`ComStmtBulkExecuteRequest::new`): the
    types (`bulkTypes`) only if the flags have `SEND_TYPES_TO_SERVER`, and every value with its
    indicator (`bulkInd`). -/
def bulkNew (stmtId flags : Nat) (rows : List (List Val)) : BulkReq :=
  ⟨stmtId, flags, if hasFlag flags SEND_TYPES_TO_SERVER then bulkTypes rows else [],
   rows.flatten.map (fun v => (bulkInd v, v))⟩

/-- One parameter type on the wire: the type code and the flag byte. -/
def bulkTypeEnc (t : Nat × Nat) : List U8 := [byte t.1, byte t.2]

/-- One value on the wire: the indicator, then the binary encoding of the value (nothing for
    `NULL`). For the indicators the crate itself produces (`bulkInd`) this is the protocol's
    layout. **Crate behaviour**: with a `DEFAULT` or `IGNORE` indicator the value is written
    too (the protocol has no value after them); such indicators only occur in a request read by
    the crate's own reader (`bulkValueRead`). -/
def bulkValueEnc (iv : Nat × Val) : List U8 := byte iv.1 :: binEnc iv.2

/-- The `COM_STMT_BULK_EXECUTE` packet of a request: header `0xFA`, statement id, flags, the
    types if the flags have `SEND_TYPES_TO_SERVER`, then the values. -/
def bulkReqEnc (q : BulkReq) : List U8 :=
  byte 0xFA :: leBytes 4 q.stmtId ++ leBytes 2 q.flags
    ++ (if hasFlag q.flags SEND_TYPES_TO_SERVER then q.types.flatMap bulkTypeEnc else [])
    ++ q.values.flatMap bulkValueEnc

/-- The number of bytes a row of values takes in a request: one indicator byte per value plus
    its binary encoding. -/
def bulkRowLen (row : List Val) : Nat := (row.map (fun v => 1 + (binEnc v).length)).sum


/-- The (indicator code, value) of a `StmtBulkExecuteParamValue`. -/
def bulkIV (v : packets.StmtBulkExecuteParamValue) : Nat × Val :=
  (bulkIndicatorCode v.indicator.1, Val.ofValue v.value)

/-- The parameters a bulk reader is given, as (column type, unsigned): only the `UNSIGNED_FLAG` of
    the column flags matters. -/
def bulkParams (ps : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags)) :
    List (constants.ColumnType × Bool) :=
  ps.val.map (fun p => (p.1, isUnsigned p.2))

/-- What `ComStmtBulkExecuteRequest::new` returns for a batch of rows: `NoParams` for no rows,
    `MixedArity` if a row's length differs from the first row's, else the request `bulkNew`. -/
inductive BulkNewOut where
  | noParams
  | mixedArity
  | ok (q : BulkReq)

/-- The outcome of `ComStmtBulkExecuteRequest::new stmtId flags rows`. -/
def bulkNewOut (stmtId flags : Nat) (rows : List (List Val)) : BulkNewOut :=
  match rows with
  | [] => .noParams
  | r0 :: _ =>
    if rows.all (fun r => r.length == r0.length) then .ok (bulkNew stmtId flags rows) else .mixedArity

/-- The Rust result `r` is the outcome `o`. -/
def BulkNewOut.Matches (o : BulkNewOut)
    (r : core.result.Result packets.ComStmtBulkExecuteRequest packets.BulkExecuteRequestError) :
    Prop :=
  match o with
  | .noParams => r = .Err .NoParams
  | .mixedArity => r = .Err .MixedArity
  | .ok q => ∃ x, r = .Ok x ∧ BulkReq.of x = q

/-! ## The bulk request builder -/

/-- A `ComStmtBulkExecuteRequestBuilder`, as the specs describe it. -/
structure BulkBuilder where
  stmtId : Nat
  withTypes : Bool
  withResults : Bool
  rows : List (List value.Value)
  payloadLen : Nat
  arity : Option Nat
  namedParams : Option (Slice (alloc.vec.Vec U8))
  maxPayloadLen : Nat

/-- The `BulkBuilder` of a `ComStmtBulkExecuteRequestBuilder`. -/
def BulkBuilder.of (b : packets.ComStmtBulkExecuteRequestBuilder) : BulkBuilder :=
  ⟨b.stmt_id.val, b.with_types, b.with_results, b.params_set.val.map (·.val), b.payload_len.val,
   b.arity.map (·.val), b.named_params, b.max_payload_len.val⟩

/-- The flag word `build` sends: `SEND_UNIT_RESULTS` if `with_results`, `SEND_TYPES_TO_SERVER` if
    the types are still to be sent (only in the first request of a builder). -/
def BulkBuilder.flags (b : BulkBuilder) : Nat :=
  (if b.withResults then SEND_UNIT_RESULTS else 0) ||| (if b.withTypes then SEND_TYPES_TO_SERVER else 0)

/-- What `add_row` returns: the row was added (`Ok(None)`); it would make the request too large
    and is handed back (`Ok(Some(row))`); it alone is too large (`RowTooLarge`); or its length
    differs from the builder's arity (`MixedArity`). -/
inductive AddRowOut where
  | added
  | full
  | tooLarge
  | mixedArity

/-- The crate's `add_row`, on the builder's fields: the arity is fixed by the first row offered;
    a row of another length is rejected. The size of the request so far (`payloadLen`, without
    the 7 header bytes) starts at `2 * arity` (the types) while the types are still to be sent;
    a row adds `bulkRowLen`. A row is added if the request stays within `maxPayloadLen`
    (`max_allowed_packet - 4`), handed back if not (`tooLarge` if the builder has no rows). -/
def bulkAddRow (b : BulkBuilder) (row : List value.Value) : AddRowOut × BulkBuilder :=
  let ar := b.arity.getD row.length
  let b1 := { b with arity := some ar }
  if row.length ≠ ar then (.mixedArity, b1)
  else
    let pl := if b.withTypes ∧ b.payloadLen = 0 then 2 * row.length else b.payloadLen
    let dl := bulkRowLen (row.map Val.ofValue)
    if b.maxPayloadLen < 7 + pl + dl then
      (if b.rows = [] then .tooLarge else .full, { b1 with payloadLen := pl })
    else (.added, { b1 with rows := b.rows ++ [row], payloadLen := pl + dl })

/-- The Rust result of `add_row` is the outcome `o` (for the row `row`). -/
def AddRowOut.Matches (o : AddRowOut) (row : alloc.vec.Vec value.Value)
    (r : core.result.Result (Option (alloc.vec.Vec value.Value))
      packets.BulkExecuteRequestBuilderError) : Prop :=
  match o with
  | .added => r = .Ok none
  | .full => r = .Ok (some row)
  | .tooLarge => r = .Err (.Request (.RowTooLarge row))
  | .mixedArity => r = .Err (.Request .MixedArity)

/-- The builder's bookkeeping is right: every row has the arity, `payloadLen` is the size of the
    request `build` would make (without the 7 header bytes), and with rows that request fits in
    `maxPayloadLen`. Holds for a new builder and is kept by `add_row` and `build`
    (`Defs.bulkAddRow_inv`). -/
def BulkBuilder.Inv (b : BulkBuilder) : Prop :=
  (∀ row ∈ b.rows, some row.length = b.arity) ∧
  b.payloadLen = (if b.withTypes then 2 * b.arity.getD 0 else 0)
    + (b.rows.map (fun r => bulkRowLen (r.map Val.ofValue))).sum ∧
  (b.rows ≠ [] → 7 + b.payloadLen ≤ b.maxPayloadLen)

/-- The crate's reader of one parameter type (`StmtBulkExecuteParamType::deserialize`): a type
    byte (`none` on an empty input; `none`, the byte consumed, if it is not a known type code),
    then a flag byte (the same, if it is neither 0 nor 128). -/
def bulkTypeRead : List U8 → Option (Nat × Nat) × List U8
  | [] => (none, [])
  | t :: rest =>
    if (columnTypeOfCode t.val).isNone then (none, rest)
    else match rest with
      | [] => (none, [])
      | f :: rest' => if f.val = 0 ∨ f.val = 128 then (some (t.val, f.val), rest') else (none, rest')

/-- The crate's reader of `n` parameter types within the request reader: each type is read from
    its own 3-byte group (**crate bug**: `StmtBulkExecuteParamType::SIZE` is `Some(3)`, but a type
    is 2 bytes on the wire, so the reader consumes 3 bytes per type), `none` at the first group
    `bulkTypeRead` rejects. -/
def bulkTypesRead : Nat → List U8 → Option (List (Nat × Nat))
  | 0, _ => some []
  | n + 1, bs =>
    match (bulkTypeRead (bs.take 3)).1, bulkTypesRead n (bs.drop 3) with
    | some t, some ts => some (t :: ts)
    | _, _ => none

/-- The crate's reader of one value (`StmtBulkExecuteParamValue::deserialize`) for a parameter of
    column type `ct`, unsigned if `unsigned`: the indicator byte (`none` on an empty input;
    `none`, the byte consumed, if it is above 3); for `NULL` the value `NULL`; for any other
    indicator the binary value (`binRead`), **which panics** (`unimplemented!`) for the column
    types the binary reader does not support (`binSupported`). **Crate behaviour**: a value is
    read after `DEFAULT` and `IGNORE`, although the protocol sends none. -/
def bulkValueRead (ct : constants.ColumnType) (unsigned : Bool) :
    List U8 → ReadOut (Nat × Val)
  | [] => .done none []
  | b :: rest =>
    if 3 < b.val then .done none rest
    else if b.val = 1 then .done (some (1, .null)) rest
    else if binSupported ct then
      match binRead ct unsigned rest with
      | (some v, rest') => .done (some (b.val, v)) rest'
      | (none, rest') => .done none rest'
    else .panic .panic

/-- The crate's reader of one row of values (`StmtBulkExecuteParamValues::deserialize`), one per
    parameter (type, unsigned), stopping at the first failure. -/
def bulkValuesRead : List (constants.ColumnType × Bool) → List U8 → ReadOut (List (Nat × Val))
  | [], bs => .done (some []) bs
  | (ct, u) :: ps, bs =>
    match bulkValueRead ct u bs with
    | .done (some v) rest =>
      match bulkValuesRead ps rest with
      | .done (some vs) rest' => .done (some (v :: vs)) rest'
      | .done none rest' => .done none rest'
      | .panic e => .panic e
      | .unknown => .unknown
    | .done none rest => .done none rest
    | .panic e => .panic e
    | .unknown => .unknown

/-- The crate's reader of a `COM_STMT_BULK_EXECUTE` request (`ComStmtBulkExecuteRequest::
    deserialize`) with the parameters `params` (column type, unsigned) the caller knows:
    * the header byte (`none` on an empty input; `none`, the byte consumed, if not `0xFA`);
    * the statement id, 4 bytes, then the flags, 2 bytes (each: `none`, nothing more consumed,
      if fewer); `none`, the 2 bytes consumed, if the flags have bits other than 64 and 128;
    * with `SEND_TYPES_TO_SERVER`: `3 * params.length` bytes (`none`, nothing more consumed, if
      fewer), consumed whatever they hold, read by `bulkTypesRead` (`none` if it rejects them);
      the parameters then take the types read (and their unsigned flag);
    * **one** row of values (`bulkValuesRead`).
    **Crate bugs**: the 3-byte groups of `bulkTypesRead` misread the 2-byte types the protocol
    (and the crate's own serializer) sends, as soon as there is a parameter; only the first row
    of a batch is read, the other rows are left in the input. -/
def bulkReqRead (params : List (constants.ColumnType × Bool)) : List U8 → ReadOut BulkReq
  | [] => .done none []
  | h :: r =>
    if h.val ≠ 0xFA then .done none r
    else if r.length < 4 then .done none r
    else if r.length < 6 then .done none (r.drop 4)
    else
      let sid := leNat (r.take 4)
      let f := leNat ((r.drop 4).take 2)
      let r := r.drop 6
      if f &&& (SEND_UNIT_RESULTS ||| SEND_TYPES_TO_SERVER) ≠ f then .done none r
      else
        let finish (ts : List (Nat × Nat)) (ps : List (constants.ColumnType × Bool))
            (bs : List U8) : ReadOut BulkReq :=
          match bulkValuesRead ps bs with
          | .done (some vs) rest => .done (some ⟨sid, f, ts, vs⟩) rest
          | .done none rest => .done none rest
          | .panic e => .panic e
          | .unknown => .unknown
        if hasFlag f SEND_TYPES_TO_SERVER then
          let n := params.length
          if r.length < 3 * n then .done none r
          else
            match bulkTypesRead n (r.take (3 * n)) with
            | none => .done none (r.drop (3 * n))
            | some ts =>
              finish ts (ts.filterMap (fun t => (columnTypeOfCode t.1).map (fun ct => (ct, t.2 = 128))))
                (r.drop (3 * n))
        else finish [] params r

end Defs
