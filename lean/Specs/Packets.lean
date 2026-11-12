import Proofs.Packets.ColumnMeta
import Proofs.Packets.Column
import Proofs.Packets.OkPacketKind
import Proofs.Packets.OkPacket
import Proofs.Packets.OkPacketDeserializer
import Proofs.Packets.ProgressReport
import Proofs.Packets.ErrPacket
import Proofs.Packets.SqlState
import Proofs.Packets.ServerError
import Proofs.Packets.NullBitmap
import Proofs.Packets.ComStmtExecuteRequestBuilder
import Proofs.Packets.ComStmtExecuteRequest

/-!
# `src/packets/mod.rs`
    The packets of stages c–f: column definitions (`ColumnMeta`, `Column`), OK and EOF packets
    (`OkPacketKind` and its four kinds, `OkPacketBody`, `OkPacket`, `OkPacketDeserializer`), ERR
    packets (`ProgressReport`, `ErrPacket`, `SqlState`, `ServerError`), NULL bitmaps
    (`NullBitmap`) and `COM_STMT_EXECUTE` (`ComStmtExecuteRequestBuilder`,
    `ComStmtExecuteRequest`).

    **Patches.** 22 (combinators as `match`), 23 (`io_error_from`), 24 (`RawBytes` conversions),
    25 (`TryFrom<OkPacketBody>` through `non_empty`), 26–29 (`COM_STMT_EXECUTE`: owned bitmap, index
    loops, **`ComStmtExecuteRequest::params` is a `&[Value]` and `params()` returns `&[Value]`**
    instead of `&[&Value]`, serialization tail calls `serialize_params`), 31 (`BufMut` at
    `Vec<u8>`), 32. The statements are about the patched code.

    **Configuration.** As in `Specs/Io.lean`. Readers of length-encoded strings take `Target64`.

    **Allocation caveat.** As in `Specs/Row.lean`: "does not panic" assumes allocation succeeds.

    **Definitions used.** `Defs/Packets.lean` (`ColDef`, `metaFields`, `colDefEnc`,
    `colDefEncCrate`, `colDefRead`, `lenencStrs`, `OkBody`, `OkPkt`, `OkKind`, `okBodyRead`,
    `rsTerminatorBodyRead`, `eofBodyRead`, `okPacketRead`, `okPacketEnc`, `eofPacketEnc`,
    `statusRead`, `Progress`, `ErrPkt`, `progressEnc`, `progressRead`, `errPacketEnc`,
    `errPacketRead`, `serverErrorRead`, `sqlStateRead`, `errCompatible`), `Defs/NullBitmap.lean`,
    `Defs/StmtExecute.lean` (`stmtExecuteBytes`, `comStmtExecute`, `stmtExecuteLen`, `paramType`,
    `paramValue`), `Defs/Flags.lean`, `Defs/Value.lean`, `Defs/LenEnc.lean`, `Defs/Bytes.lean`.

    **Not covered.** `Column::new` and the `with_*` builders (they use `Arc::make_mut`, not
    translated), the `*_str` accessors (UTF-8 conversion), `SessionStateInfo` and
    `OkPacket::session_state_info` (later stage), `Display` impls, the other packets of the file
    (later stages), the private helpers `non_empty`, `byte_and_bit`, `serialize_params` (covered
    through their callers), `ComStmtExecuteRequestBuilder::NULL_BITMAP_OFFSET` (an unused
    constant, not in the translation). `ColumnMeta` is crate-private; it is stated because
    `Column` is built on it.

    **Behaviour to note (bugs first).**
    * **`ColumnMeta::catalog_ref` and `Column::catalog_ref` return the `schema` field.**
    * **`MySerialize for Column` writes `column_length` before `character_set`**, the reverse of
      the protocol and of the crate's own reader: a serialized column reads back silently with the
      wrong `character_set` (the low 16 bits of the length) and `column_length`
      (`colDefEncCrate` vs `colDefEnc`, `Defs.colDefRead_colDefEncCrate`).
    * The column reader does not check that the catalog is `def`.
    * The OK/EOF readers assume `CLIENT_PROTOCOL_41`, reject a status with bit 2 (value 4) set
      (a robustness quirk: current servers do not send it),
      and leave bytes after the fields they read unconsumed; without `CLIENT_SESSION_TRACK` a
      non-empty `info` must be a length-encoded string (it is `string<EOF>` on the protocol page;
      MySQL does send it length-encoded). `ResultSetTerminator` discards affected rows and last
      insert id.
    * With `CLIENT_PROTOCOL_41`, an ERR packet without the `#` SQL-state marker is an error.
    * The NULL bitmap of a `COM_STMT_EXECUTE` request is serialized truncated to 8192 bytes
      (`BareBytes<8192>`): with more than 65536 parameters the packet is malformed (MySQL allows at
      most 65535). `as_long_data` leaves the `Bytes` values out of the packet (they must be sent
      with `COM_STMT_SEND_LONG_DATA`); their type and NULL bits are still sent. With no parameters
      the builder's length is 11 for a 10-byte packet (only affects `as_long_data`, irrelevantly).
    * `comStmtExecute` is the protocol's packet only when `CLIENT_QUERY_ATTRIBUTES` was not
      negotiated or there are no parameters (with it, the server expects a `parameter_count` field and the crate's packet is
      misread); the crate does not look at the capabilities here.
    * `NullBitmap::is_null`/`set` panic (`assert!`) on a column index past the bitmap; `read`
      panics on a short input.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct ColumnMeta and its impls` -/

/-- `into_owned`: the same fields. -/
recall packets.ColumnMeta.into_owned_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.into_owned self ⦃ m => metaFields m = metaFields self ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ColumnMeta.into_owned_spec
/-- `catalog_ref`: **returns the `schema` field, not `catalog`** (`self.schema.as_bytes()`; a bug in the crate). -/
recall packets.ColumnMeta.catalog_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.catalog_ref self ⦃ s => s.val = cowList self.schema.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ColumnMeta.catalog_ref_spec
/-- `schema_ref`: the `schema` field. -/
recall packets.ColumnMeta.schema_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.schema_ref self ⦃ s => s.val = cowList self.schema.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ColumnMeta.schema_ref_spec
/-- `table_ref`: the `table` field. -/
recall packets.ColumnMeta.table_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.table_ref self ⦃ s => s.val = cowList self.table.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ColumnMeta.table_ref_spec
/-- `org_table_ref`: the `org_table` field. -/
recall packets.ColumnMeta.org_table_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.org_table_ref self ⦃ s => s.val = cowList self.org_table.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ColumnMeta.org_table_ref_spec
/-- `name_ref`: the `name` field. -/
recall packets.ColumnMeta.name_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.name_ref self ⦃ s => s.val = cowList self.«name».1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ColumnMeta.name_ref_spec
/-- `org_name_ref`: the `org_name` field. -/
recall packets.ColumnMeta.org_name_ref_spec (self : packets.ColumnMeta) :
    packets.ColumnMeta.org_name_ref self ⦃ s => s.val = cowList self.org_name.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ColumnMeta.org_name_ref_spec
/-- `MyDeserialize for ColumnMeta`: `SIZE` is `None`. -/
recall packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for ColumnMeta`: total; the six length-encoded strings (`lenencStrs 6`). -/
recall packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64) (buf : io.ParseBuf) :
    packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map metaFields, rest.val) = lenencStrs 6 buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ColumnMeta.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MySerialize for ColumnMeta`: appends the six fields as length-encoded strings. -/
recall packets.ColumnMeta.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ColumnMeta) (buf : alloc.vec.Vec U8)
    (h : buf.length + ((metaFields self).map lenencStr).flatten.length ≤ Usize.max) :
    packets.ColumnMeta.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ ((metaFields self).map lenencStr).flatten ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ColumnMeta.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `struct Column and its impls` -/

/-- `MyDeserialize for Column`: `SIZE` is `None`. -/
recall packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for Column`: total; `colDefRead` (six strings, then 13 bytes: `0x0c`, character set, column length, type, flags, decimals, filler). -/
recall packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64) (buf : io.ParseBuf) :
    packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map ColDef.ofColumn, rest.val) = colDefRead buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownColumnFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- Round trip: a column definition in the protocol layout (`colDefEnc`) is read back. -/
recall packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h64 : Target64) (c : packets.Column) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = colDefEnc (ColDef.ofColumn c) ++ tail) :
    packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map ColDef.ofColumn = some (ColDef.ofColumn c) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownColumnFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
/-- `MySerialize for Column`: appends `colDefEncCrate`, **which has `column_length` and `character_set` in the wrong order** (not `colDefEnc`, the protocol layout the reader expects): the crate's own reader reads it back **with no error but a wrong `character_set` and `column_length`** (`Defs.colDefRead_colDefEncCrate`). -/
recall packets.Column.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.Column) (buf : alloc.vec.Vec U8)
    (h : buf.length + (colDefEncCrate (ColDef.ofColumn self)).length ≤ Usize.max) :
    packets.Column.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ colDefEncCrate (ColDef.ofColumn self) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-- `column_length`: the field. -/
recall packets.Column.impl.column_length_eq (self : packets.Column) :
    packets.Column.impl.column_length self = ok self.column_length.1

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.impl.column_length_eq
/-- `column_type`: the field. -/
recall packets.Column.impl.column_type_eq (self : packets.Column) :
    packets.Column.impl.column_type self = ok self.column_type.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.impl.column_type_eq
/-- `character_set`: the field. -/
recall packets.Column.impl.character_set_eq (self : packets.Column) :
    packets.Column.impl.character_set self = ok self.character_set.1

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.impl.character_set_eq
/-- `flags`: the field. -/
recall packets.Column.impl.flags_eq (self : packets.Column) :
    packets.Column.impl.flags self = ok self.flags.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.impl.flags_eq
/-- `decimals`: the field. -/
recall packets.Column.impl.decimals_eq (self : packets.Column) :
    packets.Column.impl.decimals self = ok self.decimals.1

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.impl.decimals_eq
/-- `catalog_ref`: **returns the `schema` field, not `catalog`** (`self.schema.as_bytes()`; a bug in the crate). -/
recall packets.Column.catalog_ref_spec (self : packets.Column) :
    packets.Column.catalog_ref self ⦃ s => s.val = cowList self.«meta».schema.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.catalog_ref_spec
/-- `schema_ref`: the `schema` field. -/
recall packets.Column.schema_ref_spec (self : packets.Column) :
    packets.Column.schema_ref self ⦃ s => s.val = cowList self.«meta».schema.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.schema_ref_spec
/-- `table_ref`: the `table` field. -/
recall packets.Column.table_ref_spec (self : packets.Column) :
    packets.Column.table_ref self ⦃ s => s.val = cowList self.«meta».table.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.table_ref_spec
/-- `org_table_ref`: the `org_table` field. -/
recall packets.Column.org_table_ref_spec (self : packets.Column) :
    packets.Column.org_table_ref self ⦃ s => s.val = cowList self.«meta».org_table.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.org_table_ref_spec
/-- `name_ref`: the `name` field. -/
recall packets.Column.name_ref_spec (self : packets.Column) :
    packets.Column.name_ref self ⦃ s => s.val = cowList self.«meta».«name».1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.name_ref_spec
/-- `org_name_ref`: the `org_name` field. -/
recall packets.Column.org_name_ref_spec (self : packets.Column) :
    packets.Column.org_name_ref self ⦃ s => s.val = cowList self.«meta».org_name.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.org_name_ref_spec
/-! ### `trait OkPacketKind and its impls` -/

/-- `HEADER` is `0xFE`. -/
recall packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq :
    packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER = 254#u8

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq
/-- `HEADER` is `0xFE`. -/
recall packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq :
    packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER = 254#u8

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq
/-- `HEADER` is `0xFE`. -/
recall packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq :
    packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER = 254#u8

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq
/-- `HEADER` is `0x00`. -/
recall packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq :
    packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER = 0#u8

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.HEADER_eq
/-- `OkPacketKind::parse_body for ResultSetTerminator`: total; the OK packet fields after the header (`rsTerminatorBodyRead`): affected rows and last insert id are read but reported as 0. -/
recall packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body caps buf ⦃ r rest =>
      ((okPart r).map OkBody.ofBody, rest.val) = rsTerminatorBodyRead caps.val buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownStatusFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec
/-- `OkPacketKind::parse_body for OldEofPacket`: total; `warnings` and `status_flags` (`eofBodyRead`). -/
recall packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body caps buf ⦃ r rest =>
      ((okPart r).map OkBody.ofBody, rest.val) = eofBodyRead buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownStatusFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec
/-- `OkPacketKind::parse_body for NetworkStreamTerminator`: total; as `OldEofPacket` (`eofBodyRead`). -/
recall packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body caps buf ⦃ r rest =>
      ((okPart r).map OkBody.ofBody, rest.val) = eofBodyRead buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownStatusFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec
/-- `OkPacketKind::parse_body for CommonOkPacket`: total; the OK packet fields after the header (`okBodyRead`). -/
recall packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body caps buf ⦃ r rest =>
      ((okPart r).map OkBody.ofBody, rest.val) = okBodyRead caps.val buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownStatusFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind.parse_body_spec
/-! ### `struct OkPacket and its impls` -/

/-- `TryFrom<OkPacketBody> for OkPacket`: never fails; `OkBody.toPkt` (a last insert id of 0 and empty strings become `None`). -/
recall packets.OkPacket.Insts.CoreConvertTryFromOkPacketBodyError.try_from_spec (body : packets.OkPacketBody) :
    packets.OkPacket.Insts.CoreConvertTryFromOkPacketBodyError.try_from body ⦃ r =>
      (okPart r).map OkPkt.ofPacket = some (OkBody.ofBody body).toPkt ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacket.Insts.CoreConvertTryFromOkPacketBodyError.try_from_spec
/-- `into_owned`: the same fields. -/
recall packets.OkPacket.into_owned_spec (self : packets.OkPacket) :
    packets.OkPacket.into_owned self ⦃ p => OkPkt.ofPacket p = OkPkt.ofPacket self ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacket.into_owned_spec
/-- `affected_rows`: the field. -/
recall packets.OkPacket.impl.affected_rows_eq (self : packets.OkPacket) :
    packets.OkPacket.impl.affected_rows self = ok self.affected_rows

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacket.impl.affected_rows_eq
/-- `last_insert_id`: the field. -/
recall packets.OkPacket.impl.last_insert_id_eq (self : packets.OkPacket) :
    packets.OkPacket.impl.last_insert_id self = ok self.last_insert_id

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacket.impl.last_insert_id_eq
/-- `status_flags`: the field. -/
recall packets.OkPacket.impl.status_flags_eq (self : packets.OkPacket) :
    packets.OkPacket.impl.status_flags self = ok self.status_flags

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacket.impl.status_flags_eq
/-- `warnings`: the field. -/
recall packets.OkPacket.impl.warnings_eq (self : packets.OkPacket) :
    packets.OkPacket.impl.warnings self = ok self.warnings

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacket.impl.warnings_eq
/-- `info_ref`: the info bytes, if any. -/
recall packets.OkPacket.info_ref_spec (self : packets.OkPacket) :
    packets.OkPacket.info_ref self ⦃ o => o.map (·.val) = self.info.map (fun rb => cowList rb.1) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacket.info_ref_spec
/-- `session_state_info_ref`: the session state bytes, if any. -/
recall packets.OkPacket.session_state_info_ref_spec (self : packets.OkPacket) :
    packets.OkPacket.session_state_info_ref self ⦃ o =>
      o.map (·.val) = self.session_state_info.map (fun rb => cowList rb.1) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacket.session_state_info_ref_spec
/-! ### `struct OkPacketDeserializer and its impls` -/

/-- `into_inner`: the packet. -/
recall packets.OkPacketDeserializer.into_inner_eq {T : Type} (self : packets.OkPacketDeserializer T) :
    packets.OkPacketDeserializer.into_inner self = ok self.1

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacketDeserializer.into_inner_eq
/-- `MyDeserialize for OkPacketDeserializer<T>`: `SIZE` is `None`. -/
recall packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq {T : Type} (inst : packets.OkPacketKind T) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE inst = none

/-- [propext, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq
/-- `MyDeserialize for OkPacketDeserializer<ResultSetTerminator>`: total; `okPacketRead .resultSetTerminator` (header byte, body, conversion to `OkPacket`). -/
recall packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_resultSetTerminator (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      ((okPart r).map (fun d => OkPkt.ofPacket d.1), rest.val) = okPacketRead .resultSetTerminator caps.val buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownStatusFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_resultSetTerminator
/-- `MyDeserialize for OkPacketDeserializer<OldEofPacket>`: total; `okPacketRead .oldEof` (header byte, body, conversion to `OkPacket`). -/
recall packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_oldEof (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      ((okPart r).map (fun d => OkPkt.ofPacket d.1), rest.val) = okPacketRead .oldEof caps.val buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownStatusFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_oldEof
/-- `MyDeserialize for OkPacketDeserializer<NetworkStreamTerminator>`: total; `okPacketRead .networkStreamTerminator` (header byte, body, conversion to `OkPacket`). -/
recall packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_networkStreamTerminator (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      ((okPart r).map (fun d => OkPkt.ofPacket d.1), rest.val) = okPacketRead .networkStreamTerminator caps.val buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownStatusFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_networkStreamTerminator
/-- `MyDeserialize for OkPacketDeserializer<CommonOkPacket>`: total; `okPacketRead .commonOk` (header byte, body, conversion to `OkPacket`). -/
recall packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_commonOk (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      ((okPart r).map (fun d => OkPkt.ofPacket d.1), rest.val) = okPacketRead .commonOk caps.val buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownStatusFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_commonOk
/-- Round trip: an OK packet (`okPacketEnc 0x00`, in the protocol page's form or, `compact`, as MySQL's `net_send_ok` writes it) is read back by `OkPacketDeserializer<CommonOkPacket>` (as `OkBody.toPkt`), when its status has only known flags and it carries a session state only if both `CLIENT_SESSION_TRACK` and `SERVER_SESSION_STATE_CHANGED` are set. The packet is the whole buffer. -/
recall packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_commonOk (h64 : Target64) (caps : constants.CapabilityFlags) (b : OkBody) (hb : b.affectedRows < 2 ^ 64 ∧ b.lastInsertId < 2 ^ 64 ∧ b.status < 2 ^ 16 ∧
      statusRead b.status = some b.status ∧ b.warnings < 2 ^ 16)
    (hssi : (hasFlag caps.val CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = [])
    (compact : Bool) (buf : io.ParseBuf) (h : buf.val = okPacketEnc 0x00 caps.val compact b) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.CommonOkPacket.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      (okPart r).map (fun d => OkPkt.ofPacket d.1) = some b.toPkt ∧ rest.val = [] ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownStatusFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_commonOk
/-- Round trip: an OK packet with header `0xFE` (either form) is read back by `OkPacketDeserializer<ResultSetTerminator>`, with affected rows and last insert id 0. -/
recall packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_resultSetTerminator (h64 : Target64) (caps : constants.CapabilityFlags) (b : OkBody) (hb : b.affectedRows < 2 ^ 64 ∧ b.lastInsertId < 2 ^ 64 ∧ b.status < 2 ^ 16 ∧
      statusRead b.status = some b.status ∧ b.warnings < 2 ^ 16)
    (hssi : (hasFlag caps.val CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = [])
    (compact : Bool) (buf : io.ParseBuf) (h : buf.val = okPacketEnc 0xFE caps.val compact b) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.ResultSetTerminator.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      (okPart r).map (fun d => OkPkt.ofPacket d.1) =
        some { b with affectedRows := 0, lastInsertId := 0 }.toPkt ∧ rest.val = [] ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownStatusFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_resultSetTerminator
/-- Round trip: an EOF packet is read back by `OkPacketDeserializer<OldEofPacket>` when its status has only known flags. -/
recall packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_oldEof (caps : constants.CapabilityFlags) (w s : Nat) (hw : w < 2 ^ 16) (hs : s < 2 ^ 16)
    (hsk : statusRead s = some s) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = eofPacketEnc w s ++ tail) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.OldEofPacket.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      (okPart r).map (fun d => OkPkt.ofPacket d.1) = some ⟨0, none, s, w, none, none⟩ ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownStatusFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_oldEof
/-- Round trip: an EOF packet is read back by `OkPacketDeserializer<NetworkStreamTerminator>` when its status has only known flags. -/
recall packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_networkStreamTerminator (caps : constants.CapabilityFlags) (w s : Nat) (hw : w < 2 ^ 16) (hs : s < 2 ^ 16)
    (hsk : statusRead s = some s) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = eofPacketEnc w s ++ tail) :
    packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize packets.NetworkStreamTerminator.Insts.Mysql_commonPacketsOkPacketKind caps buf ⦃ r rest =>
      (okPart r).map (fun d => OkPkt.ofPacket d.1) = some ⟨0, none, s, w, none, none⟩ ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, constants.UnknownStatusFlags.Insts.CoreFmtDisplay.fmt, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacketDeserializer.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip_networkStreamTerminator
/-! ### `struct ProgressReport and its impls` -/

/-- `new`: the given fields (the stage info converted with `into`). -/
recall packets.ProgressReport.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (stage max_stage : U8) (progress : U32) (stage_info : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into stage_info = ok c) :
    packets.ProgressReport.new into stage max_stage progress stage_info ⦃ p =>
      p.stage.1 = stage ∧ p.max_stage.1 = max_stage ∧ p.progress.1 = progress ∧ p.stage_info.1 = c ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ProgressReport.new_spec
/-- `stage`: the field. -/
recall packets.ProgressReport.impl.stage_eq (self : packets.ProgressReport) :
    packets.ProgressReport.impl.stage self = ok self.stage.1

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ProgressReport.impl.stage_eq
/-- `max_stage`: the field. -/
recall packets.ProgressReport.impl.max_stage_eq (self : packets.ProgressReport) :
    packets.ProgressReport.impl.max_stage self = ok self.max_stage.1

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ProgressReport.impl.max_stage_eq
/-- `progress`: the field. -/
recall packets.ProgressReport.impl.progress_eq (self : packets.ProgressReport) :
    packets.ProgressReport.impl.progress self = ok self.progress.1

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ProgressReport.impl.progress_eq
/-- `stage_info_ref`: the stage info bytes. -/
recall packets.ProgressReport.stage_info_ref_spec (self : packets.ProgressReport) :
    packets.ProgressReport.stage_info_ref self ⦃ s => s.val = cowList self.stage_info.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ProgressReport.stage_info_ref_spec
/-- `into_owned`: the same fields. -/
recall packets.ProgressReport.into_owned_spec (self : packets.ProgressReport) :
    packets.ProgressReport.into_owned self ⦃ p => Progress.of p = Progress.of self ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ProgressReport.into_owned_spec
/-- `MyDeserialize for ProgressReport`: `SIZE` is `None`. -/
recall packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for ProgressReport`: total; `progressRead`. -/
recall packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64) (buf : io.ParseBuf) :
    packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map Progress.of, rest.val) = progressRead buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MySerialize for ProgressReport`: appends `progressEnc` (the progress truncated to 3 bytes). -/
recall packets.ProgressReport.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ProgressReport) (buf : alloc.vec.Vec U8)
    (h : buf.length + (progressEnc (Progress.of self)).length ≤ Usize.max) :
    packets.ProgressReport.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ progressEnc (Progress.of self) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ProgressReport.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-- Round trip: `deserialize` reads back what `serialize` writes, when the progress fits in 3 bytes. -/
recall packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h64 : Target64) (p : packets.ProgressReport) (hp : p.progress.1.val < 2 ^ 24) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = progressEnc (Progress.of p) ++ tail) :
    packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map Progress.of = some (Progress.of p) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ProgressReport.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
/-! ### `enum ErrPacket and its impls` -/

/-- `is_error`: an error, not a progress report. -/
recall packets.ErrPacket.is_error_spec (self : packets.ErrPacket) :
    packets.ErrPacket.is_error self ⦃ b => (b ↔ ∃ e, self = .Error e) ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ErrPacket.is_error_spec
/-- `is_progress_report`: a progress report. -/
recall packets.ErrPacket.is_progress_report_spec (self : packets.ErrPacket) :
    packets.ErrPacket.is_progress_report self ⦃ b => (b ↔ ∃ p, self = .Progress p) ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ErrPacket.is_progress_report_spec
/-- `progress_report`: the report. -/
recall packets.ErrPacket.progress_report_progress (p : packets.ProgressReport) :
    packets.ErrPacket.progress_report (.Progress p) = ok p

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ErrPacket.progress_report_progress
/-- `progress_report` panics on an error (documented). -/
recall packets.ErrPacket.progress_report_error (e : packets.ServerError) :
    packets.ErrPacket.progress_report (.Error e) = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ErrPacket.progress_report_error
/-- `server_error`: the error. -/
recall packets.ErrPacket.server_error_error (e : packets.ServerError) :
    packets.ErrPacket.server_error (.Error e) = ok e

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ErrPacket.server_error_error
/-- `server_error` panics on a progress report (documented). -/
recall packets.ErrPacket.server_error_progress (p : packets.ProgressReport) :
    packets.ErrPacket.server_error (.Progress p) = fail .panic

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ErrPacket.server_error_progress
/-- `MyDeserialize for ErrPacket`: `SIZE` is `None`. -/
recall packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq :
    packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE = none

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.SIZE_eq
/-- `MyDeserialize for ErrPacket`: total; `errPacketRead` (header, code, then a progress report or the SQL state and message). -/
recall packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec (h64 : Target64) (caps : constants.CapabilityFlags) (buf : io.ParseBuf) :
    packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      ((okPart r).map ErrPkt.of, rest.val) = errPacketRead caps.val buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize_spec
/-- `MySerialize for ErrPacket`: appends `errPacketEnc` (the progress truncated to 3 bytes). -/
recall packets.ErrPacket.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ErrPacket) (buf : alloc.vec.Vec U8)
    (h : buf.length + (errPacketEnc (ErrPkt.of self)).length ≤ Usize.max) :
    packets.ErrPacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ errPacketEnc (ErrPkt.of self) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ErrPacket.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-- Round trip: an ERR packet is read back when it fits the capabilities (`errCompatible`: SQL state iff `CLIENT_PROTOCOL_41`, no error code `0xFFFF` under `CLIENT_PROGRESS_OBSOLETE`, progress reports only under it). The packet is the whole buffer (the message extends to its end). -/
recall packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip (h64 : Target64) (caps : constants.CapabilityFlags) (e : packets.ErrPacket)
    (hc : errCompatible caps.val (ErrPkt.of e)) (buf : io.ParseBuf) (h : buf.val = errPacketEnc (ErrPkt.of e)) :
    packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.deserialize caps buf ⦃ r rest =>
      (okPart r).map ErrPkt.of = some (ErrPkt.of e) ∧ rest.val = [] ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ErrPacket.Insts.Mysql_commonProtoMyDeserializeDeCapabilityFlags.roundtrip
/-! ### `struct SqlState and its impls` -/

/-- `new`: the given state. -/
recall packets.SqlState.new_eq (state : Array U8 5#usize) :
    packets.SqlState.new state = ok { __state_marker := (), state }

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SqlState.new_eq
/-- `as_bytes`: the state. -/
recall packets.SqlState.as_bytes_eq (self : packets.SqlState) :
    packets.SqlState.as_bytes self = ok self.state

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SqlState.as_bytes_eq
/-- `MyDeserialize for SqlState`: `SIZE` is `Some(6)`. -/
recall packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 6#usize

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for SqlState`: total (each part is read with `parse`); `sqlStateRead` (`#`, then 5 bytes). -/
recall packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (buf : io.ParseBuf) :
    packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun s => s.state.val), rest.val) = sqlStateRead buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SqlState.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MySerialize for SqlState`: appends `#` and the state. -/
recall packets.SqlState.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.SqlState) (buf : alloc.vec.Vec U8) (h : buf.length + 6 ≤ Usize.max) :
    packets.SqlState.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' => buf'.val = buf.val ++ byte 0x23 :: self.state.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SqlState.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `struct ServerError and its impls` -/

/-- `new`: the given fields (the message converted with `into`). -/
recall packets.ServerError.new_spec {T1 : Type} (into : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (code : U16) (state : Option packets.SqlState) (msg : T1) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into msg = ok c) :
    packets.ServerError.new into code state msg ⦃ e =>
      e.code.1 = code ∧ e.state = state ∧ e.message.1 = c ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ServerError.new_spec
/-- `error_code`: the field. -/
recall packets.ServerError.error_code_eq (self : packets.ServerError) :
    packets.ServerError.error_code self = ok self.code.1

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ServerError.error_code_eq
/-- `sql_state_ref`: the field. -/
recall packets.ServerError.sql_state_ref_eq (self : packets.ServerError) :
    packets.ServerError.sql_state_ref self = ok self.state

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ServerError.sql_state_ref_eq
/-- `message_ref`: the message bytes. -/
recall packets.ServerError.message_ref_spec (self : packets.ServerError) :
    packets.ServerError.message_ref self ⦃ s => s.val = cowList self.message.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ServerError.message_ref_spec
/-- `into_owned`: the same fields. -/
recall packets.ServerError.into_owned_spec (self : packets.ServerError) :
    packets.ServerError.into_owned self ⦃ e => ErrPkt.ofServerError e = ErrPkt.ofServerError self ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ServerError.into_owned_spec
/-- `MyDeserialize for ServerError`: `SIZE` is `None`. -/
recall packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.SIZE_eq :
    packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.SIZE = none

/-- [propext] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.SIZE_eq
/-- `MyDeserialize for ServerError` with context `(code, protocol_41)`: total; `serverErrorRead`. -/
recall packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.deserialize_spec (code : U16) (p41 : Bool) (buf : io.ParseBuf) :
    packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.deserialize (code, p41) buf ⦃ r rest =>
      ((okPart r).map ErrPkt.ofServerError, rest.val) = serverErrorRead code.val p41 buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofError, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ServerError.Insts.Mysql_commonProtoMyDeserializeDePairU16Bool.deserialize_spec
/-- `MySerialize for ServerError`: appends the SQL state (`#` and 5 bytes) if present, then the message (the code is written by `ErrPacket`). -/
recall packets.ServerError.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ServerError) (buf : alloc.vec.Vec U8)
    (h : buf.length + 6 + (cowList self.message.1).length ≤ Usize.max) :
    packets.ServerError.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ (match self.state with | some s => byte 0x23 :: s.state.val | none => [])
        ++ cowList self.message.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ServerError.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `struct NullBitmap and its impls` -/

/-- `ClientSide::BIT_OFFSET` is 0 (from `src/value/mod.rs`; the offset of `COM_STMT_EXECUTE` bitmaps). -/
recall value.ClientSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET_val :
    value.ClientSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET.val = 0

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms value.ClientSide.Insts.Mysql_commonValueSerializationSide.BIT_OFFSET_val
/-- `MyDeserialize for NullBitmap<T, Cow<[u8]>>`: `SIZE` is `None`. -/
recall packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq {T : Type} (inst : value.SerializationSide T) :
    packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE inst = none

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq
/-- `MyDeserialize for NullBitmap<T, Cow<[u8]>>` with context the number of columns: total; the next `bitmap_len` bytes, or an error with the buffer unchanged if there are fewer. -/
recall packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max) (buf : io.ParseBuf) :
    packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize inst n buf ⦃ r rest =>
      if nullBitmapLen off.val n.val ≤ buf.length then
        (okPart r).map (fun bm => cowList bm.1) = some (buf.val.take (nullBitmapLen off.val n.val)) ∧
        rest.val = buf.val.drop (nullBitmapLen off.val n.val)
      else okPart r = none ∧ rest = buf ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NullBitmapTCowDeSliceU8VecU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec
/-- `new`: an all-clear bitmap of `bitmap_len` bytes. -/
recall packets.NullBitmapTVecU8.new_spec {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max) :
    packets.NullBitmapTVecU8.new inst n ⦃ bm =>
      bm.1.val = List.replicate (nullBitmapLen off.val n.val) (byte 0) ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NullBitmapTVecU8.new_spec
/-- `read`: the first `bitmap_len` bytes of `input`, and the rest. -/
recall packets.NullBitmapTVecU8.read_spec {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (input : Slice U8) (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max)
    (hin : nullBitmapLen off.val n.val ≤ input.length) :
    packets.NullBitmapTVecU8.read inst input n ⦃ bm rest =>
      bm.1.val = input.val.take (nullBitmapLen off.val n.val) ∧
      rest.val = input.val.drop (nullBitmapLen off.val n.val) ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NullBitmapTVecU8.read_spec
/-- `read` panics (`assert!`) on an input shorter than `bitmap_len`. -/
recall packets.NullBitmapTVecU8.read_panics {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (input : Slice U8) (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max)
    (hin : input.length < nullBitmapLen off.val n.val) :
    ¬ packets.NullBitmapTVecU8.read inst input n ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NullBitmapTVecU8.read_panics
/-- `bitmap_len`: `(n + 7 + BIT_OFFSET) / 8`. -/
recall packets.NullBitmap.bitmap_len_spec {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8))
    (off : Usize) (hoff : inst.BIT_OFFSET = ok off) (n : Usize) (hn : n.val + 7 + off.val ≤ Usize.max) :
    packets.NullBitmap.bitmap_len inst asRef n ⦃ r => r.val = nullBitmapLen off.val n.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NullBitmap.bitmap_len_spec
/-- `from_bytes`: wraps the bytes. -/
recall packets.NullBitmap.from_bytes_eq {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8)) (bytes : U) :
    packets.NullBitmap.from_bytes inst asRef bytes = ok (bytes, ())

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NullBitmap.from_bytes_eq
/-- `is_null(i)`: bit `i + BIT_OFFSET` of the bytes, for any byte container `U` (given its bytes `s`). -/
recall packets.NullBitmap.is_null_spec {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8))
    (off : Usize) (hoff : inst.BIT_OFFSET = ok off) (self : packets.NullBitmap T U) (s : Slice U8)
    (hs : asRef.as_ref self.1 = ok s) (i : Usize) (hi : i.val + off.val ≤ Usize.max)
    (hb : (i.val + off.val) / 8 < s.length) :
    packets.NullBitmap.is_null inst asRef self i ⦃ b => b = bitmapBit off.val s.val i.val ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NullBitmap.is_null_spec
/-- `is_null(i)` panics (`assert!`) when bit `i + BIT_OFFSET` is past the bytes. -/
recall packets.NullBitmap.is_null_panics {T U : Type} (inst : value.SerializationSide T) (asRef : core.convert.AsRef U (Slice U8))
    (off : Usize) (hoff : inst.BIT_OFFSET = ok off) (self : packets.NullBitmap T U) (s : Slice U8)
    (hs : asRef.as_ref self.1 = ok s) (i : Usize) (hi : i.val + off.val ≤ Usize.max)
    (hb : s.length ≤ (i.val + off.val) / 8) :
    ¬ packets.NullBitmap.is_null inst asRef self i ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NullBitmap.is_null_panics
/-- `set(i, is_null)` (at `Vec<u8>`): sets bit `i + BIT_OFFSET` to `is_null`, every other bit unchanged. -/
recall packets.NullBitmap.set_spec {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (self : packets.NullBitmap T (alloc.vec.Vec U8)) (i : Usize) (b : Bool)
    (hi : i.val + off.val ≤ Usize.max) (hb : (i.val + off.val) / 8 < self.1.length) :
    packets.NullBitmap.set inst (alloc.vec.Vec.Insts.CoreConvertAsRefSlice U8 alloc.alloc.Global) (alloc.vec.Vec.Insts.CoreConvertAsMutSlice U8 alloc.alloc.Global) self i b ⦃ bm =>
      bm.1.length = self.1.length ∧
      ∀ pos, bitAt bm.1.val pos = if pos = i.val + off.val then b else bitAt self.1.val pos ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NullBitmap.set_spec
/-- `set(i, _)` panics (`assert!`) when bit `i + BIT_OFFSET` is past the bytes. -/
recall packets.NullBitmap.set_panics {T : Type} (inst : value.SerializationSide T) (off : Usize) (hoff : inst.BIT_OFFSET = ok off)
    (self : packets.NullBitmap T (alloc.vec.Vec U8)) (i : Usize) (b : Bool)
    (hi : i.val + off.val ≤ Usize.max) (hb : self.1.length ≤ (i.val + off.val) / 8) :
    ¬ packets.NullBitmap.set inst (alloc.vec.Vec.Insts.CoreConvertAsRefSlice U8 alloc.alloc.Global) (alloc.vec.Vec.Insts.CoreConvertAsMutSlice U8 alloc.alloc.Global) self i b ⦃ _ => True ⦄

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NullBitmap.set_panics
/-- `AsRef<[u8]> for NullBitmap`: the bytes. -/
recall packets.NullBitmap.Insts.CoreConvertAsRefSliceU8.as_ref_eq {T U : Type} (asRef : core.convert.AsRef U (Slice U8)) (self : packets.NullBitmap T U) :
    packets.NullBitmap.Insts.CoreConvertAsRefSliceU8.as_ref asRef self = asRef.as_ref self.1

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.NullBitmap.Insts.CoreConvertAsRefSliceU8.as_ref_eq
/-! ### `struct ComStmtExecuteRequestBuilder and its impls` -/

/-- `new`: the builder for the statement. -/
recall packets.ComStmtExecuteRequestBuilder.new_eq (stmt_id : U32) :
    packets.ComStmtExecuteRequestBuilder.new stmt_id = ok { stmt_id }

/-- [propext, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtExecuteRequestBuilder.new_eq
/-- `build(params)`: the request for the statement with no cursor, iteration count 1, the NULL bitmap of the parameters (offset 0; a parameter is NULL iff its binary encoding is empty), new-params-bound flag 1 and the parameters; `as_long_data` (also returned) iff the length the builder computes exceeds `MAX_PAYLOAD_LEN`. (The bound keeps that computation from overflowing.) -/
recall packets.ComStmtExecuteRequestBuilder.build_spec (self : packets.ComStmtExecuteRequestBuilder) (params : Slice value.Value)
    (h : stmtExecuteLen (params.val.map Val.ofValue) ≤ Usize.max) :
    packets.ComStmtExecuteRequestBuilder.build self params ⦃ req b =>
      req.stmt_id.1 = self.stmt_id ∧ req.flags.1.val = 0 ∧
      cowList req.bitmap.1 = nullBitmap 0 (params.val.map (fun v => isNullVal (Val.ofValue v))) ∧
      req.params_flags.1.val = 1 ∧ req.params = params ∧ req.as_long_data = b ∧
      (b = true ↔ maxPayloadLen < stmtExecuteLen (params.val.map Val.ofValue)) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtExecuteRequestBuilder.build_spec
/-- Headline: `build` then `serialize` appends the protocol's `COM_STMT_EXECUTE` packet (`comStmtExecute`), with the `Bytes` values left out iff `as_long_data`, for at most 65536 parameters (beyond, the bitmap is truncated). -/
recall packets.ComStmtExecuteRequestBuilder.build_serialize (self : packets.ComStmtExecuteRequestBuilder) (params : Slice value.Value) (buf : alloc.vec.Vec U8)
    (hn : params.length ≤ 65536) (h : buf.length + stmtExecuteLen (params.val.map Val.ofValue) ≤ Usize.max) :
    (packets.ComStmtExecuteRequestBuilder.build self params >>= fun p =>
      packets.ComStmtExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize p.1 buf) ⦃ buf' =>
      buf'.val = buf.val ++ comStmtExecute self.stmt_id.val (params.val.map Val.ofValue)
        (decide (maxPayloadLen < stmtExecuteLen (params.val.map Val.ofValue))) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtExecuteRequestBuilder.build_serialize
/-! ### `struct ComStmtExecuteRequest and its impls` -/

/-- `stmt_id`: the field. -/
recall packets.ComStmtExecuteRequest.impl.stmt_id_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.stmt_id self = ok self.stmt_id.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtExecuteRequest.impl.stmt_id_eq
/-- `flags`: the field. -/
recall packets.ComStmtExecuteRequest.impl.flags_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.flags self = ok self.flags.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtExecuteRequest.impl.flags_eq
/-- `bitmap`: the bitmap bytes, at most 8192 (`BareBytes<8192>`). -/
recall packets.ComStmtExecuteRequest.impl.bitmap_spec (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.bitmap self ⦃ s => s.val = (cowList self.bitmap.1).take 8192 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtExecuteRequest.impl.bitmap_spec
/-- `params_flags`: the field. -/
recall packets.ComStmtExecuteRequest.impl.params_flags_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.params_flags self = ok self.params_flags.1

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtExecuteRequest.impl.params_flags_eq
/-- `params`: the parameters (a slice of values: patch 28). -/
recall packets.ComStmtExecuteRequest.impl.params_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.params self = ok self.params

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtExecuteRequest.impl.params_eq
/-- `as_long_data`: the field. -/
recall packets.ComStmtExecuteRequest.impl.as_long_data_eq (self : packets.ComStmtExecuteRequest) :
    packets.ComStmtExecuteRequest.impl.as_long_data self = ok self.as_long_data

/-- [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtExecuteRequest.impl.as_long_data_eq
/-- `MySerialize for ComStmtExecuteRequest`: appends `stmtExecuteBytes` of its fields: header, statement id, flags, iteration count; if there are parameters, the bitmap (truncated to 8192 bytes), the params flags, the parameter types and the values (`Bytes` left out if `as_long_data`). -/
recall packets.ComStmtExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.ComStmtExecuteRequest) (buf : alloc.vec.Vec U8)
    (h : buf.length + (stmtExecuteBytes self.stmt_id.1.val self.flags.1.val ((cowList self.bitmap.1).take 8192)
      self.params_flags.1.val (self.params.val.map Val.ofValue) self.as_long_data).length ≤ Usize.max) :
    packets.ComStmtExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ stmtExecuteBytes self.stmt_id.1.val self.flags.1.val ((cowList self.bitmap.1).take 8192)
        self.params_flags.1.val (self.params.val.map Val.ofValue) self.as_long_data ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec
end mysql_common
