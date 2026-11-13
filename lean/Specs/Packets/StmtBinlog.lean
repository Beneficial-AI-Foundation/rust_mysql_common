import Proofs.Packets.ColumnBuilders
import Proofs.Packets.SessionStateInfo
import Proofs.Packets.OkPacketSessionStateInfo
import Proofs.Packets.StmtPacket
import Proofs.Packets.ComStmtSendLongData
import Proofs.Packets.ComStmtClose
import Proofs.Packets.ComStmtBulkExecuteRequestBuilder
import Proofs.Packets.StmtBulkExecuteParamType
import Proofs.Packets.StmtBulkExecuteParamValues
import Proofs.Packets.StmtBulkExecuteParamValue
import Proofs.Packets.ComStmtBulkExecuteRequest
import Proofs.Packets.ComRegisterSlave
import Proofs.Packets.ComTableDump
import Proofs.Packets.ComBinlogDump
import Proofs.Packets.GnoInterval
import Proofs.Packets.Tag
import Proofs.Packets.Sid
import Proofs.Packets.ComBinlogDumpGtid
import Proofs.Packets.SemiSyncAckPacket

/-!
# `src/packets/mod.rs` (continued): statement, session-state and replication packets
    The part of `src/packets/mod.rs` not in `Specs/Packets.lean` and not in the connection-phase
    spec file: `Column::new` and the `with_*` builders; `SessionStateInfo` and
    `OkPacket::session_state_info`; `StmtPacket` (`COM_STMT_PREPARE_OK`), `ComStmtSendLongData`,
    `ComStmtClose`; MariaDB's bulk execution (`ComStmtBulkExecuteRequestBuilder`,
    `StmtBulkExecuteParamType`, `StmtBulkExecuteParamValues`, `StmtBulkExecuteParamValue`,
    `ComStmtBulkExecuteRequest`); replication (`ComRegisterSlave`, `ComTableDump`,
    `ComBinlogDump`, `GnoInterval`, `Tag`, `Sid`, `ComBinlogDumpGtid`, `SemiSyncAckPacket`).
    (One file per Rust file is the rule; this file is kept apart from `Specs/Packets.lean` only
    while the two halves of the file are drafted in parallel, and is meant to be merged into it.)

    **Patches.** 61 (`BinlogDumpFlags`, `StmtBulkExecuteFlags` as plain bitflags), 64 (`misc::trusted`:
    `RawBytes::as_str` through `trusted::from_utf8_lossy`), 66 (`session_state_info` loop as
    recursion), 68 (`GnoInterval` errors), 69 (bulk execution: index loops and helpers), 71
    (`Sid`, `ComBinlogDumpGtid`: helpers, recursion, `trusted::sid_tag_from_utf8`), 72 (parameter
    names), and the general patches of `Specs/Packets.lean` (14 `cow_into_vec`, 22, 31). The
    statements are about the patched code.

    **Configuration.** As in `Specs/Io.lean`. Readers of length-encoded strings, of binary values,
    and of counts cast `u64 as usize` take `Target64`.

    **Allocation caveat.** "Does not panic" assumes allocation succeeds (Aeneas' model).
    Two readers call `Vec::with_capacity` with a count taken from the input before checking it
    against the input's length, which the model treats as free:
    * **`Seq<GnoInterval, LeU64>` (the intervals of a `Sid`)**: for a large count, real Rust
      aborts (out of memory), or panics (capacity overflow) for `count ≥ 2^59`, on a ~24-byte
      input, where the model returns an error (or, for `count ≥ 2^60`, panics later, at
      `16 * count`, a point real Rust never reaches); see `Sid::deserialize_overflow`;
    * **`ComBinlogDumpGtid::deserialize`, whose `Vec::with_capacity(n_sids)` with `n_sids` up to
      `2^56` from a 31-byte packet aborts real Rust (out of memory; observed at `2^56` SIDs)**,
      where the model returns an error (`deserialize_spec`).
    These readers parse packets sent *to* a server (by a replica).

    **Definitions used.** `Defs/CmdPackets.lean` (`ReadOut`, `strCowBytes`, `LossyUtf8Valid`,
    `StmtOk`, `stmtOkEnc`, `stmtOkRead`, `sendLongDataEnc`, `stmtCloseEnc`, `SEND_UNIT_RESULTS`,
    `SEND_TYPES_TO_SERVER`, `bulkIndicatorCode`, `bulkInd`, `bulkTy`, `bulkMerge`, `bulkTypes`,
    `BulkReq`, `bulkNew`, `bulkTypeEnc`, `bulkValueEnc`, `bulkReqEnc`, `bulkRowLen`, `bulkIV`,
    `bulkParams`, `BulkNewOut`, `bulkNewOut`, `BulkBuilder`, `AddRowOut`, `bulkAddRow`,
    `BulkBuilder.flags`, `BulkBuilder.Inv`, `bulkTypeRead`, `bulkTypesRead`, `bulkValueRead`,
    `bulkValuesRead`, `bulkReqRead`), `Defs/SessionState.lean` (`SsInfo`, `ssInfoEnc`,
    `ssInfoRead`, `ssInfos`, `SsChange`, `ssChangeRead`), `Defs/BinlogCmd.lean` (`RegSlave`,
    `regSlaveEnc`, `regSlaveRead`, `tableDumpEnc`, `tableDumpRead`, `BinlogDump`,
    `binlogDumpEnc`, `binlogDumpRead`, `binlogDumpFlagsAll`, `BINLOG_THROUGH_GTID`, `gnoEnc`,
    `SidV`, `sidEnc`, `sidTaggedEnc`, `gtidTagged`, `nSidsHeader`, `sidBlock`, `GtidDump`,
    `gtidDumpEnc`, `intervalsRead`, `sidRead`, `sidTaggedRead`, `sidsRead`, `gtidDumpRead`,
    `semiSyncAckEnc`, `semiSyncAckRead`), `Defs/Packets.lean` (`ColDef`), `Defs/Value.lean`
    (`Val`, `binEnc`, `binRead`, `binSupported`, `isUnsigned`), `Defs/Convert.lean` (`IsUtf8`,
    `utf8`), `Defs/VarLen.lean`, `Defs/LenEnc.lean`, `Defs/Flags.lean`, `Defs/Bytes.lean`.

    **Trusted axioms.** Beyond the opaque `io::Error` constructors and the opaque `Display` impls
    of the error types (which assert nothing): `Trusted.utf8LossyOwned` (the lossy accessors:
    their statements are exact only on valid UTF-8, the replaced string is opaque);
    `Trusted.gnoIntervalOrderError` (`GnoInterval::check_and_new`); `Trusted.sidTagUtf8Error`
    (the tagged `ComBinlogDumpGtid` reader). No `HashMap` axiom is used. No statement rests on
    the behaviour of `core.str.iter.IteratorChars.next` (an `opaque` of the Aeneas library
    without a model, reached by `Tag::new`): the `Tag` statements are partial and the GTID reader
    reports `unknown` where it would be needed.

    **Not covered.** `ColumnMeta::*_str` and `Column::*_str` (not in the translation's
    `start_from`); `ComStmtBulkExecuteRequestBuilder::add_params`, `_add_params`,
    `build_params_iter`, `build_iter` and `StmtBulkExecuteParamValues::new` (they take `Params`
    or iterators; not translated, patch 69); `Sid`'s `Display` and `FromStr`, `Tag`'s `Display`,
    the error types' `Display`; derived `Clone`/`PartialEq`/`Hash`/`Debug`. Private helpers
    (`bulk_param_types`, `merge_bulk_param_types`, `take_bulk_param_values`/`_row`,
    `set_bulk_param_types`, `parse_session_state_infos`, `Tag::validate`, `Sid::len`/
    `tag_str`/`tagged_len`/`serialize_tagged`/`deserialize_tagged`/`deserialize_tag`,
    `any_sid_tagged`, `sid_block_len_from`, `n_sids_header`, `serialize_sids_from`,
    `deserialize_tagged_sids`/`deserialize_untagged_sids`, `ComBinlogDumpGtid::is_tagged_format`/
    `sid_block_len`) are covered through their callers. Which 1–32-byte tags `Tag::new` accepts
    (see above), and hence the tagged `ComBinlogDumpGtid` reading of a SID whose tag has 1–32
    valid UTF-8 bytes (`unknown` in `gtidDumpRead`; it needs a model of `Chars::next`, or a
    translation patch checking the tag bytewise). Every other input of the readers is covered:
    `Defs.bulkReqRead_ne_unknown`, `Defs.sidRead_ne_unknown`, `Defs.gtidDumpRead_unknown`. The connection-phase packets of this file (handshake, auth, change user,
    SSL request, local infile) are in their own spec file.

    **Behaviour to note (bugs first).**
    * **`ComStmtBulkExecuteRequestBuilder::new` underflows for `max_allowed_packet < 4`**
      (`new_underflow`: a panic in debug builds, a huge limit in release builds).
    * **`ComStmtBulkExecuteRequest::deserialize` is misaligned with `SEND_TYPES_TO_SERVER`**:
      `StmtBulkExecuteParamType::SIZE` is `Some(3)` for a 2-byte type, so every type is read
      from 3 bytes and the crate's own packets are misread (`Defs.bulkReqRead_types_misread`).
    * **`ComStmtBulkExecuteRequest::deserialize` reads only the first row** of values
      (`Defs.bulkReqRead_first_row_only`), and reads a value after the `DEFAULT`/`IGNORE`
      indicators (the protocol sends none); a client-sent unsupported column type
      (`TIMESTAMP2` …) makes it panic.
    * Bulk type merging keeps the first of two conflicting types (a `TODO`) and unites the
      flags, so `Int(-1)` in a batch with a `UInt` is sent under `LONGLONG UNSIGNED` and read
      as `2^64 - 1` (`Defs.bulkTypes_int_uint`); later requests of a builder do not resend
      types, so the server keeps the first request's.
    * `Sid::serialize` and `Sid::deserialize` drop the tag; `ComBinlogDumpGtid` uses the tagged
      format as soon as one SID has a tag; its reader treats every format byte other than `1`
      as untagged (MySQL rejects it) and ignores bytes left in the SID block; the tagged
      `n_sids` word has `0` in bits 0–7 where MySQL writes `1` (harmless: MySQL's decoder ignores
      them); MySQL accepts uppercase tags (lowercasing them), the crate rejects them; `data_size` and the block are sent
      and read whatever `BINLOG_THROUGH_GTID` says; `data_size` is computed with saturating (and
      truncating `as u32`) arithmetic and is wrong for blocks of `2^32` bytes or more.
    * The interval reader allocates `count` intervals from the input's count before checking it
      (crash in real Rust, see the allocation caveat; in the model an error, or a panic at the
      unchecked `16 * count` for `count ≥ 2^60`: `Sid::deserialize_overflow`).
    * The `u8`/`u32`-length strings are truncated on serialization (documented); the `*_raw`
      accessors return the truncated (effective) bytes. `ComBinlogDump` accepts all three
      binlog flags. `StmtPacket` ignores its filler byte and anything after 12 bytes.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `impl Column`: `new` and the builders -/

/-- `Column::new(ty)`: the catalog `def` (`ColumnMeta::default`), every other string empty, every
    number 0, flags empty, the given column type. -/
recall packets.Column.new_spec (ty : constants.ColumnType) :
    packets.Column.new ty ⦃ c => ColDef.ofColumn c =
      { catalog := utf8 "def", schema := [], table := [], orgTable := [], colName := [],
        orgName := [], charset := 0, length := 0, type := ty, flags := 0, decimals := 0 } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.new_spec`

/-- `with_catalog`: replaces the catalog by (an owned copy of) the given bytes; nothing else
    changes. -/
recall packets.Column.with_catalog_spec (self : packets.Column) (catalog : Slice U8) :
    packets.Column.with_catalog self catalog ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with catalog := catalog.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.with_catalog_spec`

/-- `with_schema`: replaces the schema; nothing else changes. -/
recall packets.Column.with_schema_spec (self : packets.Column) (schema : Slice U8) :
    packets.Column.with_schema self schema ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with schema := schema.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.with_schema_spec`

/-- `with_table`: replaces the table; nothing else changes. -/
recall packets.Column.with_table_spec (self : packets.Column) (table : Slice U8) :
    packets.Column.with_table self table ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with table := table.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.with_table_spec`

/-- `with_org_table`: replaces the original table name; nothing else changes. -/
recall packets.Column.with_org_table_spec (self : packets.Column) (org_table : Slice U8) :
    packets.Column.with_org_table self org_table ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with orgTable := org_table.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.with_org_table_spec`

/-- `with_name`: replaces the column name; nothing else changes. -/
recall packets.Column.with_name_spec (self : packets.Column) («name» : Slice U8) :
    packets.Column.with_name self «name» ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with colName := «name».val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.with_name_spec`

/-- `with_org_name`: replaces the original column name; nothing else changes. -/
recall packets.Column.with_org_name_spec (self : packets.Column) (org_name : Slice U8) :
    packets.Column.with_org_name self org_name ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with orgName := org_name.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.with_org_name_spec`

/-- `with_flags`: replaces the flags; nothing else changes. -/
recall packets.Column.with_flags_spec (self : packets.Column) (flags : constants.ColumnFlags) :
    packets.Column.with_flags self flags ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with flags := flags.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.with_flags_spec`

/-- `with_column_length`: replaces the column length; nothing else changes. -/
recall packets.Column.with_column_length_spec (self : packets.Column) (column_length : U32) :
    packets.Column.with_column_length self column_length ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with length := column_length.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.with_column_length_spec`

/-- `with_character_set`: replaces the character set; nothing else changes. -/
recall packets.Column.with_character_set_spec (self : packets.Column) (character_set : U16) :
    packets.Column.with_character_set self character_set ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with charset := character_set.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.with_character_set_spec`

/-- `with_decimals`: replaces the decimals; nothing else changes. -/
recall packets.Column.with_decimals_spec (self : packets.Column) (decimals : U8) :
    packets.Column.with_decimals self decimals ⦃ c =>
      ColDef.ofColumn c = { ColDef.ofColumn self with decimals := decimals.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Column.with_decimals_spec`

/-! ### `struct SessionStateInfo and its impls` -/

/-- `into_owned`: the same type and data. -/
recall packets.SessionStateInfo.into_owned_spec (self : packets.SessionStateInfo) :
    packets.SessionStateInfo.into_owned self ⦃ s => SsInfo.of s = SsInfo.of self ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SessionStateInfo.into_owned_spec`

/-- `data_type`: the type. -/
recall packets.SessionStateInfo.impl.data_type_eq (self : packets.SessionStateInfo) :
    packets.SessionStateInfo.impl.data_type self = ok self.data_type.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SessionStateInfo.impl.data_type_eq`

/-- `data_ref`: the raw data. -/
recall packets.SessionStateInfo.data_ref_spec (self : packets.SessionStateInfo) :
    packets.SessionStateInfo.data_ref self ⦃ s => s.val = cowList self.data.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SessionStateInfo.data_ref_spec`

/-- `decode`: total; the data read as a change of the entry's type (`ssChangeRead`). Bytes of
    the data after the change are ignored. -/
recall packets.SessionStateInfo.decode_spec (h64 : Target64) (self : packets.SessionStateInfo) :
    packets.SessionStateInfo.decode self ⦃ r =>
      (okPart r).map SsChange.of = (ssChangeRead self.data_type.1 (cowList self.data.1)).1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SessionStateInfo.decode_spec`

/-- `MyDeserialize for SessionStateInfo`: `SIZE` is `None`. -/
recall packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for SessionStateInfo`: total; `ssInfoRead` (a type code 0–5, then the data as
    a length-encoded string). -/
recall packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (h64 : Target64) (buf : io.ParseBuf) :
    packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map SsInfo.of, rest.val) = ssInfoRead buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- Round trip: an entry in the protocol layout (`ssInfoEnc`) is read back. -/
recall packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (h64 : Target64) (s : packets.SessionStateInfo) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = ssInfoEnc (SsInfo.of s) ++ tail) :
    packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map SsInfo.of = some (SsInfo.of s) ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SessionStateInfo.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-- `MySerialize for SessionStateInfo`: appends `ssInfoEnc` (the type code, then the data as a
    length-encoded string). -/
recall packets.SessionStateInfo.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.SessionStateInfo) (buf : alloc.vec.Vec U8)
    (h : buf.length + (ssInfoEnc (SsInfo.of self)).length ≤ Usize.max) :
    packets.SessionStateInfo.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ ssInfoEnc (SsInfo.of self) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SessionStateInfo.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-! ### `OkPacket::session_state_info` -/

/-- `OkPacket::session_state_info`: total; no entries without session state, otherwise the
    entries of the session state string read until it is exhausted (`ssInfos`), an error if one
    is malformed. -/
recall packets.OkPacket.impl.session_state_info_spec (h64 : Target64) (self : packets.OkPacket) :
    packets.OkPacket.impl.session_state_info self ⦃ r =>
      (okPart r).map (fun v => v.val.map SsInfo.of) =
        match self.session_state_info with
        | none => some []
        | some rb => ssInfos (cowList rb.1) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.OkPacket.impl.session_state_info_spec`

/-! ### `struct StmtPacket and its impls` -/

/-- `MyDeserialize for StmtPacket`: `SIZE` is `Some(12)`. -/
recall packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 12#usize

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for StmtPacket`: total; `stmtOkRead` (12 bytes, status `0x00`). -/
recall packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map StmtOk.of, rest.val) = stmtOkRead buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- Round trip: a `COM_STMT_PREPARE_OK` in the protocol layout (`stmtOkEnc`) is read back. -/
recall packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (p : packets.StmtPacket) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = stmtOkEnc (StmtOk.of p) ++ tail) :
    packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map StmtOk.of = some (StmtOk.of p) ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-- `MySerialize for StmtPacket`: appends the 12 bytes `stmtOkEnc` (status and filler `0x00`). -/
recall packets.StmtPacket.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.StmtPacket) (buf : alloc.vec.Vec U8) (h : buf.length + 12 ≤ Usize.max) :
    packets.StmtPacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ stmtOkEnc (StmtOk.of self) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtPacket.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- `statement_id`: the field. -/
recall packets.StmtPacket.impl.statement_id_eq (self : packets.StmtPacket) :
    packets.StmtPacket.impl.statement_id self = ok self.statement_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtPacket.impl.statement_id_eq`

/-- `num_columns`: the field. -/
recall packets.StmtPacket.impl.num_columns_eq (self : packets.StmtPacket) :
    packets.StmtPacket.impl.num_columns self = ok self.num_columns.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtPacket.impl.num_columns_eq`

/-- `num_params`: the field. -/
recall packets.StmtPacket.impl.num_params_eq (self : packets.StmtPacket) :
    packets.StmtPacket.impl.num_params self = ok self.num_params.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtPacket.impl.num_params_eq`

/-- `warning_count`: the field. -/
recall packets.StmtPacket.impl.warning_count_eq (self : packets.StmtPacket) :
    packets.StmtPacket.impl.warning_count self = ok self.warning_count.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtPacket.impl.warning_count_eq`

/-! ### `struct ComStmtSendLongData and its impls` -/

/-- `ComStmtSendLongData::new(stmt_id, param_index, data)`: the given fields (`data.into()`). -/
recall packets.ComStmtSendLongData.new_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (stmt_id : U32) (param_index : U16) (data : T)
    (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into data = ok c) :
    packets.ComStmtSendLongData.new into stmt_id param_index data ⦃ p =>
      p.stmt_id.1 = stmt_id ∧ p.param_index.1 = param_index ∧ p.data.1 = c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtSendLongData.new_spec`

/-- `into_owned`: the same fields. -/
recall packets.ComStmtSendLongData.into_owned_spec (self : packets.ComStmtSendLongData) :
    packets.ComStmtSendLongData.into_owned self ⦃ p =>
      p.stmt_id.1 = self.stmt_id.1 ∧ p.param_index.1 = self.param_index.1 ∧
      cowList p.data.1 = cowList self.data.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtSendLongData.into_owned_spec`

/-- `MySerialize for ComStmtSendLongData`: appends the protocol's packet `sendLongDataEnc`
    (`0x18`, statement id, parameter index, all the data). -/
recall packets.ComStmtSendLongData.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComStmtSendLongData) (buf : alloc.vec.Vec U8)
    (h : buf.length + 7 + (cowList self.data.1).length ≤ Usize.max) :
    packets.ComStmtSendLongData.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++
        sendLongDataEnc self.stmt_id.1.val self.param_index.1.val (cowList self.data.1) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtSendLongData.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-! ### `struct ComStmtClose and its impls` -/

/-- `ComStmtClose::new(stmt_id)`: the statement id. -/
recall packets.ComStmtClose.new_eq (stmt_id : U32) :
    packets.ComStmtClose.new stmt_id = ok ⟨stmt_id⟩

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtClose.new_eq`

/-- `MySerialize for ComStmtClose`: appends the protocol's packet `stmtCloseEnc` (`0x19`, the
    statement id). -/
recall packets.ComStmtClose.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComStmtClose) (buf : alloc.vec.Vec U8) (h : buf.length + 5 ≤ Usize.max) :
    packets.ComStmtClose.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ stmtCloseEnc self.stmt_id.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtClose.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-! ### `struct ComStmtBulkExecuteRequestBuilder and its impls` -/

/-- `ComStmtBulkExecuteRequestBuilder::new(stmt_id, max_allowed_packet)`, for
    `max_allowed_packet ≥ 4`: no rows, types still to be sent, no unit results, no arity, no
    named parameters, a maximum payload of `max_allowed_packet - 4`. -/
recall packets.ComStmtBulkExecuteRequestBuilder.new_spec (stmt_id : U32) (max_allowed_packet : Usize)
    (h : 4 ≤ max_allowed_packet.val) :
    packets.ComStmtBulkExecuteRequestBuilder.new stmt_id max_allowed_packet ⦃ b =>
      BulkBuilder.of b = ⟨stmt_id.val, true, false, [], 0, none, none, max_allowed_packet.val - 4⟩ ∧
      (BulkBuilder.of b).Inv ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequestBuilder.new_spec`

/-- **Crate bug (crash path).** `new` panics (in debug builds; it wraps in release builds) for
    `max_allowed_packet < 4`: `max_allowed_packet - 4` underflows. -/
recall packets.ComStmtBulkExecuteRequestBuilder.new_underflow (stmt_id : U32) (max_allowed_packet : Usize)
    (h : max_allowed_packet.val < 4) :
    packets.ComStmtBulkExecuteRequestBuilder.new stmt_id max_allowed_packet = fail .integerOverflow

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequestBuilder.new_underflow`

/-- `with_named_params`: sets the named parameters; nothing else changes. -/
recall packets.ComStmtBulkExecuteRequestBuilder.with_named_params_spec
    (self : packets.ComStmtBulkExecuteRequestBuilder) (named_params : Option (Slice (alloc.vec.Vec U8))) :
    packets.ComStmtBulkExecuteRequestBuilder.with_named_params self named_params ⦃ b =>
      BulkBuilder.of b = { BulkBuilder.of self with namedParams := named_params } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequestBuilder.with_named_params_spec`

/-- `with_results`: requests unit results (`SEND_UNIT_RESULTS`); nothing else changes. -/
recall packets.ComStmtBulkExecuteRequestBuilder.impl.with_results_spec
    (self : packets.ComStmtBulkExecuteRequestBuilder) :
    packets.ComStmtBulkExecuteRequestBuilder.impl.with_results self ⦃ b =>
      BulkBuilder.of b = { BulkBuilder.of self with withResults := true } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequestBuilder.impl.with_results_spec`

/-- `add_row(row)`: exactly `bulkAddRow` (the arity is fixed by the first row offered; a row is
    added only while the request stays within `max_allowed_packet - 4`, otherwise handed back,
    or rejected with `RowTooLarge` if the builder has no rows). Preconditions: the size
    arithmetic does not overflow `usize`, and there is room for one more row (both true of any
    real builder). -/
recall packets.ComStmtBulkExecuteRequestBuilder.add_row_spec
    (self : packets.ComStmtBulkExecuteRequestBuilder) (params : alloc.vec.Vec value.Value)
    (hov : 7 + 2 * params.length + self.payload_len.val + bulkRowLen (params.val.map Val.ofValue)
      ≤ Usize.max)
    (hlen : self.params_set.length < Usize.max) :
    packets.ComStmtBulkExecuteRequestBuilder.add_row self params ⦃ r b =>
      (bulkAddRow (BulkBuilder.of self) params.val).1.Matches params r ∧
      BulkBuilder.of b = (bulkAddRow (BulkBuilder.of self) params.val).2 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequestBuilder.add_row_spec`

/-- `add_row` keeps the builder's bookkeeping right (`BulkBuilder.Inv`): in particular, while it
    has rows, the request `build` makes fits in `max_allowed_packet - 4` (`build_fits`). -/
recall packets.ComStmtBulkExecuteRequestBuilder.add_row_inv
    (self : packets.ComStmtBulkExecuteRequestBuilder) (params : alloc.vec.Vec value.Value)
    (hinv : (BulkBuilder.of self).Inv)
    (hov : 7 + 2 * params.length + self.payload_len.val + bulkRowLen (params.val.map Val.ofValue)
      ≤ Usize.max)
    (hlen : self.params_set.length < Usize.max) :
    packets.ComStmtBulkExecuteRequestBuilder.add_row self params ⦃ _ b => (BulkBuilder.of b).Inv ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequestBuilder.add_row_inv`

/-- `has_rows`: whether a row has been added since the last `build`. -/
recall packets.ComStmtBulkExecuteRequestBuilder.has_rows_spec
    (self : packets.ComStmtBulkExecuteRequestBuilder) :
    packets.ComStmtBulkExecuteRequestBuilder.has_rows self ⦃ b => b = decide (self.params_set.val ≠ []) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequestBuilder.has_rows_spec`

/-- `build`: the request `ComStmtBulkExecuteRequest::new` makes of the rows added (`bulkNewOut`;
    `NoParams` without rows), with `SEND_UNIT_RESULTS` if `with_results` and
    `SEND_TYPES_TO_SERVER` only in the builder's first request (`BulkBuilder.flags`); the
    builder is left without rows, with the types no longer to be sent and the arity kept.
    **Crate behaviour to note**: later requests of the same builder do not send the parameter
    types, so the server reuses the first request's types, although the later rows' types
    (`bulkTypes`) may differ (e.g. a first batch of `NULL`s has type `MYSQL_TYPE_NULL`).
    Precondition: the number of values fits in a `usize`. -/
recall packets.ComStmtBulkExecuteRequestBuilder.build_spec
    (self : packets.ComStmtBulkExecuteRequestBuilder)
    (hv : (self.params_set.val.map (·.length)).sum ≤ Usize.max) :
    packets.ComStmtBulkExecuteRequestBuilder.build self ⦃ r b =>
      (bulkNewOut self.stmt_id.val (BulkBuilder.of self).flags
        (self.params_set.val.map (fun row => row.val.map Val.ofValue))).Matches r ∧
      BulkBuilder.of b = { BulkBuilder.of self with withTypes := false, payloadLen := 0, rows := [] } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequestBuilder.build_spec`

/-- Headline: a builder whose bookkeeping is right (every builder made by `new`, `add_row` and
    `build`) builds requests whose packet fits in `max_allowed_packet - 4` bytes. -/
recall packets.ComStmtBulkExecuteRequestBuilder.build_fits
    (self : packets.ComStmtBulkExecuteRequestBuilder) (hinv : (BulkBuilder.of self).Inv)
    (hv : (self.params_set.val.map (·.length)).sum ≤ Usize.max) :
    packets.ComStmtBulkExecuteRequestBuilder.build self ⦃ r b =>
      (∀ q, r = .Ok q → (bulkReqEnc (BulkReq.of q)).length ≤ self.max_payload_len.val) ∧
      (BulkBuilder.of b).Inv ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequestBuilder.build_fits`

/-! ### `struct StmtBulkExecuteParamType and its impls` -/

/-- `StmtBulkExecuteParamType::new(type, flags)`: the given type and flags. -/
recall packets.StmtBulkExecuteParamType.new_eq (type : constants.ColumnType)
    (flags : constants.StmtExecuteParamFlags) :
    packets.StmtBulkExecuteParamType.new type flags = ok ⟨(type, ()), (flags, ())⟩

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamType.new_eq`

/-- `from_value(v)`: the type the crate sends for the value (`bulkTy`). -/
recall packets.StmtBulkExecuteParamType.from_value_spec (v : value.Value) :
    packets.StmtBulkExecuteParamType.from_value v ⦃ t =>
      (columnTypeCode t.type.1, t.flags.1.val) = bulkTy (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamType.from_value_spec`

/-- `column_type`: the type. -/
recall packets.StmtBulkExecuteParamType.column_type_eq (self : packets.StmtBulkExecuteParamType) :
    packets.StmtBulkExecuteParamType.column_type self = ok self.type.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamType.column_type_eq`

/-- `flags`: the flags. -/
recall packets.StmtBulkExecuteParamType.impl.flags_eq (self : packets.StmtBulkExecuteParamType) :
    packets.StmtBulkExecuteParamType.impl.flags self = ok self.flags.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamType.impl.flags_eq`

/-- `MyDeserialize for StmtBulkExecuteParamType`: **`SIZE` is `Some(3)`, but the type is 2
    bytes on the wire** (crate bug): `parse` (`parse_spec`) and the request reader consume 3
    bytes per type. -/
recall packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 3#usize

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for StmtBulkExecuteParamType`: total; `bulkTypeRead` (a known type code,
    then a flag byte 0 or 128). -/
recall packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun t => (columnTypeCode t.type.1, t.flags.1.val)), rest.val) =
        bulkTypeRead buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `buf.parse::<StmtBulkExecuteParamType>(())`: total; **consumes 3 bytes** (`SIZE`), of which
    `bulkTypeRead` reads two; an error with the buffer unchanged on fewer than 3 bytes (so a
    2-byte type at the end of a packet is rejected). -/
recall packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec
    (buf : io.ParseBuf) :
    io.ParseBuf.parse packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple buf () ⦃ r rest =>
      if 3 ≤ buf.length then
        (okPart r).map (fun t => (columnTypeCode t.type.1, t.flags.1.val)) = (bulkTypeRead (buf.val.take 3)).1 ∧
        rest.val = buf.val.drop 3
      else okPart r = none ∧ rest = buf ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMyDeserializeDeTuple.parse_spec`

/-- `MySerialize for StmtBulkExecuteParamType`: appends the 2 bytes `bulkTypeEnc` (type code,
    flag byte). -/
recall packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.StmtBulkExecuteParamType) (buf : alloc.vec.Vec U8) (h : buf.length + 2 ≤ Usize.max) :
    packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ bulkTypeEnc (columnTypeCode self.type.1, self.flags.1.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamType.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-! ### `struct StmtBulkExecuteParamValues and its impls` -/

/-- `AsRef<[StmtBulkExecuteParamValue]>`: the values. -/
recall packets.StmtBulkExecuteParamValues.Insts.CoreConvertAsRefSliceStmtBulkExecuteParamValue.as_ref_spec
    (self : packets.StmtBulkExecuteParamValues) :
    packets.StmtBulkExecuteParamValues.Insts.CoreConvertAsRefSliceStmtBulkExecuteParamValue.as_ref self ⦃ s =>
      s.val = self.values.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamValues.Insts.CoreConvertAsRefSliceStmtBulkExecuteParamValue.as_ref_spec`

/-- `MyDeserialize for StmtBulkExecuteParamValues`: `SIZE` is `None`. -/
recall packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE_eq :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE_eq`

/-- `MyDeserialize for StmtBulkExecuteParamValues` with the parameters `params`: one value per
    parameter (`bulkValuesRead`), exactly, whenever that reader returns. -/
recall packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_spec
    (h64 : Target64) (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (buf : io.ParseBuf) (r0 : Option (List (Nat × Val))) (rest0 : List U8)
    (h : bulkValuesRead (bulkParams params) buf.val = .done r0 rest0) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize params buf ⦃ r rest =>
      (okPart r).map (fun vs => vs.values.val.map bulkIV) = r0 ∧ rest.val = rest0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_spec`

/-- **Crash path.** `MyDeserialize for StmtBulkExecuteParamValues` panics where `bulkValuesRead`
    does: a non-`NULL` indicator for a parameter whose column type the binary reader does not
    support (`TIMESTAMP2`, `DATETIME2`, `TIME2`, `TYPED_ARRAY`, `UNKNOWN`). -/
recall packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_panics
    (h64 : Target64) (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (buf : io.ParseBuf) (e : Error) (h : bulkValuesRead (bulkParams params) buf.val = .panic e) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize params buf = fail e

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_panics`

/-- `MySerialize for StmtBulkExecuteParamValues`: appends each value (`bulkValueEnc`). -/
recall packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.StmtBulkExecuteParamValues) (buf : alloc.vec.Vec U8)
    (h : buf.length + ((self.values.val.map bulkIV).flatMap bulkValueEnc).length ≤ Usize.max) :
    packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ (self.values.val.map bulkIV).flatMap bulkValueEnc ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamValues.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-! ### `struct StmtBulkExecuteParamValue and its impls` -/

/-- `StmtBulkExecuteParamValue::new(v)`: the value, with the indicator `NULL` for `NULL` and
    `NONE` otherwise (`bulkInd`). -/
recall packets.StmtBulkExecuteParamValue.new_spec (v : value.Value) :
    packets.StmtBulkExecuteParamValue.new v ⦃ x =>
      x.value = v ∧ bulkIndicatorCode x.indicator.1 = bulkInd (Val.ofValue v) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamValue.new_spec`

/-- `indicator`: the indicator. -/
recall packets.StmtBulkExecuteParamValue.impl.indicator_eq (self : packets.StmtBulkExecuteParamValue) :
    packets.StmtBulkExecuteParamValue.impl.indicator self = ok self.indicator.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamValue.impl.indicator_eq`

/-- `value`: the value. -/
recall packets.StmtBulkExecuteParamValue.impl.value_eq (self : packets.StmtBulkExecuteParamValue) :
    packets.StmtBulkExecuteParamValue.impl.value self = ok self.value

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamValue.impl.value_eq`

/-- `MyDeserialize for StmtBulkExecuteParamValue`: `SIZE` is `None`. -/
recall packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.SIZE_eq :
    packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.SIZE_eq`

/-- `MyDeserialize for StmtBulkExecuteParamValue` for a parameter of column type `ct` with
    column flags `flags`: exactly `bulkValueRead` whenever that reader returns. **Crate
    behaviour**: a value is read after the `DEFAULT` and `IGNORE` indicators (the protocol sends
    none). -/
recall packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_spec
    (h64 : Target64) (ct : constants.ColumnType) (flags : constants.ColumnFlags) (buf : io.ParseBuf)
    (r0 : Option (Nat × Val)) (rest0 : List U8)
    (h : bulkValueRead ct (isUnsigned flags) buf.val = .done r0 rest0) :
    packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf ⦃ r rest =>
      (okPart r).map bulkIV = r0 ∧ rest.val = rest0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_spec`

/-- **Crash path.** `MyDeserialize for StmtBulkExecuteParamValue` panics where `bulkValueRead`
    does: an indicator other than `NULL` for a column type the binary reader does not support. -/
recall packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_panics
    (h64 : Target64) (ct : constants.ColumnType) (flags : constants.ColumnFlags) (buf : io.ParseBuf) (e : Error)
    (h : bulkValueRead ct (isUnsigned flags) buf.val = .panic e) :
    packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize (ct, flags) buf = fail e

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMyDeserializeDePairColumnTypeColumnFlags.deserialize_panics`

/-- `MySerialize for StmtBulkExecuteParamValue`: appends `bulkValueEnc` (the indicator, then the
    binary encoding of the value). -/
recall packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.StmtBulkExecuteParamValue) (buf : alloc.vec.Vec U8)
    (h : buf.length + (bulkValueEnc (bulkIV self)).length ≤ Usize.max) :
    packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ bulkValueEnc (bulkIV self) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.StmtBulkExecuteParamValue.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-! ### `struct ComStmtBulkExecuteRequest and its impls` -/

/-- `ComStmtBulkExecuteRequest::new(stmt_id, bulk_flags, rows)`: exactly `bulkNewOut` (`NoParams`
    for no rows, `MixedArity` if the rows differ in length, else the statement id, the flags,
    the merged types `bulkTypes` if the flags have `SEND_TYPES_TO_SERVER`, and every value with
    its indicator). Precondition: the number of values fits in a `usize`. -/
recall packets.ComStmtBulkExecuteRequest.new_spec (stmt_id : U32)
    (bulk_flags : constants.StmtBulkExecuteFlags) (values : alloc.vec.Vec (alloc.vec.Vec value.Value))
    (hv : (values.val.map (·.length)).sum ≤ Usize.max) :
    packets.ComStmtBulkExecuteRequest.new stmt_id bulk_flags values ⦃ r =>
      (bulkNewOut stmt_id.val bulk_flags.val (values.val.map (fun row => row.val.map Val.ofValue))).Matches r ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequest.new_spec`

/-- `stmt_id`: the statement id. -/
recall packets.ComStmtBulkExecuteRequest.impl.stmt_id_eq (self : packets.ComStmtBulkExecuteRequest) :
    packets.ComStmtBulkExecuteRequest.impl.stmt_id self = ok self.stmt_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequest.impl.stmt_id_eq`

/-- `bulk_flags`: the flags. -/
recall packets.ComStmtBulkExecuteRequest.impl.bulk_flags_eq (self : packets.ComStmtBulkExecuteRequest) :
    packets.ComStmtBulkExecuteRequest.impl.bulk_flags self = ok self.bulk_flags.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequest.impl.bulk_flags_eq`

/-- `types`: the parameter types. -/
recall packets.ComStmtBulkExecuteRequest.impl.types_spec (self : packets.ComStmtBulkExecuteRequest) :
    packets.ComStmtBulkExecuteRequest.impl.types self ⦃ s => s.val = cowList self.types.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequest.impl.types_spec`

/-- `values`: the values. -/
recall packets.ComStmtBulkExecuteRequest.impl.values_eq (self : packets.ComStmtBulkExecuteRequest) :
    packets.ComStmtBulkExecuteRequest.impl.values self = ok self.values

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequest.impl.values_eq`

/-- `MyDeserialize for ComStmtBulkExecuteRequest`: `SIZE` is `None`. -/
recall packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE_eq :
    packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.SIZE_eq`

/-- `MyDeserialize for ComStmtBulkExecuteRequest` with the parameters `params` the caller knows:
    exactly `bulkReqRead` whenever that reader returns. **Crate bugs** (see `bulkReqRead`):
    with `SEND_TYPES_TO_SERVER` each type is read from 3 bytes although it is sent in 2, so a
    request with parameters and types is misread (`Defs.bulkReqRead_types_misread`); only the
    first row of values is read (`Defs.bulkReqRead_first_row_only`). Precondition: `3 *
    params.len()` does not overflow `usize` (true of every real `Vec`). -/
recall packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_spec
    (h64 : Target64) (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (hn : 3 * params.length ≤ Usize.max) (buf : io.ParseBuf) (r0 : Option BulkReq) (rest0 : List U8)
    (h : bulkReqRead (bulkParams params) buf.val = .done r0 rest0) :
    packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize params buf ⦃ r rest =>
      (okPart r).map BulkReq.of = r0 ∧ rest.val = rest0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_spec`

/-- **Crash path.** `MyDeserialize for ComStmtBulkExecuteRequest` panics where `bulkReqRead` does:
    a value for a parameter whose column type (sent by the client with `SEND_TYPES_TO_SERVER`,
    or known to the caller) the binary reader does not support. A client can thus crash a
    server-side reader. -/
recall packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_panics
    (h64 : Target64) (params : alloc.vec.Vec (constants.ColumnType × constants.ColumnFlags))
    (hn : 3 * params.length ≤ Usize.max) (buf : io.ParseBuf) (e : Error)
    (h : bulkReqRead (bulkParams params) buf.val = .panic e) :
    packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize params buf = fail e

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMyDeserializeDeVecPairColumnTypeColumnFlags.deserialize_panics`

/-- `MySerialize for ComStmtBulkExecuteRequest`: appends `bulkReqEnc` (header, statement id,
    flags, the types only with `SEND_TYPES_TO_SERVER`, the values). For a request made by `new`
    this is the protocol's packet when every parameter's values have one type (or are `NULL`);
    otherwise each value is encoded in its own type under the merged type (`bulkTypes`, the
    first row's type for conflicting types: the `TODO`), which the server misreads. -/
recall packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComStmtBulkExecuteRequest) (buf : alloc.vec.Vec U8)
    (h : buf.length + (bulkReqEnc (BulkReq.of self)).length ≤ Usize.max) :
    packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ bulkReqEnc (BulkReq.of self) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComStmtBulkExecuteRequest.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-! ### `struct ComRegisterSlave and its impls` -/

/-- `ComRegisterSlave::new(server_id)`: the server id; the strings empty, the numbers 0. -/
recall packets.ComRegisterSlave.new_spec (server_id : U32) :
    packets.ComRegisterSlave.new server_id ⦃ p =>
      RegSlave.of p = ⟨server_id.val, [], [], [], 0, 0, 0⟩ ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.new_spec`

/-- `with_hostname`: sets the host name (`hostname.into()`, not truncated: serialization
    truncates); nothing else changes. -/
recall packets.ComRegisterSlave.with_hostname_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComRegisterSlave) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComRegisterSlave.with_hostname into self x ⦃ p =>
      RegSlave.of p = { RegSlave.of self with hostname := cowList c } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.with_hostname_spec`

/-- `with_user`: sets the user; nothing else changes. -/
recall packets.ComRegisterSlave.with_user_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComRegisterSlave) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComRegisterSlave.with_user into self x ⦃ p =>
      RegSlave.of p = { RegSlave.of self with user := cowList c } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.with_user_spec`

/-- `with_password`: sets the password; nothing else changes. -/
recall packets.ComRegisterSlave.with_password_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComRegisterSlave) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComRegisterSlave.with_password into self x ⦃ p =>
      RegSlave.of p = { RegSlave.of self with password := cowList c } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.with_password_spec`

/-- `with_port`: sets the port; nothing else changes. -/
recall packets.ComRegisterSlave.with_port_spec (self : packets.ComRegisterSlave) (port : U16) :
    packets.ComRegisterSlave.with_port self port ⦃ p =>
      RegSlave.of p = { RegSlave.of self with port := port.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.with_port_spec`

/-- `with_replication_rank`: sets the replication rank; nothing else changes. -/
recall packets.ComRegisterSlave.with_replication_rank_spec (self : packets.ComRegisterSlave)
    (replication_rank : U32) :
    packets.ComRegisterSlave.with_replication_rank self replication_rank ⦃ p =>
      RegSlave.of p = { RegSlave.of self with rank := replication_rank.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.with_replication_rank_spec`

/-- `with_master_id`: sets the master id; nothing else changes. -/
recall packets.ComRegisterSlave.with_master_id_spec (self : packets.ComRegisterSlave) (master_id : U32) :
    packets.ComRegisterSlave.with_master_id self master_id ⦃ p =>
      RegSlave.of p = { RegSlave.of self with masterId := master_id.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.with_master_id_spec`

/-- `server_id`: the field. -/
recall packets.ComRegisterSlave.impl.server_id_eq (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.server_id self = ok self.server_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.impl.server_id_eq`

/-- `hostname_raw`: the host name's effective bytes (at most the first 255). -/
recall packets.ComRegisterSlave.hostname_raw_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.hostname_raw self ⦃ s => s.val = (cowList self.hostname.1).take 255 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.hostname_raw_spec`

/-- `hostname`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
recall packets.ComRegisterSlave.impl.hostname_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.hostname self ⦃ c => LossyUtf8Valid ((cowList self.hostname.1).take 255) c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.impl.hostname_spec`

/-- `user_raw`: the user's effective bytes (at most the first 255). -/
recall packets.ComRegisterSlave.user_raw_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.user_raw self ⦃ s => s.val = (cowList self.user.1).take 255 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.user_raw_spec`

/-- `user`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
recall packets.ComRegisterSlave.impl.user_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.user self ⦃ c => LossyUtf8Valid ((cowList self.user.1).take 255) c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.impl.user_spec`

/-- `password_raw`: the password's effective bytes (at most the first 255). -/
recall packets.ComRegisterSlave.password_raw_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.password_raw self ⦃ s => s.val = (cowList self.password.1).take 255 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.password_raw_spec`

/-- `password`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
recall packets.ComRegisterSlave.impl.password_spec (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.password self ⦃ c => LossyUtf8Valid ((cowList self.password.1).take 255) c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.impl.password_spec`

/-- `port`: the field. -/
recall packets.ComRegisterSlave.impl.port_eq (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.port self = ok self.port.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.impl.port_eq`

/-- `replication_rank`: the field. -/
recall packets.ComRegisterSlave.impl.replication_rank_eq (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.replication_rank self = ok self.replication_rank.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.impl.replication_rank_eq`

/-- `master_id`: the field. -/
recall packets.ComRegisterSlave.impl.master_id_eq (self : packets.ComRegisterSlave) :
    packets.ComRegisterSlave.impl.master_id self = ok self.master_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.impl.master_id_eq`

/-- `MySerialize for ComRegisterSlave`: appends the protocol's packet `regSlaveEnc`, the strings
    truncated to 255 bytes (documented). -/
recall packets.ComRegisterSlave.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComRegisterSlave) (buf : alloc.vec.Vec U8)
    (h : buf.length + (regSlaveEnc (RegSlave.of self)).length ≤ Usize.max) :
    packets.ComRegisterSlave.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ regSlaveEnc (RegSlave.of self) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- `MyDeserialize for ComRegisterSlave`: `SIZE` is `None`. -/
recall packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for ComRegisterSlave`: total; `regSlaveRead`. -/
recall packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map RegSlave.of, rest.val) = regSlaveRead buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- Round trip: a packet with strings of at most 255 bytes, in the protocol layout, is read
    back. -/
recall packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (p : packets.ComRegisterSlave)
    (h255 : (RegSlave.of p).hostname.length ≤ 255 ∧ (RegSlave.of p).user.length ≤ 255 ∧
      (RegSlave.of p).password.length ≤ 255)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = regSlaveEnc (RegSlave.of p) ++ tail) :
    packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map RegSlave.of = some (RegSlave.of p) ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComRegisterSlave.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-! ### `struct ComTableDump and its impls` -/

/-- `ComTableDump::new(database, table)`: the two names (`into()`, not truncated). -/
recall packets.ComTableDump.new_spec {T1 T2 : Type}
    (into1 : core.convert.Into T1 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (into2 : core.convert.Into T2 (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (database : T1) (table : T2) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h1 : into1.into database = ok c1) (h2 : into2.into table = ok c2) :
    packets.ComTableDump.new into1 into2 database table ⦃ t =>
      cowList t.database.1 = cowList c1 ∧ cowList t.table.1 = cowList c2 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComTableDump.new_spec`

/-- `database_raw`: the database's effective bytes (at most the first 255). -/
recall packets.ComTableDump.database_raw_spec (self : packets.ComTableDump) :
    packets.ComTableDump.database_raw self ⦃ s => s.val = (cowList self.database.1).take 255 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComTableDump.database_raw_spec`

/-- `database`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
recall packets.ComTableDump.impl.database_spec (self : packets.ComTableDump) :
    packets.ComTableDump.impl.database self ⦃ c => LossyUtf8Valid ((cowList self.database.1).take 255) c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComTableDump.impl.database_spec`

/-- `table_raw`: the table's effective bytes (at most the first 255). -/
recall packets.ComTableDump.table_raw_spec (self : packets.ComTableDump) :
    packets.ComTableDump.table_raw self ⦃ s => s.val = (cowList self.table.1).take 255 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComTableDump.table_raw_spec`

/-- `table`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
recall packets.ComTableDump.impl.table_spec (self : packets.ComTableDump) :
    packets.ComTableDump.impl.table self ⦃ c => LossyUtf8Valid ((cowList self.table.1).take 255) c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComTableDump.impl.table_spec`

/-- `MySerialize for ComTableDump`: appends `tableDumpEnc` (`0x13`, the two names with 1-byte
    lengths, truncated to 255 bytes: documented). -/
recall packets.ComTableDump.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComTableDump) (buf : alloc.vec.Vec U8)
    (h : buf.length + (tableDumpEnc (cowList self.database.1) (cowList self.table.1)).length ≤ Usize.max) :
    packets.ComTableDump.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ tableDumpEnc (cowList self.database.1) (cowList self.table.1) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComTableDump.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- `MyDeserialize for ComTableDump`: `SIZE` is `None`. -/
recall packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for ComTableDump`: total; `tableDumpRead`. -/
recall packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun t => (cowList t.database.1, cowList t.table.1)), rest.val) =
        tableDumpRead buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- Round trip: names of at most 255 bytes, in the protocol layout, are read back. -/
recall packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (db tbl : List U8) (hdb : db.length ≤ 255) (htbl : tbl.length ≤ 255) (tail : List U8)
    (buf : io.ParseBuf) (h : buf.val = tableDumpEnc db tbl ++ tail) :
    packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun t => (cowList t.database.1, cowList t.table.1)) = some (db, tbl) ∧
      rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComTableDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-! ### `struct ComBinlogDump and its impls` -/

/-- `ComBinlogDump::new(server_id)`: position 0, no flags, the server id, an empty file name. -/
recall packets.ComBinlogDump.new_spec (server_id : U32) :
    packets.ComBinlogDump.new server_id ⦃ d => BinlogDump.of d = ⟨0, 0, server_id.val, []⟩ ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDump.new_spec`

/-- `with_pos`: sets the position; nothing else changes. -/
recall packets.ComBinlogDump.with_pos_spec (self : packets.ComBinlogDump) (pos : U32) :
    packets.ComBinlogDump.with_pos self pos ⦃ d =>
      BinlogDump.of d = { BinlogDump.of self with pos := pos.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDump.with_pos_spec`

/-- `with_flags`: sets the flags; nothing else changes. -/
recall packets.ComBinlogDump.with_flags_spec (self : packets.ComBinlogDump) (flags : packets.BinlogDumpFlags) :
    packets.ComBinlogDump.with_flags self flags ⦃ d =>
      BinlogDump.of d = { BinlogDump.of self with flags := flags.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDump.with_flags_spec`

/-- `with_filename`: sets the file name (`filename.into()`); nothing else changes. -/
recall packets.ComBinlogDump.with_filename_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComBinlogDump) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComBinlogDump.with_filename into self x ⦃ d =>
      BinlogDump.of d = { BinlogDump.of self with filename := cowList c } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDump.with_filename_spec`

/-- `pos`: the field. -/
recall packets.ComBinlogDump.impl.pos_eq (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.impl.pos self = ok self.pos.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDump.impl.pos_eq`

/-- `flags`: the field. -/
recall packets.ComBinlogDump.impl.flags_eq (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.impl.flags self = ok self.flags.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDump.impl.flags_eq`

/-- `server_id`: the field. -/
recall packets.ComBinlogDump.impl.server_id_eq (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.impl.server_id self = ok self.server_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDump.impl.server_id_eq`

/-- `filename_raw`: the file name. -/
recall packets.ComBinlogDump.filename_raw_spec (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.filename_raw self ⦃ s => s.val = cowList self.filename.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDump.filename_raw_spec`

/-- `filename`: the file name as a string, lossily converted (exact on valid UTF-8). -/
recall packets.ComBinlogDump.impl.filename_spec (self : packets.ComBinlogDump) :
    packets.ComBinlogDump.impl.filename self ⦃ c => LossyUtf8Valid (cowList self.filename.1) c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDump.impl.filename_spec`

/-- `MySerialize for ComBinlogDump`: appends the protocol's packet `binlogDumpEnc`. -/
recall packets.ComBinlogDump.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComBinlogDump) (buf : alloc.vec.Vec U8)
    (h : buf.length + (binlogDumpEnc (BinlogDump.of self)).length ≤ Usize.max) :
    packets.ComBinlogDump.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ binlogDumpEnc (BinlogDump.of self) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDump.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- `MyDeserialize for ComBinlogDump`: `SIZE` is `None`. -/
recall packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for ComBinlogDump`: total; `binlogDumpRead` (11 bytes, then the file name is
    the rest of the input). -/
recall packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map BinlogDump.of, rest.val) = binlogDumpRead buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- Round trip: a packet with known flags, in the protocol layout, is read back (the file name
    takes the rest of the input). -/
recall packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (d : packets.ComBinlogDump)
    (hf : (BinlogDump.of d).flags &&& binlogDumpFlagsAll = (BinlogDump.of d).flags)
    (buf : io.ParseBuf) (h : buf.val = binlogDumpEnc (BinlogDump.of d)) :
    packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map BinlogDump.of = some (BinlogDump.of d) ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDump.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-! ### `struct GnoInterval and its impls` -/

/-- `GnoInterval::new(start, end)`: the two bounds, unchecked. -/
recall packets.GnoInterval.new_spec (start «end» : U64) :
    packets.GnoInterval.new start «end» ⦃ g => g.start.1 = start ∧ g.«end».1 = «end» ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.GnoInterval.new_spec`

/-- `start`: the start (inclusive). -/
recall packets.GnoInterval.impl.start_eq (self : packets.GnoInterval) :
    packets.GnoInterval.impl.start self = ok self.start.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.GnoInterval.impl.start_eq`

/-- `end`: the end (exclusive). -/
recall packets.GnoInterval.impl.end_eq (self : packets.GnoInterval) :
    packets.GnoInterval.impl.end self = ok self.«end».1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.GnoInterval.impl.end_eq`

/-- `check_and_new(start, end)`: total; an error iff the interval `[start, end)` is empty or
    contains 0 (`start ≥ end` or `start = 0`; GNOs start at 1), else the interval. -/
recall packets.GnoInterval.check_and_new_spec (start «end» : U64) :
    packets.GnoInterval.check_and_new start «end» ⦃ r =>
      if «end».val ≤ start.val ∨ start.val = 0 then okPart r = none
      else ∃ g, r = .Ok g ∧ g.start.1 = start ∧ g.«end».1 = «end» ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.GnoInterval.check_and_new_spec`

/-- `MySerialize for GnoInterval`: appends `gnoEnc` (start, end, 8 bytes each). -/
recall packets.GnoInterval.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.GnoInterval) (buf : alloc.vec.Vec U8) (h : buf.length + 16 ≤ Usize.max) :
    packets.GnoInterval.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ gnoEnc (self.start.1.val, self.«end».1.val) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.GnoInterval.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- `MyDeserialize for GnoInterval`: `SIZE` is `Some(16)`. -/
recall packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = some 16#usize

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for GnoInterval`: reads 16 bytes (start, end). Unchecked: it panics on a
    shorter buffer (`deserialize_panics`); `parse` checks through `SIZE`. -/
recall packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun g => (g.start.1.val, g.«end».1.val)) =
        some (leNat (buf.val.take 8), leNat ((buf.val.drop 8).take 8)) ∧
      rest.val = buf.val.drop 16 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- `MyDeserialize for GnoInterval` panics on fewer than 16 bytes. -/
recall packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics
    (buf : io.ParseBuf) (h : buf.length < 16) :
    packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf = fail .panic

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.GnoInterval.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics`

/-! ### `struct Tag and its impls` -/

/-- `Tag::new(s)` of an empty string: `InvalidTag::Empty`. -/
recall packets.Tag.new_empty {T : Type} (into : core.convert.Into T (alloc.borrow.Cow Str String))
    (s : T) (c : alloc.borrow.Cow Str String) (h : into.into s = ok c) (he : strCowBytes c = []) :
    packets.Tag.new into s = ok (.Err .Empty)

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Tag.new_empty`

/-- `Tag::new(s)` of a string of more than 32 bytes (`Tag::MAX_LEN`): `InvalidTag::TooLong` with
    the length. -/
recall packets.Tag.new_too_long {T : Type} (into : core.convert.Into T (alloc.borrow.Cow Str String))
    (s : T) (c : alloc.borrow.Cow Str String) (h : into.into s = ok c)
    (hl : 32 < (strCowBytes c).length) (hfit : (strCowBytes c).length ≤ Usize.max) :
    packets.Tag.new into s ⦃ r => ∃ n : Usize, r = .Err (.TooLong n) ∧ n.val = (strCowBytes c).length ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Tag.new_too_long`

/-- `Tag::new(s)`, partially: if it returns a tag, the tag is `s.into()` and has 1 to 32 bytes.
    (The character checks, `[a-z_][a-z0-9_]*`, go through `Chars::next`, an Aeneas-library
    function without a model, so whether a 1–32-byte string is accepted is not stated.) -/
recall packets.Tag.new_ok {T : Type} (into : core.convert.Into T (alloc.borrow.Cow Str String))
    (s : T) (c : alloc.borrow.Cow Str String) (h : into.into s = ok c) (t : packets.Tag)
    (hr : packets.Tag.new into s = ok (.Ok t)) :
    t = c ∧ 1 ≤ (strCowBytes c).length ∧ (strCowBytes c).length ≤ 32

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Tag.new_ok`

/-- `as_str`: the tag's bytes. (Precondition: they fit in a `usize`, true of every real
    string.) -/
recall packets.Tag.as_str_spec (self : packets.Tag) (hfit : (strCowBytes self).length ≤ Usize.max) :
    packets.Tag.as_str self ⦃ s => s.val = strCowBytes self ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Tag.as_str_spec`

/-- `into_owned`: an owned tag with the same bytes. (Preconditions: the bytes are valid UTF-8,
    as those of every Rust `&str`, and fit in a `usize`.) -/
recall packets.Tag.into_owned_spec (self : packets.Tag) (hu : IsUtf8 (strCowBytes self))
    (hfit : (strCowBytes self).length ≤ Usize.max) :
    packets.Tag.into_owned self ⦃ t => (∃ o, t = .Owned o) ∧ strCowBytes t = strCowBytes self ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Tag.into_owned_spec`

/-- `Deref<Target = str> for Tag`: the tag's bytes. -/
recall packets.Tag.Insts.CoreOpsDerefDerefStr.deref_spec (self : packets.Tag)
    (hfit : (strCowBytes self).length ≤ Usize.max) :
    packets.Tag.Insts.CoreOpsDerefDerefStr.deref self ⦃ s => s.val = strCowBytes self ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Tag.Insts.CoreOpsDerefDerefStr.deref_spec`

/-- `TryFrom<&str> for Tag`: `Tag::new` of the borrowed string. -/
recall packets.Tag.Insts.CoreConvertTryFromSharedAStrInvalidTag.try_from_eq (s : Str) :
    packets.Tag.Insts.CoreConvertTryFromSharedAStrInvalidTag.try_from s =
      packets.Tag.new (core.convert.IntoFrom alloc.borrow.CowAStrString.Insts.CoreConvertFromSharedAStr) s

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Tag.Insts.CoreConvertTryFromSharedAStrInvalidTag.try_from_eq`

/-- `TryFrom<String> for Tag`: `Tag::new` of the owned string. -/
recall packets.TagStatic.Insts.CoreConvertTryFromStringInvalidTag.try_from_eq (s : String) :
    packets.TagStatic.Insts.CoreConvertTryFromStringInvalidTag.try_from s =
      packets.Tag.new (core.convert.IntoFrom alloc.borrow.CowAStrString.Insts.CoreConvertFromString) s

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.TagStatic.Insts.CoreConvertTryFromStringInvalidTag.try_from_eq`

/-! ### `struct Sid and its impls` -/

/-- `Sid::new(uuid)`: the UUID, no tag, no intervals. -/
recall packets.Sid.new_spec (uuid : Array U8 16#usize) :
    packets.Sid.new uuid ⦃ s => SidV.of s = ⟨uuid.val, none, []⟩ ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Sid.new_spec`

/-- `uuid`: the field. -/
recall packets.Sid.impl.uuid_eq (self : packets.Sid) :
    packets.Sid.impl.uuid self = ok self.uuid

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Sid.impl.uuid_eq`

/-- `tag`: the field. -/
recall packets.Sid.impl.tag_eq (self : packets.Sid) :
    packets.Sid.impl.tag self = ok self.tag

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Sid.impl.tag_eq`

/-- `intervals`: the intervals. -/
recall packets.Sid.impl.intervals_spec (self : packets.Sid) :
    packets.Sid.impl.intervals self ⦃ s => s.val = cowList self.intervals.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Sid.impl.intervals_spec`

/-- `with_interval(g)`: appends the interval (unchecked); nothing else changes. (Precondition:
    room for one more interval.) -/
recall packets.Sid.with_interval_spec (self : packets.Sid) (g : packets.GnoInterval)
    (h : (cowList self.intervals.1).length < Usize.max) :
    packets.Sid.with_interval self g ⦃ s =>
      SidV.of s = { SidV.of self with
        intervals := (SidV.of self).intervals ++ [(g.start.1.val, g.«end».1.val)] } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Sid.with_interval_spec`

/-- `with_intervals(v)`: replaces the intervals (unchecked); nothing else changes. -/
recall packets.Sid.with_intervals_spec (self : packets.Sid) (v : alloc.vec.Vec packets.GnoInterval) :
    packets.Sid.with_intervals self v ⦃ s =>
      SidV.of s = { SidV.of self with intervals := v.val.map (fun g => (g.start.1.val, g.«end».1.val)) } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Sid.with_intervals_spec`

/-- `with_tag(t)`: sets the tag. -/
recall packets.Sid.with_tag_eq (self : packets.Sid) (t : packets.Tag) :
    packets.Sid.with_tag self t = ok { self with tag := some t }

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Sid.with_tag_eq`

/-- `MySerialize for Sid`: appends the untagged format `sidEnc` (UUID, interval count,
    intervals). **The tag is not written** (the tagged format is written only by
    `ComBinlogDumpGtid`). -/
recall packets.Sid.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.Sid)
    (buf : alloc.vec.Vec U8) (h : buf.length + (sidEnc (SidV.of self)).length ≤ Usize.max) :
    packets.Sid.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ sidEnc (SidV.of self) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Sid.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- `MyDeserialize for Sid`: `SIZE` is `None`. -/
recall packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for Sid`: the untagged format (`sidRead`; the tag is `None`), exactly,
    whenever that reader returns. -/
recall packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64)
    (buf : io.ParseBuf) (r0 : Option SidV) (rest0 : List U8) (h : sidRead buf.val = .done r0 rest0) :
    packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map SidV.of = r0 ∧ rest.val = rest0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- **Crash path.** In the model, `MyDeserialize for Sid` panics where `sidRead` does: an
    interval count `n` from the input with `16 * n` above `usize::MAX` (`n ≥ 2^60`, unchecked
    multiplication). **Real Rust crashes earlier and more often**: `Vec::with_capacity(n)` runs
    first, before the count is checked against the input, so a large count aborts the process
    (out of memory), and `n ≥ 2^59` panics (capacity overflow), on a ~24-byte input; the model
    treats the allocation as free (allocation caveat) and returns an error for `n < 2^60`. The
    model's `16 * n` overflow is never reached in real Rust. -/
recall packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_overflow (h64 : Target64)
    (buf : io.ParseBuf) (e : Error) (h : sidRead buf.val = .panic e) :
    packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf = fail e

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_overflow`

/-- Round trip: the untagged format is read back, without the tag. -/
recall packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip (h64 : Target64)
    (s : packets.Sid) (tail : List U8) (buf : io.ParseBuf) (h : buf.val = sidEnc (SidV.of s) ++ tail) :
    packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map SidV.of = some { SidV.of s with tag := none } ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.Sid.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-! ### `struct ComBinlogDumpGtid and its impls` -/

/-- `ComBinlogDumpGtid::new(server_id)`: no flags, the server id, an empty file name, position
    0, no SIDs. -/
recall packets.ComBinlogDumpGtid.new_spec (server_id : U32) :
    packets.ComBinlogDumpGtid.new server_id ⦃ g =>
      GtidDump.of g = ⟨0, server_id.val, [], 0, []⟩ ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.new_spec`

/-- `server_id`: the field. -/
recall packets.ComBinlogDumpGtid.impl.server_id_eq (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.impl.server_id self = ok self.server_id.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.impl.server_id_eq`

/-- `flags`: the field. -/
recall packets.ComBinlogDumpGtid.impl.flags_eq (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.impl.flags self = ok self.flags.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.impl.flags_eq`

/-- `filename_raw`: the file name's effective bytes (at most the first `u32::MAX`). -/
recall packets.ComBinlogDumpGtid.filename_raw_spec (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.filename_raw self ⦃ s =>
      s.val = (cowList self.filename.1).take (2 ^ 32 - 1) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.filename_raw_spec`

/-- `filename`: the effective bytes as a string, lossily converted (exact on valid UTF-8). -/
recall packets.ComBinlogDumpGtid.impl.filename_spec (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.impl.filename self ⦃ c =>
      LossyUtf8Valid ((cowList self.filename.1).take (2 ^ 32 - 1)) c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.impl.filename_spec`

/-- `pos`: the field. -/
recall packets.ComBinlogDumpGtid.impl.pos_eq (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.impl.pos self = ok self.pos.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.impl.pos_eq`

/-- `sids`: the SIDs. -/
recall packets.ComBinlogDumpGtid.sids_spec (self : packets.ComBinlogDumpGtid) :
    packets.ComBinlogDumpGtid.sids self ⦃ s => s.val = cowList self.sid_block.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.sids_spec`

/-- `with_filename`: sets the file name (`filename.into()`); nothing else changes. -/
recall packets.ComBinlogDumpGtid.with_filename_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.ComBinlogDumpGtid) (x : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into x = ok c) :
    packets.ComBinlogDumpGtid.with_filename into self x ⦃ g =>
      GtidDump.of g = { GtidDump.of self with filename := cowList c } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.with_filename_spec`

/-- `with_server_id`: sets the server id; nothing else changes. -/
recall packets.ComBinlogDumpGtid.with_server_id_spec (self : packets.ComBinlogDumpGtid) (server_id : U32) :
    packets.ComBinlogDumpGtid.with_server_id self server_id ⦃ g =>
      GtidDump.of g = { GtidDump.of self with serverId := server_id.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.with_server_id_spec`

/-- `with_flags(flags)`: sets the flags, with `BINLOG_THROUGH_GTID` set exactly when there are
    SIDs; nothing else changes. -/
recall packets.ComBinlogDumpGtid.with_flags_spec (self : packets.ComBinlogDumpGtid)
    (flags : packets.BinlogDumpFlags) :
    packets.ComBinlogDumpGtid.with_flags self flags ⦃ g =>
      GtidDump.of g = { GtidDump.of self with
        flags := if cowList self.sid_block.1 = [] then andNot 16 flags.val BINLOG_THROUGH_GTID
                 else flags.val ||| BINLOG_THROUGH_GTID } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.with_flags_spec`

/-- `with_pos`: sets the position; nothing else changes. -/
recall packets.ComBinlogDumpGtid.with_pos_spec (self : packets.ComBinlogDumpGtid) (pos : U64) :
    packets.ComBinlogDumpGtid.with_pos self pos ⦃ g =>
      GtidDump.of g = { GtidDump.of self with pos := pos.val } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.with_pos_spec`

/-- `with_sid(sid)`: appends the SID and sets `BINLOG_THROUGH_GTID`; nothing else changes.
    (Preconditions: room for one more SID, and tags that fit in a `usize`, as every real
    string does: a borrowed block is cloned first.) -/
recall packets.ComBinlogDumpGtid.with_sid_spec (self : packets.ComBinlogDumpGtid) (sid : packets.Sid)
    (h : (cowList self.sid_block.1).length < Usize.max)
    (htags : ∀ s ∈ (GtidDump.of self).sids, ∀ t, s.tag = some t → t.length ≤ Usize.max) :
    packets.ComBinlogDumpGtid.with_sid self sid ⦃ g =>
      GtidDump.of g = { GtidDump.of self with
        flags := (GtidDump.of self).flags ||| BINLOG_THROUGH_GTID,
        sids := (GtidDump.of self).sids ++ [SidV.of sid] } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.with_sid_spec`

/-- `with_sids(sids)`: replaces the SIDs (`sids.into()`), with `BINLOG_THROUGH_GTID` set exactly
    when there are SIDs; nothing else changes. -/
recall packets.ComBinlogDumpGtid.with_sids_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice packets.Sid) (alloc.vec.Vec packets.Sid)))
    (self : packets.ComBinlogDumpGtid) (x : T)
    (c : alloc.borrow.Cow (Slice packets.Sid) (alloc.vec.Vec packets.Sid)) (h : into.into x = ok c) :
    packets.ComBinlogDumpGtid.with_sids into self x ⦃ g =>
      GtidDump.of g = { GtidDump.of self with
        flags := if cowList c = [] then andNot 16 (GtidDump.of self).flags BINLOG_THROUGH_GTID
                 else (GtidDump.of self).flags ||| BINLOG_THROUGH_GTID,
        sids := (cowList c).map SidV.of } ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.with_sids_spec`

/-- `MySerialize for ComBinlogDumpGtid`: appends `gtidDumpEnc`: the file name with a 4-byte
    length, the position, `data_size` and the SID block (tagged format iff some SID has a tag;
    `data_size` and the block are sent even without `BINLOG_THROUGH_GTID`). Precondition: the
    SID block is shorter than `2^32` bytes; otherwise **crate behaviour**: `data_size` is
    computed with saturating (and truncating `as u32`) arithmetic and no longer matches the
    block. -/
recall packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.ComBinlogDumpGtid) (buf : alloc.vec.Vec U8)
    (hblk : (sidBlock (GtidDump.of self).sids).length < 2 ^ 32)
    (h : buf.length + (gtidDumpEnc (GtidDump.of self)).length ≤ Usize.max) :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ gtidDumpEnc (GtidDump.of self) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- `MyDeserialize for ComBinlogDumpGtid`: `SIZE` is `None`. -/
recall packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for ComBinlogDumpGtid`: exactly `gtidDumpRead` whenever that reader returns.
    It does in the untagged format, and in the tagged format until it meets a non-empty tag
    (`unknown`: the tag's character check is not modelled, see `sidTaggedRead`).
    It is never `unknown` in the untagged format (`Defs.sidsRead_untagged_ne_unknown`), and in
    the tagged format only through a tag of 1–32 valid UTF-8 bytes
    (`Defs.gtidDumpRead_unknown`, `Defs.sidTaggedRead_unknown_iff`).
    **Allocation caveat (GTID).** The SID count comes from the input (up to `2^56`) and is passed
    to `Vec::with_capacity` before any SID is read, which the model treats as free: in real Rust
    a 31-byte packet announcing `2^56` SIDs makes the reader try to allocate `2^56` SIDs and
    abort the process (out of memory, observed), where the model returns an error. The same
    holds for each SID's interval count (`Sid::deserialize_overflow`). -/
recall packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (h64 : Target64) (buf : io.ParseBuf) (r0 : Option GtidDump) (rest0 : List U8)
    (h : gtidDumpRead buf.val = .done r0 rest0) :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map GtidDump.of = r0 ∧ rest.val = rest0 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- **Crash path.** `MyDeserialize for ComBinlogDumpGtid` panics where `gtidDumpRead` does: a SID
    whose interval count `n` has `16 * n` above `usize::MAX` (see `Sid::deserialize_overflow`:
    real Rust crashes earlier, in `Vec::with_capacity`). -/
recall packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics
    (h64 : Target64) (buf : io.ParseBuf) (e : Error) (h : gtidDumpRead buf.val = .panic e) :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf = fail e

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_panics`

/-- Round trip (untagged format): a request without tags, with known flags, a file name shorter
    than `2^32` bytes and a SID block shorter than `2^32` bytes, is read back from
    `gtidDumpEnc`. (With a tag, see `deserialize_spec`.) -/
recall packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (h64 : Target64) (g : packets.ComBinlogDumpGtid)
    (hnotag : gtidTagged (GtidDump.of g).sids = false)
    (hf : (GtidDump.of g).flags &&& binlogDumpFlagsAll = (GtidDump.of g).flags)
    (hfn : (GtidDump.of g).filename.length < 2 ^ 32)
    (hblk : (sidBlock (GtidDump.of g).sids).length < 2 ^ 32)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = gtidDumpEnc (GtidDump.of g) ++ tail) :
    packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map GtidDump.of = some (GtidDump.of g) ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.ComBinlogDumpGtid.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

/-! ### `struct SemiSyncAckPacket and its impls` -/

/-- `SemiSyncAckPacket::new(position, filename)`: the position and the file name
    (`filename.into()`). -/
recall packets.SemiSyncAckPacket.new_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (position : U64) (filename : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into filename = ok c) :
    packets.SemiSyncAckPacket.new into position filename ⦃ p =>
      p.position.1 = position ∧ p.filename.1 = c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SemiSyncAckPacket.new_spec`

/-- `with_position`: sets the position; nothing else changes. -/
recall packets.SemiSyncAckPacket.with_position_spec (self : packets.SemiSyncAckPacket) (position : U64) :
    packets.SemiSyncAckPacket.with_position self position ⦃ p =>
      p.position.1 = position ∧ p.filename = self.filename ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SemiSyncAckPacket.with_position_spec`

/-- `with_filename`: sets the file name; nothing else changes. -/
recall packets.SemiSyncAckPacket.with_filename_spec {T : Type}
    (into : core.convert.Into T (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (self : packets.SemiSyncAckPacket) (filename : T) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h : into.into filename = ok c) :
    packets.SemiSyncAckPacket.with_filename into self filename ⦃ p =>
      p.position = self.position ∧ p.filename.1 = c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SemiSyncAckPacket.with_filename_spec`

/-- `position`: the field. -/
recall packets.SemiSyncAckPacket.impl.position_eq (self : packets.SemiSyncAckPacket) :
    packets.SemiSyncAckPacket.impl.position self = ok self.position.1

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SemiSyncAckPacket.impl.position_eq`

/-- `filename_raw`: the file name. -/
recall packets.SemiSyncAckPacket.filename_raw_spec (self : packets.SemiSyncAckPacket) :
    packets.SemiSyncAckPacket.filename_raw self ⦃ s => s.val = cowList self.filename.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SemiSyncAckPacket.filename_raw_spec`

/-- `filename`: the file name as a string, lossily converted (exact on valid UTF-8). -/
recall packets.SemiSyncAckPacket.impl.filename_spec (self : packets.SemiSyncAckPacket) :
    packets.SemiSyncAckPacket.impl.filename self ⦃ c => LossyUtf8Valid (cowList self.filename.1) c ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SemiSyncAckPacket.impl.filename_spec`

/-- `MySerialize for SemiSyncAckPacket`: appends `semiSyncAckEnc` (`0xEF`, the position, the
    file name). -/
recall packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.SemiSyncAckPacket) (buf : alloc.vec.Vec U8)
    (h : buf.length + 9 + (cowList self.filename.1).length ≤ Usize.max) :
    packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ semiSyncAckEnc self.position.1.val (cowList self.filename.1) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- `MyDeserialize for SemiSyncAckPacket`: `SIZE` is `None`. -/
recall packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq`

/-- `MyDeserialize for SemiSyncAckPacket`: total; `semiSyncAckRead` (9 bytes, then the file name
    is the rest of the input). -/
recall packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (buf : io.ParseBuf) :
    packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun p => (p.position.1.val, cowList p.filename.1)), rest.val) =
        semiSyncAckRead buf.val ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec`

/-- Round trip: `semiSyncAckEnc` is read back (the file name takes the rest of the input). -/
recall packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip
    (p : packets.SemiSyncAckPacket) (buf : io.ParseBuf)
    (h : buf.val = semiSyncAckEnc p.position.1.val (cowList p.filename.1)) :
    packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      (okPart r).map (fun q => (q.position.1.val, cowList q.filename.1)) =
        some (p.position.1.val, cowList p.filename.1) ∧ rest.val = [] ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms packets.SemiSyncAckPacket.Insts.Mysql_commonProtoMyDeserializeDeTuple.roundtrip`

end mysql_common
