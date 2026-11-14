import Proofs.Packets.SessionStateChange.SessionStateChange
import Proofs.Packets.SessionStateChange.Gtids
import Proofs.Packets.SessionStateChange.Schema
import Proofs.Packets.SessionStateChange.SystemVariable
import Proofs.Packets.SessionStateChange.TransactionCharacteristics
import Proofs.Packets.SessionStateChange.TransactionState
import Proofs.Packets.SessionStateChange.Unsupported

/-!
# `src/packets/session_state_change.rs`
    The decoded session state changes of an OK packet (`SessionStateChange` and its variants'
    types `Gtids`, `Schema`, `SystemVariable`, `TransactionCharacteristics`, `TransactionState`,
    `Unsupported`): construction, the raw and lossy accessors, `into_owned`, the readers of the
    `data` of a session state entry, and serialization. The entries themselves
    (`SessionStateInfo`, `OkPacket::session_state_info`) are in `Specs/Packets/StmtBinlog.lean`.

    **Patches.** 65 (combinators as `match`; the three system-variable loops as recursion; a
    private `SystemVariable::to_owned_static` for `into_owned` of the vector; `== &b"1"[..]`), 64
    (`RawBytes::as_str` through `trusted::from_utf8_lossy`). The statements are about the patched
    code.

    **Configuration.** As in `Specs/Io.lean`. The readers take `Target64` (length-encoded
    strings).

    **Allocation caveat.** As in `Specs/Row.lean`.

    **Definitions used.** `Defs/SessionState.lean` (`SsChange`, `SsChange.of`, `SsChange.type?`,
    `ssChangeEnc`, `ssChangeRead`, `sysVarRead`, `sysVarsFuel`, `gtidsRead`, `lenencAs`),
    `Defs/CmdPackets.lean` (`LossyUtf8Valid`), `Defs/LenEnc.lean`, `Defs/Bytes.lean`.

    **Trusted axioms.** `Trusted.utf8LossyOwned` (the `as_str`/`*_str` accessors: exact only on
    valid UTF-8), and the opaque `io::Error` constructors (asserting nothing).

    **Not covered.** Derived `Clone`/`PartialEq`/`Hash`/`Debug`; the private recursive helpers
    (`system_variables_to_owned`, `deserialize_system_variables`, `serialize_system_variables`,
    `SystemVariable::to_owned_static`), covered through their callers.

    **Behaviour to note.**
    * A system-variable entry is read as name/value pairs until the data is exhausted (MySQL sends
      one per entry), so the reader does not stop after one pair.
    * `SESSION_TRACK_STATE_CHANGE` gives `IsTracked(true)` exactly for the string `"1"`; any other
      well-formed string (`"0"` or not) is `false`; a malformed length-encoded string is an
      error.
    * The GTID encoding-specification byte is skipped without being checked (only `0` is
      defined).
    * `Unsupported` is never produced by the reader (every type code it accepts has a variant);
      the bytes of the data after the change are ignored by `SessionStateInfo::decode`.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `enum SessionStateChange and its impls` -/

/-- `into_owned`: the same change. -/
recall packets.session_state_change.SessionStateChange.into_owned_spec (self : packets.session_state_change.SessionStateChange) :
    packets.session_state_change.SessionStateChange.into_owned self ⦃ c => SsChange.of c = SsChange.of self ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SessionStateChange.into_owned_spec
/-- `MyDeserialize for SessionStateChange`: `SIZE` is `None`. -/
recall packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.SIZE_eq :
    packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.SIZE_eq
/-- `MyDeserialize for SessionStateChange` with the type `ty`: total; `ssChangeRead ty` (the
    protocol's `data` layout of that type; system variables until the input is exhausted;
    `IsTracked` is `true` exactly for `"1"`). -/
recall packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.deserialize_spec
    (h64 : Target64) (ty : constants.SessionStateType) (buf : io.ParseBuf) :
    packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.deserialize ty buf ⦃ r rest =>
      ((okPart r).map SsChange.of, rest.val) = ssChangeRead ty buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.deserialize_spec
/-- Round trip: the `data` of a change (`ssChangeEnc`), read with the change's type, gives the
    change back (for system variables the data must end there, as the reader takes pairs until
    the input is exhausted). `Unsupported` has no type and is never read. -/
recall packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.roundtrip
    (h64 : Target64) (c : packets.session_state_change.SessionStateChange) (ty : constants.SessionStateType)
    (hty : (SsChange.of c).type? = some ty)
    (tail : List U8) (htail : tail = [] ∨ ty ≠ .SESSION_TRACK_SYSTEM_VARIABLES) (buf : io.ParseBuf)
    (h : buf.val = ssChangeEnc (SsChange.of c) ++ tail) :
    packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.deserialize ty buf ⦃ r rest =>
      (okPart r).map SsChange.of = some (SsChange.of c) ∧ rest.val = tail ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMyDeserializeDeSessionStateType.roundtrip
/-- `MySerialize for SessionStateChange`: appends `ssChangeEnc` (the protocol's `data`; for
    `IsTracked`, `"1"` or `"0"`). -/
recall packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.session_state_change.SessionStateChange) (buf : alloc.vec.Vec U8)
    (h : buf.length + (ssChangeEnc (SsChange.of self)).length ≤ Usize.max) :
    packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ ssChangeEnc (SsChange.of self) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SessionStateChange.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `struct Gtids and its impls` -/

/-- `Gtids::new(v)`: wraps `v.into()`. -/
recall packets.session_state_change.Gtids.new_spec {X : Type}
    (into : core.convert.Into X (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (v : X) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into v = ok c) :
    packets.session_state_change.Gtids.new into v ⦃ x => x.1 = c ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Gtids.new_spec
/-- `as_bytes`: the raw GTID set. -/
recall packets.session_state_change.Gtids.as_bytes_spec (self : packets.session_state_change.Gtids) :
    packets.session_state_change.Gtids.as_bytes self ⦃ s => s.val = cowList self.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Gtids.as_bytes_spec
/-- `as_str`: the GTID set as a string, lossily converted (exact on valid UTF-8). -/
recall packets.session_state_change.Gtids.as_str_spec (self : packets.session_state_change.Gtids) :
    packets.session_state_change.Gtids.as_str self ⦃ c => LossyUtf8Valid (cowList self.1) c ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.utf8LossyOwned, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Gtids.as_str_spec
/-- `into_owned`: the same bytes. -/
recall packets.session_state_change.Gtids.into_owned_spec (self : packets.session_state_change.Gtids) :
    packets.session_state_change.Gtids.into_owned self ⦃ x => cowList x.1 = cowList self.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Gtids.into_owned_spec
/-- `MyDeserialize for Gtids`: `SIZE` is `None`. -/
recall packets.session_state_change.Gtids.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.session_state_change.Gtids.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Gtids.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for Gtids`: total; `gtidsRead` (the encoding byte skipped unchecked, then a length-encoded string). -/
recall packets.session_state_change.Gtids.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64)
    (buf : io.ParseBuf) :
    packets.session_state_change.Gtids.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun x => cowList x.1), rest.val) = gtidsRead buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Gtids.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MySerialize for Gtids`: appends the encoding byte `0`, then the GTID set as a length-encoded string. -/
recall packets.session_state_change.Gtids.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.session_state_change.Gtids)
    (buf : alloc.vec.Vec U8) (h : buf.length + ((byte 0 :: lenencStr (cowList self.1))).length ≤ Usize.max) :
    packets.session_state_change.Gtids.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ (byte 0 :: lenencStr (cowList self.1)) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Gtids.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `struct Schema and its impls` -/

/-- `Schema::new(v)`: wraps `v.into()`. -/
recall packets.session_state_change.Schema.new_spec {X : Type}
    (into : core.convert.Into X (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (v : X) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into v = ok c) :
    packets.session_state_change.Schema.new into v ⦃ x => x.1 = c ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Schema.new_spec
/-- `as_bytes`: the raw schema name. -/
recall packets.session_state_change.Schema.as_bytes_spec (self : packets.session_state_change.Schema) :
    packets.session_state_change.Schema.as_bytes self ⦃ s => s.val = cowList self.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Schema.as_bytes_spec
/-- `as_str`: the schema name as a string, lossily converted (exact on valid UTF-8). -/
recall packets.session_state_change.Schema.as_str_spec (self : packets.session_state_change.Schema) :
    packets.session_state_change.Schema.as_str self ⦃ c => LossyUtf8Valid (cowList self.1) c ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.utf8LossyOwned, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Schema.as_str_spec
/-- `into_owned`: the same bytes. -/
recall packets.session_state_change.Schema.into_owned_spec (self : packets.session_state_change.Schema) :
    packets.session_state_change.Schema.into_owned self ⦃ x => cowList x.1 = cowList self.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Schema.into_owned_spec
/-- `MyDeserialize for Schema`: `SIZE` is `None`. -/
recall packets.session_state_change.Schema.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.session_state_change.Schema.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Schema.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for Schema`: total; a length-encoded string (`checkedLenencStr`). -/
recall packets.session_state_change.Schema.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64)
    (buf : io.ParseBuf) :
    packets.session_state_change.Schema.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun x => cowList x.1), rest.val) = checkedLenencStr buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Schema.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MySerialize for Schema`: appends the schema name as a length-encoded string. -/
recall packets.session_state_change.Schema.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.session_state_change.Schema)
    (buf : alloc.vec.Vec U8) (h : buf.length + (lenencStr (cowList self.1)).length ≤ Usize.max) :
    packets.session_state_change.Schema.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ lenencStr (cowList self.1) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Schema.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `struct SystemVariable and its impls` -/

/-- `SystemVariable::new(name, value)`: wraps `name.into()` and `value.into()`. -/
recall packets.session_state_change.SystemVariable.new_spec {X Y : Type}
    (into1 : core.convert.Into X (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (into2 : core.convert.Into Y (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (n : X) (v : Y) (c1 c2 : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8))
    (h1 : into1.into n = ok c1) (h2 : into2.into v = ok c2) :
    packets.session_state_change.SystemVariable.new into1 into2 n v ⦃ x => x.«name».1 = c1 ∧ x.value.1 = c2 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SystemVariable.new_spec
/-- `name_bytes`: the raw name. -/
recall packets.session_state_change.SystemVariable.name_bytes_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.name_bytes self ⦃ s => s.val = cowList self.«name».1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SystemVariable.name_bytes_spec
/-- `name_str`: the name as a string, lossily converted (exact on valid UTF-8). -/
recall packets.session_state_change.SystemVariable.name_str_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.name_str self ⦃ c => LossyUtf8Valid (cowList self.«name».1) c ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.utf8LossyOwned, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SystemVariable.name_str_spec
/-- `value_bytes`: the raw value. -/
recall packets.session_state_change.SystemVariable.value_bytes_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.value_bytes self ⦃ s => s.val = cowList self.value.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SystemVariable.value_bytes_spec
/-- `value_str`: the value as a string, lossily converted (exact on valid UTF-8). -/
recall packets.session_state_change.SystemVariable.value_str_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.value_str self ⦃ c => LossyUtf8Valid (cowList self.value.1) c ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.utf8LossyOwned, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SystemVariable.value_str_spec
/-- `into_owned`: the same name and value. -/
recall packets.session_state_change.SystemVariable.into_owned_spec (self : packets.session_state_change.SystemVariable) :
    packets.session_state_change.SystemVariable.into_owned self ⦃ x =>
      cowList x.«name».1 = cowList self.«name».1 ∧ cowList x.value.1 = cowList self.value.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SystemVariable.into_owned_spec
/-- `MyDeserialize for SystemVariable`: `SIZE` is `None`. -/
recall packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for SystemVariable`: total; `sysVarRead` (the name, then the value, as
    length-encoded strings). -/
recall packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    (h64 : Target64) (buf : io.ParseBuf) :
    packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun x => (cowList x.«name».1, cowList x.value.1)), rest.val) = sysVarRead buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MySerialize for SystemVariable`: appends the name, then the value, as length-encoded
    strings. -/
recall packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMySerialize.serialize_spec
    (self : packets.session_state_change.SystemVariable) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lenencStr (cowList self.«name».1) ++ lenencStr (cowList self.value.1)).length ≤ Usize.max) :
    packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ lenencStr (cowList self.«name».1) ++ lenencStr (cowList self.value.1) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.SystemVariable.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `struct TransactionCharacteristics and its impls` -/

/-- `TransactionCharacteristics::new(v)`: wraps `v.into()`. -/
recall packets.session_state_change.TransactionCharacteristics.new_spec {X : Type}
    (into : core.convert.Into X (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (v : X) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into v = ok c) :
    packets.session_state_change.TransactionCharacteristics.new into v ⦃ x => x.1 = c ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionCharacteristics.new_spec
/-- `as_bytes`: the raw value. -/
recall packets.session_state_change.TransactionCharacteristics.as_bytes_spec (self : packets.session_state_change.TransactionCharacteristics) :
    packets.session_state_change.TransactionCharacteristics.as_bytes self ⦃ s => s.val = cowList self.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionCharacteristics.as_bytes_spec
/-- `as_str`: the value as a string, lossily converted (exact on valid UTF-8). -/
recall packets.session_state_change.TransactionCharacteristics.as_str_spec (self : packets.session_state_change.TransactionCharacteristics) :
    packets.session_state_change.TransactionCharacteristics.as_str self ⦃ c => LossyUtf8Valid (cowList self.1) c ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.utf8LossyOwned, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionCharacteristics.as_str_spec
/-- `into_owned`: the same bytes. -/
recall packets.session_state_change.TransactionCharacteristics.into_owned_spec (self : packets.session_state_change.TransactionCharacteristics) :
    packets.session_state_change.TransactionCharacteristics.into_owned self ⦃ x => cowList x.1 = cowList self.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionCharacteristics.into_owned_spec
/-- `MyDeserialize for TransactionCharacteristics`: `SIZE` is `None`. -/
recall packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for TransactionCharacteristics`: total; a length-encoded string (`checkedLenencStr`). -/
recall packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64)
    (buf : io.ParseBuf) :
    packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun x => cowList x.1), rest.val) = checkedLenencStr buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MySerialize for TransactionCharacteristics`: appends the value as a length-encoded string. -/
recall packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.session_state_change.TransactionCharacteristics)
    (buf : alloc.vec.Vec U8) (h : buf.length + (lenencStr (cowList self.1)).length ≤ Usize.max) :
    packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ lenencStr (cowList self.1) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `struct TransactionState and its impls` -/

/-- `TransactionState::new(v)`: wraps `v.into()`. -/
recall packets.session_state_change.TransactionState.new_spec {X : Type}
    (into : core.convert.Into X (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (v : X) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into v = ok c) :
    packets.session_state_change.TransactionState.new into v ⦃ x => x.1 = c ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionState.new_spec
/-- `as_bytes`: the raw value. -/
recall packets.session_state_change.TransactionState.as_bytes_spec (self : packets.session_state_change.TransactionState) :
    packets.session_state_change.TransactionState.as_bytes self ⦃ s => s.val = cowList self.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionState.as_bytes_spec
/-- `as_str`: the value as a string, lossily converted (exact on valid UTF-8). -/
recall packets.session_state_change.TransactionState.as_str_spec (self : packets.session_state_change.TransactionState) :
    packets.session_state_change.TransactionState.as_str self ⦃ c => LossyUtf8Valid (cowList self.1) c ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.utf8LossyOwned, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionState.as_str_spec
/-- `into_owned`: the same bytes. -/
recall packets.session_state_change.TransactionState.into_owned_spec (self : packets.session_state_change.TransactionState) :
    packets.session_state_change.TransactionState.into_owned self ⦃ x => cowList x.1 = cowList self.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionState.into_owned_spec
/-- `MyDeserialize for TransactionState`: `SIZE` is `None`. -/
recall packets.session_state_change.TransactionState.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.session_state_change.TransactionState.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionState.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for TransactionState`: total; a length-encoded string (`checkedLenencStr`). -/
recall packets.session_state_change.TransactionState.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64)
    (buf : io.ParseBuf) :
    packets.session_state_change.TransactionState.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun x => cowList x.1), rest.val) = checkedLenencStr buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionState.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MySerialize for TransactionState`: appends the value as a length-encoded string. -/
recall packets.session_state_change.TransactionState.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.session_state_change.TransactionState)
    (buf : alloc.vec.Vec U8) (h : buf.length + (lenencStr (cowList self.1)).length ≤ Usize.max) :
    packets.session_state_change.TransactionState.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ lenencStr (cowList self.1) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.TransactionState.Insts.Mysql_commonProtoMySerialize.serialize_spec
/-! ### `struct Unsupported and its impls` -/

/-- `Unsupported::new(v)`: wraps `v.into()`. -/
recall packets.session_state_change.Unsupported.new_spec {X : Type}
    (into : core.convert.Into X (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (v : X) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into v = ok c) :
    packets.session_state_change.Unsupported.new into v ⦃ x => x.1 = c ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Unsupported.new_spec
/-- `as_bytes`: the raw value. -/
recall packets.session_state_change.Unsupported.as_bytes_spec (self : packets.session_state_change.Unsupported) :
    packets.session_state_change.Unsupported.as_bytes self ⦃ s => s.val = cowList self.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Unsupported.as_bytes_spec
/-- `as_str`: the value as a string, lossily converted (exact on valid UTF-8). -/
recall packets.session_state_change.Unsupported.as_str_spec (self : packets.session_state_change.Unsupported) :
    packets.session_state_change.Unsupported.as_str self ⦃ c => LossyUtf8Valid (cowList self.1) c ⦄

/-- [propext, Classical.choice, Quot.sound, Trusted.utf8LossyOwned, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Unsupported.as_str_spec
/-- `into_owned`: the same bytes. -/
recall packets.session_state_change.Unsupported.into_owned_spec (self : packets.session_state_change.Unsupported) :
    packets.session_state_change.Unsupported.into_owned self ⦃ x => cowList x.1 = cowList self.1 ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Unsupported.into_owned_spec
/-- `MyDeserialize for Unsupported`: `SIZE` is `None`. -/
recall packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none

/-- does not depend on any axioms -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq
/-- `MyDeserialize for Unsupported`: total; a length-encoded string (`checkedLenencStr`). -/
recall packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64)
    (buf : io.ParseBuf) :
    packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun x => cowList x.1), rest.val) = checkedLenencStr buf.val ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
/-- `MySerialize for Unsupported`: appends the value as a length-encoded string. -/
recall packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.session_state_change.Unsupported)
    (buf : alloc.vec.Vec U8) (h : buf.length + (lenencStr (cowList self.1)).length ≤ Usize.max) :
    packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ lenencStr (cowList self.1) ⦄

/-- [propext, Classical.choice, Quot.sound, core.io.error.Error, core.io.error.Error.ofMsg] -/
#guard_msgs (whitespace := lax, substring := true) in #print axioms packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMySerialize.serialize_spec
end mysql_common
