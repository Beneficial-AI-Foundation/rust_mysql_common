import Defs
import Proofs.Util.BinlogEvGtid
import Proofs.Binlog.Consts.EventType
import Proofs.Misc.LenencIntLen
import Proofs.Misc.Raw.Array
import Proofs.Misc.Raw.Int.LeU56
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Misc.Raw.Int.LenEnc
import Proofs.Misc.Raw.ParseBuf

/-! Statements for `struct GtidEvent and its impls` (spec file: `Specs/Binlog/Events/GtidEvent.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs mysql_common.PBUtil

namespace mysql_common

/-- `new(sid, gno)`: untagged, with the logical-clock part, everything else 0 (server versions 0, not `UNDEFINED_SERVER_VERSION`). -/
theorem binlog.events.gtid_event.GtidEvent.new_spec (sid : Array U8 16#usize) (gno : U64) :
    binlog.events.gtid_event.GtidEvent.new sid gno ⦃ e => gtidView e =
      { flags := 0, sid := sid.val, gno := gno.val, lc := true, lastCommitted := 0,
        sequenceNumber := 0, immediateCommitTs := 0, originalCommitTs := 0, txLength := 0,
        immediateServerVersion := 0, originalServerVersion := 0 } ∧
      e.tag = none ∧ e.serialization_version.val = 0 ∧ e.commit_group_ticket.val = 0 ⦄ := by
  unfold binlog.events.gtid_event.GtidEvent.new
  step*
  simp_all [gtidView, binlog.events.gtid_event.GtidEvent.COMMIT_GROUP_TICKET_UNSET]

/-- `new_tagged(sid, tag, gno)`: tagged (serialization version 2), no logical-clock part, server versions `UNDEFINED_SERVER_VERSION`. -/
theorem binlog.events.gtid_event.GtidEvent.new_tagged_spec (sid : Array U8 16#usize) (tag : packets.Tag) (gno : U64) :
    binlog.events.gtid_event.GtidEvent.new_tagged sid tag gno ⦃ e => gtidView e =
      { flags := 0, sid := sid.val, gno := gno.val, lc := false, lastCommitted := 0,
        sequenceNumber := 0, immediateCommitTs := 0, originalCommitTs := 0, txLength := 0,
        immediateServerVersion := undefinedServerVersion, originalServerVersion := undefinedServerVersion } ∧
      e.tag = some tag ∧ e.serialization_version.val = 2 ∧ e.commit_group_ticket.val = 0 ⦄ := by
  unfold binlog.events.gtid_event.GtidEvent.new_tagged
  step*
  simp_all [gtidView, binlog.events.gtid_event.GtidEvent.COMMIT_GROUP_TICKET_UNSET, binlog.events.gtid_event.GtidEvent.UNDEFINED_SERVER_VERSION,
    binlog.events.gtid_event.GtidEvent.TAGGED_SERIALIZATION_VERSION_V2, undefinedServerVersion]

/-- `is_tagged`: whether there is a tag. -/
theorem binlog.events.gtid_event.GtidEvent.is_tagged_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.is_tagged e = ok e.tag.isSome := by
  unfold binlog.events.gtid_event.GtidEvent.is_tagged; rfl

/-- `event_type`: `GTID_TAGGED_LOG_EVENT` if tagged, else `GTID_EVENT`. -/
theorem binlog.events.gtid_event.GtidEvent.event_type_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.event_type e = ok (if e.tag.isSome then .GTID_TAGGED_LOG_EVENT else .GTID_EVENT) := by
  unfold binlog.events.gtid_event.GtidEvent.event_type
  cases e.tag <;> rfl

/-- `with_flags`. -/
theorem binlog.events.gtid_event.GtidEvent.with_flags_spec (e : binlog.events.gtid_event.GtidEvent) (f : binlog.consts.GtidFlags) :
    binlog.events.gtid_event.GtidEvent.with_flags e f = ok { e with flags := (f, ()) } := by
  unfold binlog.events.gtid_event.GtidEvent.with_flags
  simp only [binlog.consts.GtidFlags.bits, misc.raw.flags.RawFlags.new]
  exact (bind_tc_ok _ _).trans (bind_tc_ok _ _)

/-- `flags_raw`: all the flag bits. -/
theorem binlog.events.gtid_event.GtidEvent.flags_raw_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.flags_raw e = ok e.flags.1 := by
  unfold binlog.events.gtid_event.GtidEvent.flags_raw; rfl

/-- `flags`: the known flag bits. -/
theorem binlog.events.gtid_event.GtidEvent.impl.flags_spec (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.flags e ⦃ f => f.val = e.flags.1.val &&& gtidFlagsAll ⦄ := by
  unfold binlog.events.gtid_event.GtidEvent.impl.flags
  rw [misc.raw.flags.RawFlags.get_eq]
  simp [binlog.consts.GtidFlags.Insts.BitflagsTraitsFlagsU8.FLAGS,
    bitflags.traits.Flag.new, binlog.consts.GtidFlags.MAY_HAVE_SBR, binlog.consts.GtidFlags.Insts.BitflagsTraitsFlagsU8.bits,
    binlog.consts.GtidFlags.bits, binlog.consts.GtidFlags.Insts.BitflagsTraitsFlagsU8.from_bits_retain,
    binlog.consts.GtidFlags.from_bits_retain, U8.Insts.BitflagsTraitsBits.EMPTY, gtidFlagsAll,
    U8.Insts.CoreOpsBitBitOrU8U8.bitor, U8.Insts.CoreOpsBitBitAndU8U8.bitand]

/-- `with_sid`. -/
theorem binlog.events.gtid_event.GtidEvent.with_sid_eq (e : binlog.events.gtid_event.GtidEvent) (s : Array U8 16#usize) :
    binlog.events.gtid_event.GtidEvent.with_sid e s = ok { e with sid := s } := by
  unfold binlog.events.gtid_event.GtidEvent.with_sid; rfl

/-- `sid`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.sid_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.sid e = ok e.sid := by
  unfold binlog.events.gtid_event.GtidEvent.impl.sid; rfl

/-- `with_gno`. -/
theorem binlog.events.gtid_event.GtidEvent.with_gno_eq (e : binlog.events.gtid_event.GtidEvent) (g : U64) :
    binlog.events.gtid_event.GtidEvent.with_gno e g = ok { e with gno := (g, ()) } := by
  unfold binlog.events.gtid_event.GtidEvent.with_gno; rw [misc.raw._const.RawConst.new_eq]; exact bind_tc_ok _ _

/-- `gno`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.gno_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.gno e = ok e.gno.1 := by
  unfold binlog.events.gtid_event.GtidEvent.impl.gno; rfl

/-- `tag`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.tag_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.tag e = ok e.tag := by
  unfold binlog.events.gtid_event.GtidEvent.impl.tag; rfl

/-- `with_tag`: the tag, and serialization version 2. -/
theorem binlog.events.gtid_event.GtidEvent.with_tag_eq (e : binlog.events.gtid_event.GtidEvent) (t : packets.Tag) :
    binlog.events.gtid_event.GtidEvent.with_tag e t = ok { e with tag := some t, serialization_version := 2#u8 } := by
  unfold binlog.events.gtid_event.GtidEvent.with_tag; simp [binlog.events.gtid_event.GtidEvent.TAGGED_SERIALIZATION_VERSION_V2]

/-- `lc_typecode`: 2 iff the logical-clock part is present. -/
theorem binlog.events.gtid_event.GtidEvent.impl.lc_typecode_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.lc_typecode e = ok (if e.lc_typecode.isSome then some 2#u8 else none) := by
  unfold binlog.events.gtid_event.GtidEvent.impl.lc_typecode
  cases e.lc_typecode <;> simp [core.option.Option.as_ref, misc.raw.int.ConstU8.value]

/-- `with_lc_typecode`: adds the logical-clock part. -/
theorem binlog.events.gtid_event.GtidEvent.with_lc_typecode_spec (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.with_lc_typecode e ⦃ e' => gtidView e' = { gtidView e with lc := true } ∧ e'.tag = e.tag ⦄ := by
  unfold binlog.events.gtid_event.GtidEvent.with_lc_typecode
  step*
  simp [gtidView]

/-- `with_last_committed`. -/
theorem binlog.events.gtid_event.GtidEvent.with_last_committed_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_last_committed e x = ok { e with last_committed := (x, ()) } := by
  unfold binlog.events.gtid_event.GtidEvent.with_last_committed; rw [misc.raw.int.RawInt.new_eq]; exact bind_tc_ok _ _

/-- `last_committed`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.last_committed_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.last_committed e = ok e.last_committed.1 := by
  unfold binlog.events.gtid_event.GtidEvent.impl.last_committed; rfl

/-- `with_sequence_number`. -/
theorem binlog.events.gtid_event.GtidEvent.with_sequence_number_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_sequence_number e x = ok { e with sequence_number := (x, ()) } := by
  unfold binlog.events.gtid_event.GtidEvent.with_sequence_number; rw [misc.raw.int.RawInt.new_eq]; exact bind_tc_ok _ _

/-- `sequence_number`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.sequence_number_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.sequence_number e = ok e.sequence_number.1 := by
  unfold binlog.events.gtid_event.GtidEvent.impl.sequence_number; rfl

/-- `with_immediate_commit_timestamp` (stored as given; 56 bits are written). -/
theorem binlog.events.gtid_event.GtidEvent.with_immediate_commit_timestamp_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_immediate_commit_timestamp e x = ok { e with immediate_commit_timestamp := (x, ()) } := by
  unfold binlog.events.gtid_event.GtidEvent.with_immediate_commit_timestamp; rw [misc.raw.int.RawInt.new_eq]; exact bind_tc_ok _ _

/-- `immediate_commit_timestamp`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.immediate_commit_timestamp_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.immediate_commit_timestamp e = ok e.immediate_commit_timestamp.1 := by
  unfold binlog.events.gtid_event.GtidEvent.impl.immediate_commit_timestamp; rfl

/-- `with_original_commit_timestamp`. -/
theorem binlog.events.gtid_event.GtidEvent.with_original_commit_timestamp_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_original_commit_timestamp e x = ok { e with original_commit_timestamp := (x, ()) } := by
  unfold binlog.events.gtid_event.GtidEvent.with_original_commit_timestamp; rw [misc.raw.int.RawInt.new_eq]; exact bind_tc_ok _ _

/-- `original_commit_timestamp`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.original_commit_timestamp_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.original_commit_timestamp e = ok e.original_commit_timestamp.1 := by
  unfold binlog.events.gtid_event.GtidEvent.impl.original_commit_timestamp; rfl

/-- `with_tx_length`. -/
theorem binlog.events.gtid_event.GtidEvent.with_tx_length_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_tx_length e x = ok { e with tx_length := (x, ()) } := by
  unfold binlog.events.gtid_event.GtidEvent.with_tx_length; rw [misc.raw.int.RawInt.new_eq]; exact bind_tc_ok _ _

/-- `tx_length`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.tx_length_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.tx_length e = ok e.tx_length.1 := by
  unfold binlog.events.gtid_event.GtidEvent.impl.tx_length; rfl

/-- `with_original_server_version`. -/
theorem binlog.events.gtid_event.GtidEvent.with_original_server_version_eq (e : binlog.events.gtid_event.GtidEvent) (x : U32) :
    binlog.events.gtid_event.GtidEvent.with_original_server_version e x = ok { e with original_server_version := (x, ()) } := by
  unfold binlog.events.gtid_event.GtidEvent.with_original_server_version; rw [misc.raw.int.RawInt.new_eq]; exact bind_tc_ok _ _

/-- `original_server_version`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.original_server_version_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.original_server_version e = ok e.original_server_version.1 := by
  unfold binlog.events.gtid_event.GtidEvent.impl.original_server_version; rfl

/-- `with_immediate_server_version`. -/
theorem binlog.events.gtid_event.GtidEvent.with_immediate_server_version_eq (e : binlog.events.gtid_event.GtidEvent) (x : U32) :
    binlog.events.gtid_event.GtidEvent.with_immediate_server_version e x = ok { e with immediate_server_version := (x, ()) } := by
  unfold binlog.events.gtid_event.GtidEvent.with_immediate_server_version; rw [misc.raw.int.RawInt.new_eq]; exact bind_tc_ok _ _

/-- `immediate_server_version`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.immediate_server_version_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.immediate_server_version e = ok e.immediate_server_version.1 := by
  unfold binlog.events.gtid_event.GtidEvent.impl.immediate_server_version; rfl

/-- `commit_group_ticket`. -/
theorem binlog.events.gtid_event.GtidEvent.impl.commit_group_ticket_eq (e : binlog.events.gtid_event.GtidEvent) :
    binlog.events.gtid_event.GtidEvent.impl.commit_group_ticket e = ok e.commit_group_ticket := by
  unfold binlog.events.gtid_event.GtidEvent.impl.commit_group_ticket; rfl

/-- `with_commit_group_ticket`. -/
theorem binlog.events.gtid_event.GtidEvent.with_commit_group_ticket_eq (e : binlog.events.gtid_event.GtidEvent) (x : U64) :
    binlog.events.gtid_event.GtidEvent.with_commit_group_ticket e x = ok { e with commit_group_ticket := x } := by
  unfold binlog.events.gtid_event.GtidEvent.with_commit_group_ticket; rfl

/-- `MyDeserialize::SIZE` is `None`. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE_eq :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE = none := by
  unfold binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.SIZE; rfl

private theorem eventTypeOfCode_code {n : Nat} {t : binlog.consts.EventType} (h : eventTypeOfCode n = some t) :
    eventTypeCode t = n := by
  unfold eventTypeOfCode at h
  simpa using List.find?_some h

private theorem rawint_eq_u64 {T : Type} (pe : core.cmp.PartialEq T T) (inst : misc.raw.int.IntRepr T U64)
    (a b : misc.raw.int.RawInt T U64) :
    misc.raw.int.RawInt.Insts.CoreCmpPartialEqRawInt.eq pe inst core.cmp.PartialEqU64 a b = ok (decide (a.1.val = b.1.val)) := by
  obtain ⟨x, _⟩ := a; obtain ⟨y, _⟩ := b
  by_cases h : x = y
  · subst h; simp [misc.raw.int.RawInt.Insts.CoreCmpPartialEqRawInt.eq, liftFun2, core.cmp.impls.PartialEqU64.eq,
      core.marker.PhantomData.Insts.CoreCmpPartialEqPhantomData.eq]
  · have : x.val ≠ y.val := fun e => h (UScalar.eq_of_val_eq e)
    simp [misc.raw.int.RawInt.Insts.CoreCmpPartialEqRawInt.eq, liftFun2, core.cmp.impls.PartialEqU64.eq, h, this]

private theorem rawint_eq_u32 {T : Type} (pe : core.cmp.PartialEq T T) (inst : misc.raw.int.IntRepr T U32)
    (a b : misc.raw.int.RawInt T U32) :
    misc.raw.int.RawInt.Insts.CoreCmpPartialEqRawInt.eq pe inst core.cmp.PartialEqU32 a b = ok (decide (a.1.val = b.1.val)) := by
  obtain ⟨x, _⟩ := a; obtain ⟨y, _⟩ := b
  by_cases h : x = y
  · subst h; simp [misc.raw.int.RawInt.Insts.CoreCmpPartialEqRawInt.eq, liftFun2, core.cmp.impls.PartialEqU32.eq,
      core.marker.PhantomData.Insts.CoreCmpPartialEqPhantomData.eq]
  · have : x.val ≠ y.val := fun e => h (UScalar.eq_of_val_eq e)
    simp [misc.raw.int.RawInt.Insts.CoreCmpPartialEqRawInt.eq, liftFun2, core.cmp.impls.PartialEqU32.eq, h, this]

private theorem lift_cast_u64_usize_small (x : U64) (h : x.val < 2 ^ 32) :
    lift (UScalar.cast .Usize x) ⦃ r => r.val = x.val ⦄ := by
  simp only [lift, WP.spec_ok]
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
    simp only [UScalarTy.numBits]; cases System.Platform.numBits_eq <;> simp [*]
  exact Nat.lt_of_lt_of_le h this

/-- `MyDeserialize` for `GTID_EVENT` (33) and `ANONYMOUS_GTID_EVENT` (34): total; `gtidRead`; untagged, serialization version 0, no commit group ticket. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_untagged (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val = 33 ∨ ctx.event_type_raw.val = 34) (buf : io.ParseBuf) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => ReadsAs gtidView (gtidRead buf.val) r rest ∧
      ∀ e, okPart r = some e → e.tag = none ∧ e.serialization_version.val = 0 ∧ e.commit_group_ticket.val = 0 ⦄ := by
  sorry

/-- `MyDeserialize` for `GTID_TAGGED_LOG_EVENT` (42): the (opaque) tagged reader. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_tagged (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val = 42) (buf : io.ParseBuf) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf = binlog.events.gtid_event.GtidEvent.deserialize_tagged buf := by
  unfold binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  have h42 : eventTypeOfCode 42 = some .GTID_TAGGED_LOG_EVENT := by rfl
  rw [binlog.consts.EventType.Insts.CoreConvertTryFromU8UnknownEventType.try_from_spec, hc, h42]
  exact bind_tc_ok _ _

/-- `MyDeserialize` with any other event type in the context: an error. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_other (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val ∉ [33, 34, 42]) (buf : io.ParseBuf) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r _ => okPart r = none ⦄ := by
  unfold binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  rw [binlog.consts.EventType.Insts.CoreConvertTryFromU8UnknownEventType.try_from_spec]
  generalize hx : eventTypeOfCode ctx.event_type_raw.val = x
  rcases x with _ | t
  · simp [misc.io_error_from, okPart]
  · have := eventTypeOfCode_code hx
    cases t <;> simp_all [misc.io_error_msg, okPart, eventTypeCode]

private theorem and_clear_mod (a : Nat) (k n : Nat) (hk : k < n) :
    (a &&& ((2 ^ n - 1) ^^^ 2 ^ k)) % 2 ^ (k + 1) = a % 2 ^ k := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
  by_cases h1 : j < k
  · have : j < n := by omega
    have : k ≠ j := by omega
    simp [*, show j < k + 1 by omega]
  · by_cases h2 : j = k
    · subst h2; simp [hk]
    · simp [h1, show ¬ j < k + 1 by omega]

private theorem or_set_mod (a : Nat) (k : Nat) :
    (a ||| 2 ^ k) % 2 ^ (k + 1) = a % 2 ^ k + 2 ^ k := by
  have e : a % 2 ^ k + 2 ^ k = 2 ^ k * 1 ||| a % 2 ^ k := by
    rw [← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by positivity))]; ring
  rw [e]
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.mul_one, Nat.testBit_two_pow]
  by_cases h1 : j < k
  · simp [h1, show j < k + 1 by omega, show k ≠ j by omega]
  · by_cases h2 : j = k
    · subst h2; simp
    · simp [h1, show ¬ j < k + 1 by omega, show k ≠ j by omega]

private theorem not_val_u64 (i : U64) : (~~~i).val = 2 ^ 64 - 1 - i.val := by
  show (UScalar.not i).val = _
  simp only [UScalar.not, UScalar.val, BitVec.toNat_not]
  rfl

private theorem not_val_u32 (i : U32) : (~~~i).val = 2 ^ 32 - 1 - i.val := by
  show (UScalar.not i).val = _
  simp only [UScalar.not, UScalar.val, BitVec.toNat_not]
  rfl

attribute [local step] misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec
  misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec
  misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_spec
  misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.serialize_spec

private theorem or55 (a : Nat) :
    leBytes 7 (a ||| 36028797018963968) = leBytes 7 (a % 36028797018963968 + 36028797018963968) := by
  rw [← IntAndMisc.leBytes_mod 7]; exact congrArg _ (or_set_mod a 55)

private theorem and55 (a : Nat) :
    leBytes 7 (a &&& 18410715276690587647) = leBytes 7 (a % 36028797018963968) := by
  rw [← IntAndMisc.leBytes_mod 7, show (18410715276690587647 : Nat) = (2 ^ 64 - 1) ^^^ 2 ^ 55 by decide]
  exact congrArg _ (and_clear_mod a 55 64 (by norm_num))

private theorem or31 (a : Nat) :
    leBytes 4 (a ||| 2147483648) = leBytes 4 (a % 2147483648 + 2147483648) := by
  rw [← IntAndMisc.leBytes_mod 4]; exact congrArg _ (or_set_mod a 31)

private theorem and31 (a : Nat) :
    leBytes 4 (a &&& 2147483647) = leBytes 4 (a % 2147483648) := by
  rw [← IntAndMisc.leBytes_mod 4, show (2147483647 : Nat) = (2 ^ 32 - 1) ^^^ 2 ^ 31 by decide]
  exact congrArg _ (and_clear_mod a 31 32 (by norm_num))

private theorem size64_mod : 36028797018963968 % U64.size = 36028797018963968 := by
  simp [U64.size, U64.numBits]

private theorem size32_mod : 2147483648 % U32.size = 2147483648 := by
  simp [U32.size, U32.numBits]

private theorem rawint_new_spec {T P : Type} (inst : misc.raw.int.IntRepr T P) (x : P) :
    misc.raw.int.RawInt.new inst x ⦃ r => r.1 = x ⦄ := by
  rw [misc.raw.int.RawInt.new_eq]; exact (WP.spec_ok _).mpr rfl

attribute [local step] rawint_new_spec

/-- The bytes `LogicalClockFields::serialize_untagged` appends. -/
private def lcEnc (f : binlog.events.gtid_event.LogicalClockFields) : List U8 :=
  let ict := f.immediate_commit_timestamp.1.val
  let oct := f.original_commit_timestamp.1.val
  let isv := f.immediate_server_version.1.val
  let osv := f.original_server_version.1.val
  leBytes 8 f.last_committed.1.val ++ leBytes 8 f.sequence_number.1.val ++
      leBytes 7 (ict % 2 ^ 55 + if ict ≠ oct then 2 ^ 55 else 0) ++
      (if ict ≠ oct then leBytes 7 oct else []) ++ lenencInt f.tx_length.1.val ++
      leBytes 4 (isv % 2 ^ 31 + if isv ≠ osv then 2 ^ 31 else 0) ++
      (if isv ≠ osv then leBytes 4 osv else [])

private theorem lc_serialize (f : binlog.events.gtid_event.LogicalClockFields) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lcEnc f).length ≤ Usize.max) :
    f.serialize_untagged buf ⦃ buf' => buf'.val = buf.val ++ lcEnc f ⦄ := by
  unfold binlog.events.gtid_event.LogicalClockFields.serialize_untagged
  simp only [rawint_eq_u64, rawint_eq_u32, misc.raw.int.RawInt.deref_eq, misc.raw.int.RawInt.serialize_eq]
  have hl : ∀ (k n : Nat), (leBytes k n).length = k := PBUtil.length_leBytes
  simp only [lcEnc, List.length_append, hl] at h ⊢
  generalize hb1 : decide (f.immediate_commit_timestamp.1.val = f.original_commit_timestamp.1.val) = b1
  generalize hb2 : decide (f.immediate_server_version.1.val = f.original_server_version.1.val) = b2
  cases b1 <;> cases b2 <;> step* <;> repeat' (split <;> step*)
  all_goals simp_all [or55, and55, or31, and31, size64_mod, size32_mod, not_val_u64, not_val_u32]

attribute [local step] U8.Insts.Mysql_commonMiscRawIntIntReprU8.serialize_spec
  ArrayU8LEN.Insts.Mysql_commonProtoMySerialize.serialize_spec
  misc.raw.int.ConstU8.Insts.Mysql_commonProtoMySerialize.serialize_spec

/-- `MySerialize` of an untagged event: appends `gtidEnc`. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize_spec (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag = none) (buf : alloc.vec.Vec U8)
    (h : buf.length + (gtidEnc e).length ≤ Usize.max) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf ⦃ buf' => buf'.val = buf.val ++ gtidEnc e ⦄ := by
  unfold binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize
  simp only [core.option.Option.is_some, ht]
  unfold binlog.events.gtid_event.GtidEvent.serialize_untagged
  simp only [misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMySerialize.serialize_eq,
    misc.raw._const.RawConst.Insts.Mysql_commonProtoMySerialize.serialize_eq]
  have hl : ∀ (k n : Nat), (leBytes k n).length = k := PBUtil.length_leBytes
  have hs : e.sid.val.length = 16 := by simp
  rcases hc : e.lc_typecode with _ | c
  · simp only [gtidEnc, hc, List.length_append, List.length_cons, List.length_nil, hl, hs] at h ⊢
    step* <;> simp_all [alloc.vec.Vec.length]; omega
  · simp only [gtidEnc, hc, List.length_append, List.length_cons, List.length_nil, hl, hs] at h ⊢
    step* <;> try (simp_all [alloc.vec.Vec.length]; omega)
    step with lc_serialize as ⟨b', hb'⟩
    · simp only [lcEnc, List.length_append, hl, alloc.vec.Vec.length, buf4_post, buf3_post, buf2_post, buf1_post,
        List.length_cons, List.length_nil, hs] at h ⊢
      omega
    · simp only [hb', buf4_post, buf3_post, buf2_post, buf1_post, lcEnc, List.append_assoc, List.cons_append,
        List.nil_append]
      rfl

/-- `MySerialize` of a tagged event: the (opaque) tagged writer. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize_tagged (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag.isSome) (buf : alloc.vec.Vec U8) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize e buf = binlog.events.gtid_event.GtidEvent.serialize_tagged e buf := by
  unfold binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMySerialize.serialize
  simp [core.option.Option.is_some, ht]

private theorem ok_of_map {T V : Type} {m : Result ((core.result.Result T core.io.error.Error) × io.ParseBuf)}
    {f : T → V} {v : V} {t : List U8}
    (h : m ⦃ r rest => (okPart r).map f = some v ∧ rest.val = t ⦄) :
    m ⦃ r rest => ∃ x, r = .Ok x ∧ f x = v ∧ rest.val = t ⦄ := by
  apply WP.spec_mono h
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  obtain ⟨x, rfl, hx⟩ := (BinlogEvGtid.okPart_map_some_iff _ _ _).1 h1
  exact ⟨x, rfl, hx, h2⟩

private theorem parse_usize_ok (buf : io.ParseBuf) (n : Usize) (h : n.val ≤ buf.length) :
    io.ParseBuf.parse io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize buf n ⦃ r rest =>
      ∃ x, r = .Ok x ∧ x.val = buf.val.take n.val ∧ rest.val = buf.val.drop n.val ⦄ := by
  apply ok_of_map
  apply WP.spec_mono (PKUtil.parse_usize_spec buf n)
  intro r hr; simpa [h] using hr

private theorem parse_flags (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.parse_unchecked
        (misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple
        binlog.consts.GtidFlags.Insts.BitflagsTraitsFlagsU8
        U8.Insts.Mysql_commonMiscRawIntIntReprU8) buf () ⦃ r rest =>
      ∃ x : misc.raw.flags.RawFlags binlog.consts.GtidFlags U8 U8, r = .Ok x ∧ x.1.val = leNat (buf.val.take 1) ∧
        rest.val = buf.val.drop 1 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  apply ok_of_map (f := fun (x : misc.raw.flags.RawFlags binlog.consts.GtidFlags U8 U8) => x.1.val)
  have := misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    binlog.consts.GtidFlags.Insts.BitflagsTraitsFlagsU8 U8.Insts.Mysql_commonMiscRawIntIntReprU8 buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 1)) ∧ rest.val = buf.val.drop 1)
    (U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec buf h)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  exact ⟨by simpa [Option.map_map] using h1, h2⟩

private theorem parse_sid (buf : io.ParseBuf) (h : 16 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple 16#usize) buf () ⦃ r rest =>
      ∃ x, r = .Ok x ∧ x.val = buf.val.take 16 ∧ rest.val = buf.val.drop 16 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  exact ok_of_map (ArrayU8LEN.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec 16#usize buf h)

private theorem parse_gno (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.parse_unchecked
        (misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple binlog.consts.Gno
        misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      ∃ x : misc.raw._const.RawConst misc.raw.int.LeU64 binlog.consts.Gno U64, r = .Ok x ∧
        x.1.val = leNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  apply ok_of_map (f := fun (x : misc.raw._const.RawConst misc.raw.int.LeU64 binlog.consts.Gno U64) => x.1.val)
  have := misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec
    binlog.consts.Gno misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64 buf
    (fun o rest => o.map (·.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8)
    (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec buf h)
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  exact ⟨by simpa [Option.map_map] using h1, h2⟩

attribute [local step] io.ParseBuf.is_empty_spec io.ParseBuf.len_spec

private theorem branch_ok_bind {T C : Type} (x : T)
    (k : core.ops.control_flow.ControlFlow (core.result.Result Never core.io.error.Error) T → Result C) :
    (do let cf ← core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Ok x); k cf) =
      k (.Continue x) := bind_tc_ok _ _

/-- Merge the `branch` results that `step*` leaves apart. -/
local macro "fixup" : tactic => `(tactic| (
  (try subst_vars) <;>
  (try simp only [core.ops.control_flow.ControlFlow.Continue.injEq, reduceCtorEq] at *) <;>
  (try subst_vars)))

private theorem untagged_no_lc (e : binlog.events.gtid_event.GtidEvent) (hlc : e.lc_typecode = none)
    (tail : List U8) (hb : tail.head?.map (·.val) ≠ some 2) (buf : io.ParseBuf) (h : buf.val = gtidEnc e ++ tail) :
    binlog.events.gtid_event.GtidEvent.deserialize_untagged buf ⦃ r rest => (okPart r).map gtidView = some
      { gtidView e with
        lc := false, lastCommitted := 0, sequenceNumber := 0, immediateCommitTs := 0,
        originalCommitTs := 0, txLength := 0, immediateServerVersion := undefinedServerVersion,
        originalServerVersion := undefinedServerVersion } ∧ rest.val = tail ⦄ := by
  have hl : ∀ (k n : Nat), (leBytes k n).length = k := PBUtil.length_leBytes
  have hs : e.sid.val.length = 16 := by simp
  simp only [gtidEnc, hlc, List.append_nil] at h
  have hlen : 25 ≤ buf.length := by
    simp only [Slice.length, h, List.length_append, List.length_cons, List.length_nil, hl, hs]; omega
  have hS : binlog.events.gtid_event.GtidEvent.ENCODED_SID_LENGTH.val = 16 := by
    unfold binlog.events.gtid_event.GtidEvent.ENCODED_SID_LENGTH; rfl
  have hU := BinlogEvGtid.u32_max_le_usize
  unfold binlog.events.gtid_event.GtidEvent.deserialize_untagged
  step*
  step with parse_usize_ok as ⟨r, buf1, pb, hr, hpb, hb1⟩
  subst hr
  step*
  fixup
  have hi1 : i1.val = 25 := by omega
  have hP : ([e.flags.1] ++ e.sid.val ++ leBytes 8 e.gno.1.val).length = 25 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hl, hs]
  rw [hi1, h, List.take_left' hP] at hpb
  rw [hi1, h, List.drop_left' hP] at hb1
  step with parse_flags pb (by simp [Slice.length, hpb, hs]) as ⟨r, sbuf, fl, hr, hfl, hsb⟩
  subst hr
  step*
  fixup
  simp only [hpb, List.cons_append, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero] at hfl hsb
  step with parse_sid sbuf (by simp [Slice.length, hsb, hs, hl]) as ⟨r, sbuf1, sid, hr, hsid, hsb1⟩
  subst hr
  step*
  fixup
  simp only [hsb, List.nil_append, List.take_left' hs, List.drop_left' hs] at hsid hsb1
  step with parse_gno sbuf1 (by simp [Slice.length, hsb1, hl]) as ⟨r, sbuf2, gno, hr, hgno, hsb2⟩
  subst hr
  have hgv : gno.1.val = e.gno.1.val := by
    rw [hgno, hsb1, List.take_of_length_le (by rw [hl]), BinlogEvGtid.leNat_leBytes_u64]
  have hfv : val.1.val = e.flags.1.val := by rw [hfl]; simp [leNat]
  step*
  · fixup
    simp [okPart, gtidView, hfv, hsid, hgv, binlog.events.gtid_event.GtidEvent.UNDEFINED_SERVER_VERSION,
      undefinedServerVersion, last_committed_post, immediate_commit_timestamp_post, tx_length_post,
      ‹original_server_version.1 = _›]
  · rename_i hnb
    have : buf1.val ≠ [] := fun h0 => hnb (b_post.mpr h0)
    have := List.length_pos_iff.mpr this
    simpa [Slice.length] using this
  · rename_i hc
    exfalso; apply hb
    obtain ⟨c, t, hct⟩ := BinlogEvGtid.list_cons_of_length_pos buf1.val (List.length_pos_iff.mpr (fun h0 => ‹¬b = true› (b_post.mpr h0)))
    simp only [hct, List.head?_cons, Option.map_some, Option.some.injEq]
    simp only [hct, List.getElem_cons_zero] at i2_post
    rw [← i2_post, hc]; unfold binlog.events.gtid_event.GtidEvent.LOGICAL_TIMESTAMP_TYPECODE; rfl
  · fixup
    simp [okPart, gtidView, hfv, hsid, hgv, binlog.events.gtid_event.GtidEvent.UNDEFINED_SERVER_VERSION,
      undefinedServerVersion, last_committed_post, immediate_commit_timestamp_post, tx_length_post,
      ‹original_server_version.1 = _›]
private theorem bne_u64 (x : U64) : (x != 0#u64) = true ↔ x.val ≠ 0 := by
  rw [bne_iff_ne]; constructor
  · intro h h0; exact h (UScalar.eq_of_val_eq (by simpa using h0))
  · intro h h0; exact h (by simp [h0])

private theorem bne_u32 (x : U32) : (x != 0#u32) = true ↔ x.val ≠ 0 := by
  rw [bne_iff_ne]; constructor
  · intro h h0; exact h (UScalar.eq_of_val_eq (by simpa using h0))
  · intro h h0; exact h (by simp [h0])

private theorem and_pow_set (a k : Nat) : (a % 2 ^ k + 2 ^ k) &&& 2 ^ k = 2 ^ k := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.add_comm, Nat.testBit_two_pow]
  by_cases hj : k = j
  · subst hj; simp [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (Nat.mod_lt _ (by positivity))]
  · simp [hj]

private theorem and_pow_clear (a k : Nat) (h : a < 2 ^ k) : a &&& 2 ^ k = 0 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hj : k = j
  · subst hj; simp [Nat.testBit_lt_two_pow h]
  · simp [hj]

private theorem u32_clear_val (a b : U32) (hb : b.val = 2 ^ 31) : (a &&& ~~~b).val = a.val % 2 ^ 31 := by
  rw [UScalar.val_and, not_val_u32, hb, show (2 ^ 32 - 1 - 2 ^ 31 : Nat) = (2 ^ 32 - 1) ^^^ 2 ^ 31 by decide]
  rw [← and_clear_mod a.val 31 32 (by norm_num)]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left a.hBounds)).symm

private theorem u64_clear_val (a b : U64) (hb : b.val = 2 ^ 55) (ha : a.val < 2 ^ 56) :
    (a &&& ~~~b).val = a.val % 2 ^ 55 := by
  rw [UScalar.val_and, not_val_u64, hb, show (2 ^ 64 - 1 - 2 ^ 55 : Nat) = (2 ^ 64 - 1) ^^^ 2 ^ 55 by decide]
  rw [← and_clear_mod a.val 55 64 (by norm_num)]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left ha)).symm

private theorem pu_rawint {T P : Type} (inst : misc.raw.int.IntRepr T P) (f : P → Nat) (v : Nat) (tl : List U8)
    (buf : io.ParseBuf) (h : inst.deserialize buf ⦃ r rest => (okPart r).map f = some v ∧ rest.val = tl ⦄) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple inst) buf () ⦃ r rest =>
      ∃ x : misc.raw.int.RawInt T P, r = .Ok x ∧ f x.1 = v ∧ rest.val = tl ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  apply ok_of_map (f := fun (x : misc.raw.int.RawInt T P) => f x.1)
  have := IntAndMisc.rawint_deserialize_spec inst buf (fun o rest => o.map f = some v ∧ rest.val = tl) h
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  exact ⟨by simpa [Option.map_map] using h1, h2⟩

private theorem pu_leu56 (buf : io.ParseBuf) (h : 7 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      ∃ x : misc.raw.int.RawInt misc.raw.int.LeU56 U64, r = .Ok x ∧ x.1.val = leNat (buf.val.take 7) ∧
        rest.val = buf.val.drop 7 ⦄ :=
  pu_rawint _ (fun x : U64 => x.val) _ _ buf (misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec buf h)

private theorem pu_leu32 (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      ∃ x : misc.raw.int.RawInt misc.raw.int.LeU32 U32, r = .Ok x ∧ x.1.val = leNat (buf.val.take 4) ∧
        rest.val = buf.val.drop 4 ⦄ :=
  pu_rawint _ (fun x : U32 => x.val) _ _ buf (misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec buf h)

private theorem pu_leu64 (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      ∃ x : misc.raw.int.RawInt misc.raw.int.LeU64 U64, r = .Ok x ∧ x.1.val = leNat (buf.val.take 8) ∧
        rest.val = buf.val.drop 8 ⦄ :=
  pu_rawint _ (fun x : U64 => x.val) _ _ buf (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec buf h)

private theorem p_leu56_rt (x : U64) (tl : List U8) (buf : io.ParseBuf) (h : buf.val = leBytes 7 x.val ++ tl) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      ∃ y : misc.raw.int.RawInt misc.raw.int.LeU56 U64, r = .Ok y ∧ y.1.val = x.val % 2 ^ 56 ∧ rest.val = tl ⦄ :=
  ok_of_map (f := fun (y : misc.raw.int.RawInt misc.raw.int.LeU56 U64) => y.1.val)
    (misc.raw.int.LeU56.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip x tl buf h)

private theorem p_leu32_rt (x : U32) (tl : List U8) (buf : io.ParseBuf) (h : buf.val = leBytes 4 x.val ++ tl) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      ∃ y : misc.raw.int.RawInt misc.raw.int.LeU32 U32, r = .Ok y ∧ y.1.val = x.val ∧ rest.val = tl ⦄ :=
  ok_of_map (f := fun (y : misc.raw.int.RawInt misc.raw.int.LeU32 U32) => y.1.val)
    (misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.roundtrip x tl buf h)

private theorem pu_lenenc_rt (x : U64) (tl : List U8) (buf : io.ParseBuf) (h : buf.val = lenencInt x.val ++ tl) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      ∃ y : misc.raw.int.RawInt misc.raw.int.LenEnc U64, r = .Ok y ∧ y.1 = x ∧ rest.val = tl ⦄ := by
  have := misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.roundtrip x tl buf h
  rw [io.ParseBuf.parse_of_size_none _ buf () (by simp [misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE, misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawIntIntReprU64.SIZE_eq])] at this
  rw [io.ParseBuf.parse_unchecked_eq]
  exact ok_of_map (f := fun (y : misc.raw.int.RawInt misc.raw.int.LenEnc U64) => y.1) this

private theorem pu_constu8 (buf : io.ParseBuf) (h1 : 1 ≤ buf.length) (h2 : leNat (buf.val.take 1) = 2) :
    io.ParseBuf.parse_unchecked
      (misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple 2#u8
        binlog.events.gtid_event.InvalidLogicalTimestampTypecode.Insts.CoreErrorError
        binlog.events.gtid_event.InvalidLogicalTimestampTypecode.Insts.CoreDefaultDefault) buf () ⦃ r rest =>
      ∃ x : misc.raw.int.ConstU8 binlog.events.gtid_event.InvalidLogicalTimestampTypecode 2#u8, r = .Ok x ∧
        rest.val = buf.val.drop 1 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw.int.ConstU8.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec 2#u8
    binlog.events.gtid_event.InvalidLogicalTimestampTypecode.Insts.CoreErrorError
    binlog.events.gtid_event.InvalidLogicalTimestampTypecode.Insts.CoreDefaultDefault
    (by simp [binlog.events.gtid_event.InvalidLogicalTimestampTypecode.Insts.CoreDefaultDefault.default]) buf h1
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨ha, hb⟩
  cases r with
  | Ok x => exact ⟨x, rfl, hb⟩
  | Err _ => simp [okPart, h2] at ha

private theorem untagged_lc (e : binlog.events.gtid_event.GtidEvent) (hlc : e.lc_typecode.isSome)
    (hi : e.immediate_commit_timestamp.1.val < 2 ^ 55) (ho : e.original_commit_timestamp.1.val < 2 ^ 56)
    (hsv : e.immediate_server_version.1.val < 2 ^ 31)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = gtidEnc e ++ tail) :
    binlog.events.gtid_event.GtidEvent.deserialize_untagged buf ⦃ r rest => (okPart r).map gtidView = some (gtidView e) ∧ rest.val = tail ⦄ := by
  have hl : ∀ (k n : Nat), (leBytes k n).length = k := PBUtil.length_leBytes
  have hs : e.sid.val.length = 16 := by simp
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hlc
  generalize hT : (leBytes 7 (e.immediate_commit_timestamp.1.val % 2 ^ 55 +
      if e.immediate_commit_timestamp.1.val ≠ e.original_commit_timestamp.1.val then 2 ^ 55 else 0) ++
      (if e.immediate_commit_timestamp.1.val ≠ e.original_commit_timestamp.1.val then leBytes 7 e.original_commit_timestamp.1.val else []) ++
      lenencInt e.tx_length.1.val ++
      leBytes 4 (e.immediate_server_version.1.val % 2 ^ 31 + if e.immediate_server_version.1.val ≠ e.original_server_version.1.val then 2 ^ 31 else 0) ++
      (if e.immediate_server_version.1.val ≠ e.original_server_version.1.val then leBytes 4 e.original_server_version.1.val else []) ++ tail) = T
  have hbuf : buf.val = ([e.flags.1] ++ e.sid.val ++ leBytes 8 e.gno.1.val) ++
      (byte 2 :: (leBytes 8 e.last_committed.1.val ++ leBytes 8 e.sequence_number.1.val) ++ T) := by
    rw [h, ← hT]; simp only [gtidEnc, hc, List.append_assoc, List.cons_append, List.nil_append]
  clear h
  have hP : ([e.flags.1] ++ e.sid.val ++ leBytes 8 e.gno.1.val).length = 25 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hl, hs]
  have hS : binlog.events.gtid_event.GtidEvent.ENCODED_SID_LENGTH.val = 16 := by
    unfold binlog.events.gtid_event.GtidEvent.ENCODED_SID_LENGTH; rfl
  have hU := BinlogEvGtid.u32_max_le_usize
  have hlen : 25 ≤ buf.length := by
    simp only [Slice.length, hbuf, List.length_append, hP]; omega
  unfold binlog.events.gtid_event.GtidEvent.deserialize_untagged
  step*
  step with parse_usize_ok as ⟨r, buf1, pb, hr, hpb, hb1⟩
  subst hr
  rw [branch_ok_bind]
  have hi1 : i1.val = 25 := by omega
  rw [hi1, hbuf, List.take_left' hP] at hpb
  rw [hi1, hbuf, List.drop_left' hP] at hb1
  step with parse_flags pb (by simp [Slice.length, hpb, hs]) as ⟨r, sbuf, fl, hr, hfl, hsb⟩
  subst hr
  rw [branch_ok_bind]
  simp only [hpb, List.cons_append, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero] at hfl hsb
  step with parse_sid sbuf (by simp [Slice.length, hsb, hs, hl]) as ⟨r, sbuf1, sid, hr, hsid, hsb1⟩
  subst hr
  rw [branch_ok_bind]
  simp only [hsb, List.nil_append, List.take_left' hs, List.drop_left' hs] at hsid hsb1
  step with parse_gno sbuf1 (by simp [Slice.length, hsb1, hl]) as ⟨r, sbuf2, gno, hr, hgno, hsb2⟩
  subst hr
  rw [branch_ok_bind]
  have hgv : gno.1.val = e.gno.1.val := by
    rw [hgno, hsb1, List.take_of_length_le (by rw [hl]), BinlogEvGtid.leNat_leBytes_u64]
  have hfv : fl.1.val = e.flags.1.val := by rw [hfl]; simp [leNat]
  step
  step
  step
  step
  apply WP.spec_bind (io.ParseBuf.is_empty_spec buf1)
  intro b hb
  have hbf : b = false := by
    cases b
    · rfl
    · exact absurd (hb.mp rfl) (by simp [hb1])
  subst hbf
  rw [ite_eq_right_of_eq_false _ _ (by decide)]
  step
  have hi2 : i2 = binlog.events.gtid_event.GtidEvent.LOGICAL_TIMESTAMP_TYPECODE := by
    rw [i2_post]; simp only [hb1, List.cons_append, List.getElem_cons_zero]
    unfold binlog.events.gtid_event.GtidEvent.LOGICAL_TIMESTAMP_TYPECODE; rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true hi2)]
  step with pu_constu8 buf1 (by simp [Slice.length, hb1]) (by simp only [hb1, List.cons_append, List.take_succ_cons, List.take_zero, leNat]; rfl) as ⟨r, buf2, lct, hr, hb2⟩
  subst hr
  rw [branch_ok_bind]
  simp only [hb1, List.cons_append, List.drop_succ_cons, List.drop_zero] at hb2
  have hAB : (leBytes 8 e.last_committed.1.val ++ leBytes 8 e.sequence_number.1.val).length = 16 := by
    simp [hl]
  step with parse_usize_ok buf2 16#usize (by simp [Slice.length, hb2, hl]; omega) as ⟨r, buf3, pb1, hr, hpb1, hb3⟩
  subst hr
  rw [branch_ok_bind]
  simp only [hb2, List.take_left' hAB, List.drop_left' hAB] at hpb1 hb3
  step with pu_leu64 pb1 (by simp [Slice.length, hpb1, hl]) as ⟨r, sb2, lcv, hr, hlcv, hsb2'⟩
  subst hr
  rw [branch_ok_bind]
  step with pu_leu64 sb2 (by simp [Slice.length, hsb2', hpb1, hl]) as ⟨r, sb3, snv, hr, hsnv, hsb3'⟩
  subst hr
  rw [branch_ok_bind]
  obtain ⟨T2, hT2⟩ : ∃ T2, T2 = lenencInt e.tx_length.1.val ++
      leBytes 4 (e.immediate_server_version.1.val % 2 ^ 31 + if e.immediate_server_version.1.val ≠ e.original_server_version.1.val then 2 ^ 31 else 0) ++
      (if e.immediate_server_version.1.val ≠ e.original_server_version.1.val then leBytes 4 e.original_server_version.1.val else []) ++ tail := ⟨_, rfl⟩
  have hraw : e.immediate_commit_timestamp.1.val % 2 ^ 55 +
      (if e.immediate_commit_timestamp.1.val ≠ e.original_commit_timestamp.1.val then 2 ^ 55 else 0) < 2 ^ 56 := by
    split_ifs <;> omega
  have hT' : T = leBytes 7 (e.immediate_commit_timestamp.1.val % 2 ^ 55 +
      if e.immediate_commit_timestamp.1.val ≠ e.original_commit_timestamp.1.val then 2 ^ 55 else 0) ++
      ((if e.immediate_commit_timestamp.1.val ≠ e.original_commit_timestamp.1.val then leBytes 7 e.original_commit_timestamp.1.val else []) ++ T2) := by
    rw [← hT, hT2]; simp only [List.append_assoc]
  clear hT
  step as ⟨i3, i3_post⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by
    unfold binlog.events.gtid_event.GtidEvent.IMMEDIATE_COMMIT_TIMESTAMP_LENGTH
    show 7 ≤ i3.val
    rw [i3_post]; simp [Slice.length, hb3, hT', hl]))]
  step with pu_leu56 buf3 (by simp [Slice.length, hb3, hT', hl]) as ⟨r, buf4, tsx, hr, htsx, hb4⟩
  subst hr
  rw [branch_ok_bind]
  rw [hb3, hT', List.take_left' (hl _ _), BinlogEvGtid.leNat_leBytes_of_lt _ _ hraw] at htsx
  rw [hb3, hT', List.drop_left' (hl _ _)] at hb4
  obtain ⟨i4, pd⟩ := tsx
  step as ⟨i5, hi5, _⟩
  have h55 : i5.val = 2 ^ 55 := by rw [hi5]; simp [U64.size, U64.numBits, Nat.shiftLeft_eq]
  step as ⟨i6, hi6, _⟩
  obtain ⟨SVt, hSVt⟩ : ∃ s, s = leBytes 4 (e.immediate_server_version.1.val % 2 ^ 31 + if e.immediate_server_version.1.val ≠ e.original_server_version.1.val then 2 ^ 31 else 0) ++
      ((if e.immediate_server_version.1.val ≠ e.original_server_version.1.val then leBytes 4 e.original_server_version.1.val else []) ++ tail) := ⟨_, rfl⟩
  have hT2' : T2 = lenencInt e.tx_length.1.val ++ SVt := by rw [hT2, hSVt]; simp only [List.append_assoc]
  clear hT2
  have hSV4 : 4 ≤ SVt.length := by rw [hSVt]; simp [hl]
  by_cases hio : e.immediate_commit_timestamp.1.val = e.original_commit_timestamp.1.val
  · -- no separate original timestamp
    have hict : i4.val = e.immediate_commit_timestamp.1.val := by
      have hn : ¬ (e.immediate_commit_timestamp.1.val ≠ e.original_commit_timestamp.1.val) := not_not.mpr hio
      rw [htsx]; simp only [hn, ite_false, Nat.add_zero]; exact Nat.mod_eq_of_lt hi
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by
      rw [Bool.not_eq_true, ← Bool.not_eq_true, bne_u64, not_not, hi6, UScalar.val_and, h55, hict]
      exact and_pow_clear _ _ hi))]
    simp only [hio, ne_eq, not_true_eq_false, ite_false, List.nil_append] at hb4
    apply WP.spec_bind (io.ParseBuf.is_empty_spec buf4)
    intro b hb
    have hbf : b = false := by
      cases b
      · rfl
      · exact absurd (hb.mp rfl) (by
          rw [hb4, hT2']; have := BinlogEvGtid.lenencInt_length_pos e.tx_length.1.val
          intro h0; rw [List.append_eq_nil_iff] at h0; rw [h0.1] at this; simp at this)
    subst hbf
    rw [ite_eq_right_of_eq_false _ _ (by decide)]
    step with pu_lenenc_rt e.tx_length.1 SVt buf4 (by rw [hb4, hT2']) as ⟨r, buf6, txv, hr, htxv, hb6⟩
    subst hr
    rw [branch_ok_bind]
    step as ⟨i9, hi9⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by
      unfold binlog.events.gtid_event.GtidEvent.IMMEDIATE_SERVER_VERSION_LENGTH
      show 4 ≤ i9.val
      rw [hi9, Slice.length, hb6]; exact hSV4))]
    step with pu_leu32 buf6 (by rw [Slice.length, hb6]; exact hSV4) as ⟨r, buf7, svx, hr, hsvx, hb7⟩
    subst hr
    rw [branch_ok_bind]
    obtain ⟨i10, pd1⟩ := svx
    step as ⟨i11, hi11, _⟩
    have h31 : i11.val = 2 ^ 31 := by rw [hi11]; simp [U32.size, U32.numBits, Nat.shiftLeft_eq]
    step as ⟨i12, hi12, _⟩
    by_cases hisv : e.immediate_server_version.1.val = e.original_server_version.1.val
    · have hn : ¬ (e.immediate_server_version.1.val ≠ e.original_server_version.1.val) := not_not.mpr hisv
      simp only [hn, ite_false, Nat.add_zero, List.nil_append] at hSVt
      have hisvv : i10.val = e.immediate_server_version.1.val := by
        rw [show (i10, pd1).1 = i10 from rfl, hb6, hSVt, List.take_left' (hl _ _),
          BinlogEvGtid.leNat_leBytes_of_lt _ _ (by omega)] at hsvx
        rw [hsvx]; exact Nat.mod_eq_of_lt hsv
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by
        rw [Bool.not_eq_true, ← Bool.not_eq_true, bne_u32, not_not, hi12, UScalar.val_and, h31, hisvv]
        exact and_pow_clear _ _ hsv))]
      apply (WP.spec_ok _).mpr
      have hsnv' : snv.1.val = e.sequence_number.1.val := by
        rw [hsnv, hsb2', hpb1, List.drop_left' (hl _ _), List.take_of_length_le (by rw [hl]),
          BinlogEvGtid.leNat_leBytes_u64]
      have hlcv'' : lcv.1.val = e.last_committed.1.val := by
        rw [hlcv, hpb1, List.take_left' (hl _ _), BinlogEvGtid.leNat_leBytes_u64]
      refine ⟨?_, ?_⟩
      · simp only [okPart, Option.map_some, gtidView, hc, Option.isSome_some, hfv, hsid, hgv, hlcv'', hsnv',
          hict, htxv, hisvv, hio, hisv]
      · rw [hb7, hb6, hSVt, List.drop_left' (hl _ _)]
    · have hn : e.immediate_server_version.1.val ≠ e.original_server_version.1.val := hisv
      simp only [hn, ne_eq, not_false_eq_true, ite_true] at hSVt
      have hisvv : i10.val = e.immediate_server_version.1.val % 2 ^ 31 + 2 ^ 31 := by
        rw [show (i10, pd1).1 = i10 from rfl, hb6, hSVt, List.take_left' (hl _ _),
          BinlogEvGtid.leNat_leBytes_of_lt _ _ (by omega)] at hsvx
        exact hsvx
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by
        rw [bne_u32, hi12, UScalar.val_and, h31, hisvv, and_pow_set]; positivity))]
      step as ⟨i13, hi13⟩
      step as ⟨i14, hi14, _⟩
      have hb7' : buf7.val = leBytes 4 e.original_server_version.1.val ++ tail := by
        rw [hb7, hb6, hSVt, List.drop_left' (hl _ _)]
      step with p_leu32_rt e.original_server_version.1 tail buf7 hb7' as ⟨r, buf8, osvx, hr, hosvx, hb8⟩
      subst hr
      rw [branch_ok_bind]
      apply (WP.spec_ok _).mpr
      have hsnv' : snv.1.val = e.sequence_number.1.val := by
        rw [hsnv, hsb2', hpb1, List.drop_left' (hl _ _), List.take_of_length_le (by rw [hl]),
          BinlogEvGtid.leNat_leBytes_u64]
      have hlcv'' : lcv.1.val = e.last_committed.1.val := by
        rw [hlcv, hpb1, List.take_left' (hl _ _), BinlogEvGtid.leNat_leBytes_u64]
      have hi14v : i14.val = e.immediate_server_version.1.val := by
        rw [hi14, hi13, u32_clear_val _ _ h31, hisvv]; omega
      refine ⟨?_, hb8⟩
      simp only [okPart, Option.map_some, gtidView, hc, Option.isSome_some, hfv, hsid, hgv, hlcv'', hsnv',
          hict, htxv, hi14v, hio, hosvx]
  · have hn : e.immediate_commit_timestamp.1.val ≠ e.original_commit_timestamp.1.val := hio
    have hict : i4.val = e.immediate_commit_timestamp.1.val % 2 ^ 55 + 2 ^ 55 := by
      rw [htsx]; simp only [hn, ne_eq, not_false_eq_true, ite_true]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by
      rw [bne_u64, hi6, UScalar.val_and, h55, hict, and_pow_set]; positivity))]
    step as ⟨i7, hi7⟩
    step as ⟨i8, hi8, _⟩
    have hi8v : i8.val = e.immediate_commit_timestamp.1.val := by
      rw [hi8, hi7, u64_clear_val _ _ h55 (by rw [hict]; omega), hict]; omega
    simp only [hn, ne_eq, not_false_eq_true, ite_true] at hb4
    step with p_leu56_rt e.original_commit_timestamp.1 T2 buf4 hb4 as ⟨r, bufO, ov, hr, hov, hbO⟩
    subst hr
    rw [branch_ok_bind]
    have hov' : ov.1.val = e.original_commit_timestamp.1.val := by rw [hov]; exact Nat.mod_eq_of_lt ho
    apply WP.spec_bind (io.ParseBuf.is_empty_spec bufO)
    intro b hb
    have hbf : b = false := by
      cases b
      · rfl
      · exact absurd (hb.mp rfl) (by
          rw [hbO, hT2']; have := BinlogEvGtid.lenencInt_length_pos e.tx_length.1.val
          intro h0; rw [List.append_eq_nil_iff] at h0; rw [h0.1] at this; simp at this)
    subst hbf
    rw [ite_eq_right_of_eq_false _ _ (by decide)]
    step with pu_lenenc_rt e.tx_length.1 SVt bufO (by rw [hbO, hT2']) as ⟨r, buf6, txv, hr, htxv, hb6⟩
    subst hr
    rw [branch_ok_bind]
    step as ⟨i9, hi9⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by
      unfold binlog.events.gtid_event.GtidEvent.IMMEDIATE_SERVER_VERSION_LENGTH
      show 4 ≤ i9.val
      rw [hi9, Slice.length, hb6]; exact hSV4))]
    step with pu_leu32 buf6 (by rw [Slice.length, hb6]; exact hSV4) as ⟨r, buf7, svx, hr, hsvx, hb7⟩
    subst hr
    rw [branch_ok_bind]
    obtain ⟨i10, pd1⟩ := svx
    step as ⟨i11, hi11, _⟩
    have h31 : i11.val = 2 ^ 31 := by rw [hi11]; simp [U32.size, U32.numBits, Nat.shiftLeft_eq]
    step as ⟨i12, hi12, _⟩
    by_cases hisv : e.immediate_server_version.1.val = e.original_server_version.1.val
    · have hn : ¬ (e.immediate_server_version.1.val ≠ e.original_server_version.1.val) := not_not.mpr hisv
      simp only [hn, ite_false, Nat.add_zero, List.nil_append] at hSVt
      have hisvv : i10.val = e.immediate_server_version.1.val := by
        rw [show (i10, pd1).1 = i10 from rfl, hb6, hSVt, List.take_left' (hl _ _),
          BinlogEvGtid.leNat_leBytes_of_lt _ _ (by omega)] at hsvx
        rw [hsvx]; exact Nat.mod_eq_of_lt hsv
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by
        rw [Bool.not_eq_true, ← Bool.not_eq_true, bne_u32, not_not, hi12, UScalar.val_and, h31, hisvv]
        exact and_pow_clear _ _ hsv))]
      apply (WP.spec_ok _).mpr
      have hsnv' : snv.1.val = e.sequence_number.1.val := by
        rw [hsnv, hsb2', hpb1, List.drop_left' (hl _ _), List.take_of_length_le (by rw [hl]),
          BinlogEvGtid.leNat_leBytes_u64]
      have hlcv'' : lcv.1.val = e.last_committed.1.val := by
        rw [hlcv, hpb1, List.take_left' (hl _ _), BinlogEvGtid.leNat_leBytes_u64]
      refine ⟨?_, ?_⟩
      · simp only [okPart, Option.map_some, gtidView, hc, Option.isSome_some, hfv, hsid, hgv, hlcv'', hsnv',
          hi8v, htxv, hisvv, hov', hisv]
      · rw [hb7, hb6, hSVt, List.drop_left' (hl _ _)]
    · have hn : e.immediate_server_version.1.val ≠ e.original_server_version.1.val := hisv
      simp only [hn, ne_eq, not_false_eq_true, ite_true] at hSVt
      have hisvv : i10.val = e.immediate_server_version.1.val % 2 ^ 31 + 2 ^ 31 := by
        rw [show (i10, pd1).1 = i10 from rfl, hb6, hSVt, List.take_left' (hl _ _),
          BinlogEvGtid.leNat_leBytes_of_lt _ _ (by omega)] at hsvx
        exact hsvx
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by
        rw [bne_u32, hi12, UScalar.val_and, h31, hisvv, and_pow_set]; positivity))]
      step as ⟨i13, hi13⟩
      step as ⟨i14, hi14, _⟩
      have hb7' : buf7.val = leBytes 4 e.original_server_version.1.val ++ tail := by
        rw [hb7, hb6, hSVt, List.drop_left' (hl _ _)]
      step with p_leu32_rt e.original_server_version.1 tail buf7 hb7' as ⟨r, buf8, osvx, hr, hosvx, hb8⟩
      subst hr
      rw [branch_ok_bind]
      apply (WP.spec_ok _).mpr
      have hsnv' : snv.1.val = e.sequence_number.1.val := by
        rw [hsnv, hsb2', hpb1, List.drop_left' (hl _ _), List.take_of_length_le (by rw [hl]),
          BinlogEvGtid.leNat_leBytes_u64]
      have hlcv'' : lcv.1.val = e.last_committed.1.val := by
        rw [hlcv, hpb1, List.take_left' (hl _ _), BinlogEvGtid.leNat_leBytes_u64]
      have hi14v : i14.val = e.immediate_server_version.1.val := by
        rw [hi14, hi13, u32_clear_val _ _ h31, hisvv]; omega
      refine ⟨?_, hb8⟩
      simp only [okPart, Option.map_some, gtidView, hc, Option.isSome_some, hfv, hsid, hgv, hlcv'', hsnv',
          hi8v, htxv, hi14v, hov', hosvx]


private theorem deserialize_eq_untagged (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val = 33 ∨ ctx.event_type_raw.val = 34) (buf : io.ParseBuf) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf =
      binlog.events.gtid_event.GtidEvent.deserialize_untagged buf := by
  unfold binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize
  rw [binlog.consts.EventType.Insts.CoreConvertTryFromU8UnknownEventType.try_from_spec]
  rcases hc with hc | hc
  · have h33 : eventTypeOfCode 33 = some .GTID_EVENT := by rfl
    rw [hc, h33]
    exact bind_tc_ok _ _
  · have h34 : eventTypeOfCode 34 = some .ANONYMOUS_GTID_EVENT := by rfl
    rw [hc, h34]
    exact bind_tc_ok _ _

/-- Round trip (untagged, with the logical-clock part): the event reads back, for timestamps below `2^55` (immediate) and `2^56` (original) and an immediate server version below `2^31`; bytes after it are left. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag = none) (hlc : e.lc_typecode.isSome)
    (hi : e.immediate_commit_timestamp.1.val < 2 ^ 55) (ho : e.original_commit_timestamp.1.val < 2 ^ 56)
    (hs : e.immediate_server_version.1.val < 2 ^ 31)
    (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val = 33 ∨ ctx.event_type_raw.val = 34)
    (tail : List U8) (buf : io.ParseBuf) (h : buf.val = gtidEnc e ++ tail) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map gtidView = some (gtidView e) ∧ rest.val = tail ⦄ := by
  rw [deserialize_eq_untagged ctx hc]
  exact (fun _ => untagged_lc e hlc hi ho hs tail buf h) ht

/-- Round trip of an untagged event without the logical-clock part (pre-5.7): the 25-byte prefix reads back with the defaults (zeros, server versions `UNDEFINED_SERVER_VERSION`), provided the following bytes do not start with `2`. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize_roundtrip_no_lc (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag = none) (hlc : e.lc_typecode = none)
    (ctx : binlog.BinlogCtx) (hc : ctx.event_type_raw.val = 33 ∨ ctx.event_type_raw.val = 34)
    (tail : List U8) (hb : tail.head?.map (·.val) ≠ some 2) (buf : io.ParseBuf) (h : buf.val = gtidEnc e ++ tail) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonProtoMyDeserializeDeBinlogCtx.deserialize ctx buf ⦃ r rest => (okPart r).map gtidView = some
      { gtidView e with
        lc := false, lastCommitted := 0, sequenceNumber := 0, immediateCommitTs := 0,
        originalCommitTs := 0, txLength := 0, immediateServerVersion := undefinedServerVersion,
        originalServerVersion := undefinedServerVersion } ∧ rest.val = tail ⦄ := by
  rw [deserialize_eq_untagged ctx hc]
  exact (fun _ => untagged_no_lc e hlc tail hb buf h) ht

set_option maxHeartbeats 1000000 in
/-- `BinlogStruct::len` of an untagged event: `gtidLenCrate`, which always counts the logical-clock part. **Quirk:** without it (`lc_typecode` `None`) `serialize` writes 25 bytes but `len` is at least 54 (`Defs.gtidLenCrate_ne`); with it, `len` is the length of `gtidEnc` (`Defs.gtidLenCrate_eq`). -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_spec (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag = none) (v : binlog.consts.BinlogVersion) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v ⦃ n => n.val = gtidLenCrate e ⦄ := by
  unfold binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  simp only [core.option.Option.is_some, ht]
  unfold binlog.events.gtid_event.GtidEvent.len_untagged binlog.events.gtid_event.LogicalClockFields.len_untagged
  simp only [rawint_eq_u64, rawint_eq_u32, misc.raw.int.RawInt.deref_eq]
  have hU := BinlogEvGtid.u32_max_le_usize
  have hS : binlog.events.gtid_event.GtidEvent.ENCODED_SID_LENGTH.val = 16 := by
    unfold binlog.events.gtid_event.GtidEvent.ENCODED_SID_LENGTH; rfl
  have hl9 := BinlogEvGtid.lenencInt_length_le e.tx_length.1.val
  generalize hb1 : decide (e.immediate_commit_timestamp.1.val = e.original_commit_timestamp.1.val) = b1
  generalize hb2 : decide (e.immediate_server_version.1.val = e.original_server_version.1.val) = b2
  have hL := BinlogEvGtid.header_len_val
  have h4 : (4#usize).val = 4 := rfl
  have h7 : (7#usize).val = 7 := rfl
  cases b1 <;> cases b2 <;> step* <;>
  step with misc.lenenc_int_len_spec as ⟨i1, hi1⟩ <;>
  step with lift_cast_u64_usize_small i1 (by omega) as ⟨i2, hi2⟩ <;>
  step* <;>
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 <;>
  (try simp only [BinlogEvGtid.usize_saturating_add_val] at *) <;>
  (try simp only [gtidLenCrate, evLenCap, hb1, hb2, ne_eq, not_false_eq_true, not_true_eq_false, ite_true, ite_false]) <;>
  (have hK : 1000 ≤ 2 ^ 32 - 1 := by norm_num) <;>
  generalize (2 : Nat) ^ 32 - 1 = K at * <;>
  generalize Usize.max = M at * <;>
  clear hb1 hb2 ht <;> omega

/-- `BinlogStruct::len` of a tagged event: the (opaque) tagged length. -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len_tagged (e : binlog.events.gtid_event.GtidEvent) (ht : e.tag.isSome) (v : binlog.consts.BinlogVersion) :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len e v = binlog.events.gtid_event.GtidEvent.len_tagged e := by
  unfold binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogStruct.len
  simp [core.option.Option.is_some, ht]

/-- `BinlogEvent::EVENT_TYPE`: `GTID_EVENT` (33). -/
theorem binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE_eq :
    binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE = .GTID_EVENT := by
  unfold binlog.events.gtid_event.GtidEvent.Insts.Mysql_commonBinlogBinlogEvent.EVENT_TYPE; rfl

end mysql_common
