import Defs
import Proofs.Util.StmtBulkSsB
import Proofs.Misc.Raw.Bytes.RawBytes

/-! Statements for `struct TransactionCharacteristics and its impls` (spec file: `Specs/Packets/SessionStateChange.lean`).
Helper lemmas: `Proofs/Util/StmtBulkSsB.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `TransactionCharacteristics::new(v)`: wraps `v.into()`. -/
theorem packets.session_state_change.TransactionCharacteristics.new_spec {X : Type}
    (into : core.convert.Into X (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (v : X) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into v = ok c) :
    packets.session_state_change.TransactionCharacteristics.new into v ⦃ x => x.1 = c ⦄ := by
  unfold packets.session_state_change.TransactionCharacteristics.new
  rw [misc.raw.bytes.RawBytes.new_eq _ into v c h]
  apply WP.spec_bind (Pₘ := fun x => x.1 = c) ((WP.spec_ok _).mpr rfl)
  intro x hx
  exact (WP.spec_ok _).mpr hx

/-- `as_bytes`: the raw value. -/
theorem packets.session_state_change.TransactionCharacteristics.as_bytes_spec (self : packets.session_state_change.TransactionCharacteristics) :
    packets.session_state_change.TransactionCharacteristics.as_bytes self ⦃ s => s.val = cowList self.1 ⦄ := by
  unfold packets.session_state_change.TransactionCharacteristics.as_bytes
  exact PCSUtil.lenenc_as_bytes self

/-- `as_str`: the value as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.session_state_change.TransactionCharacteristics.as_str_spec (self : packets.session_state_change.TransactionCharacteristics) :
    packets.session_state_change.TransactionCharacteristics.as_str self ⦃ c => LossyUtf8Valid (cowList self.1) c ⦄ := by
  unfold packets.session_state_change.TransactionCharacteristics.as_str
  exact SBSsB.lenenc_as_str self

/-- `into_owned`: the same bytes. -/
theorem packets.session_state_change.TransactionCharacteristics.into_owned_spec (self : packets.session_state_change.TransactionCharacteristics) :
    packets.session_state_change.TransactionCharacteristics.into_owned self ⦃ x => cowList x.1 = cowList self.1 ⦄ := by
  unfold packets.session_state_change.TransactionCharacteristics.into_owned
  apply WP.spec_bind (PCSUtil.raw_into_owned _ self)
  intro x hx
  exact (WP.spec_ok _).mpr hx

/-- `MyDeserialize for TransactionCharacteristics`: `SIZE` is `None`. -/
theorem packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  unfold packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for TransactionCharacteristics`: total; a length-encoded string (`checkedLenencStr`). -/
theorem packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64)
    (buf : io.ParseBuf) :
    packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun x => cowList x.1), rest.val) = checkedLenencStr buf.val ⦄ := by
  unfold packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  exact SBSsB.lenenc_parse_rewrap h64 buf

/-- `MySerialize for TransactionCharacteristics`: appends the value as a length-encoded string. -/
theorem packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.session_state_change.TransactionCharacteristics)
    (buf : alloc.vec.Vec U8) (h : buf.length + (lenencStr (cowList self.1)).length ≤ Usize.max) :
    packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ lenencStr (cowList self.1) ⦄ := by
  unfold packets.session_state_change.TransactionCharacteristics.Insts.Mysql_commonProtoMySerialize.serialize
  exact PCSUtil.lenenc_raw_serialize self buf h

end mysql_common
