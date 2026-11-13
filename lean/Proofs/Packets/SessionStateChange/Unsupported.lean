import Defs

/-! Statements for `struct Unsupported and its impls` (spec file: `Specs/Packets/SessionStateChange.lean`).
Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `Unsupported::new(v)`: wraps `v.into()`. -/
theorem packets.session_state_change.Unsupported.new_spec {X : Type}
    (into : core.convert.Into X (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (v : X) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into v = ok c) :
    packets.session_state_change.Unsupported.new into v ⦃ x => x.1 = c ⦄ := by
  sorry

/-- `as_bytes`: the raw value. -/
theorem packets.session_state_change.Unsupported.as_bytes_spec (self : packets.session_state_change.Unsupported) :
    packets.session_state_change.Unsupported.as_bytes self ⦃ s => s.val = cowList self.1 ⦄ := by
  sorry

/-- `as_str`: the value as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.session_state_change.Unsupported.as_str_spec (self : packets.session_state_change.Unsupported) :
    packets.session_state_change.Unsupported.as_str self ⦃ c => LossyUtf8Valid (cowList self.1) c ⦄ := by
  sorry

/-- `into_owned`: the same bytes. -/
theorem packets.session_state_change.Unsupported.into_owned_spec (self : packets.session_state_change.Unsupported) :
    packets.session_state_change.Unsupported.into_owned self ⦃ x => cowList x.1 = cowList self.1 ⦄ := by
  sorry

/-- `MyDeserialize for Unsupported`: `SIZE` is `None`. -/
theorem packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  sorry

/-- `MyDeserialize for Unsupported`: total; a length-encoded string (`checkedLenencStr`). -/
theorem packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64)
    (buf : io.ParseBuf) :
    packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun x => cowList x.1), rest.val) = checkedLenencStr buf.val ⦄ := by
  sorry

/-- `MySerialize for Unsupported`: appends the value as a length-encoded string. -/
theorem packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.session_state_change.Unsupported)
    (buf : alloc.vec.Vec U8) (h : buf.length + (lenencStr (cowList self.1)).length ≤ Usize.max) :
    packets.session_state_change.Unsupported.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ lenencStr (cowList self.1) ⦄ := by
  sorry

end mysql_common
