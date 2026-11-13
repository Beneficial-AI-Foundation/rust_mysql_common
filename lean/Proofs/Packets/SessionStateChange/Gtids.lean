import Defs
import Proofs.Util.StmtBulkSsA
import Proofs.Util.Shared

/-! Statements for `struct Gtids and its impls` (spec file: `Specs/Packets/SessionStateChange.lean`).
Helper lemmas: `Proofs/Util/StmtBulkSsA.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `Gtids::new(v)`: wraps `v.into()`. -/
theorem packets.session_state_change.Gtids.new_spec {X : Type}
    (into : core.convert.Into X (alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)))
    (v : X) (c : alloc.borrow.Cow (Slice U8) (alloc.vec.Vec U8)) (h : into.into v = ok c) :
    packets.session_state_change.Gtids.new into v ⦃ x => x.1 = c ⦄ := by
  unfold packets.session_state_change.Gtids.new
  apply WP.spec_bind (SBSsA.lenenc_new into v c h)
  intro x hx
  exact (WP.spec_ok _).mpr hx

/-- `as_bytes`: the raw GTID set. -/
theorem packets.session_state_change.Gtids.as_bytes_spec (self : packets.session_state_change.Gtids) :
    packets.session_state_change.Gtids.as_bytes self ⦃ s => s.val = cowList self.1 ⦄ := by
  exact PCSUtil.lenenc_as_bytes self

/-- `as_str`: the GTID set as a string, lossily converted (exact on valid UTF-8). -/
theorem packets.session_state_change.Gtids.as_str_spec (self : packets.session_state_change.Gtids) :
    packets.session_state_change.Gtids.as_str self ⦃ c => LossyUtf8Valid (cowList self.1) c ⦄ := by
  exact Shared.lenenc_as_str self

/-- `into_owned`: the same bytes. -/
theorem packets.session_state_change.Gtids.into_owned_spec (self : packets.session_state_change.Gtids) :
    packets.session_state_change.Gtids.into_owned self ⦃ x => cowList x.1 = cowList self.1 ⦄ := by
  unfold packets.session_state_change.Gtids.into_owned
  apply WP.spec_bind (PCSUtil.raw_into_owned _ self)
  intro x hx
  exact (WP.spec_ok _).mpr hx

/-- `MyDeserialize for Gtids`: `SIZE` is `None`. -/
theorem packets.session_state_change.Gtids.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE_eq :
    packets.session_state_change.Gtids.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE = none := by
  unfold packets.session_state_change.Gtids.Insts.Mysql_commonProtoMyDeserializeDeTuple.SIZE; rfl

/-- `MyDeserialize for Gtids`: total; `gtidsRead` (the encoding byte skipped unchecked, then a length-encoded string). -/
theorem packets.session_state_change.Gtids.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec (h64 : Target64)
    (buf : io.ParseBuf) :
    packets.session_state_change.Gtids.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map (fun x => cowList x.1), rest.val) = gtidsRead buf.val ⦄ := by
  unfold packets.session_state_change.Gtids.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize
  step with io.ParseBuf.checked_skip_spec buf 1#usize as ⟨ b, buf1, hb ⟩
  split_ifs at hb with hlen
  · obtain ⟨rfl, hb1⟩ := hb
    simp only [↓reduceIte]
    step with SBSsA.lenenc_parse h64 buf1 as ⟨ r, rest, hr ⟩
    have hlen' : buf.val ≠ [] := by
      intro h; simp [Slice.length, h] at hlen
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hlen'
    rw [hx] at hb1
    simp only [List.drop_succ_cons, List.drop_zero] at hb1
    rw [hb1] at hr
    simp only [gtidsRead, hx]
    cases r <;> simp_all [okPart]
  · obtain ⟨rfl, hb2⟩ := hb
    rw [hb2]
    have hnil : buf.val = [] := by simpa [Slice.length] using hlen
    simp [misc.unexpected_buf_eof, misc.io_error_msg, gtidsRead, hnil, okPart]

/-- `MySerialize for Gtids`: appends the encoding byte `0`, then the GTID set as a length-encoded string. -/
theorem packets.session_state_change.Gtids.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : packets.session_state_change.Gtids)
    (buf : alloc.vec.Vec U8) (h : buf.length + ((byte 0 :: lenencStr (cowList self.1))).length ≤ Usize.max) :
    packets.session_state_change.Gtids.Insts.Mysql_commonProtoMySerialize.serialize self buf ⦃ buf' =>
      buf'.val = buf.val ++ (byte 0 :: lenencStr (cowList self.1)) ⦄ := by
  unfold packets.session_state_change.Gtids.Insts.Mysql_commonProtoMySerialize.serialize
  step as ⟨ buf1, hbuf1 ⟩
  step with PCSUtil.lenenc_raw_serialize self buf1 (by simp_all; omega) as ⟨ buf2, hbuf2 ⟩
  simp_all [byte]; rfl

end mysql_common
