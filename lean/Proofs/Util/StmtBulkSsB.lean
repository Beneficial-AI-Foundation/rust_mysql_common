import Defs
import Proofs.Util.PacketsColStmt
import Proofs.Io.ParseBuf
import Proofs.Defs.LemmasG

/-! Helper lemmas for the length-encoded `RawBytes` wrappers of `session_state_change`
(`Proofs/Packets/SessionStateChange/{TransactionCharacteristics,TransactionState,
SessionStateChange}.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.SBSsB

/-- `as_str` of a length-encoded `RawBytes`: the bytes, lossily converted. -/
theorem lenenc_as_str (rb : misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit) :
    misc.raw.bytes.RawBytes.as_str misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple rb
      ⦃ c => LossyUtf8Valid (cowList rb.1) c ⦄ := by
  unfold misc.raw.bytes.RawBytes.as_str
  apply WP.spec_bind (PCSUtil.lenenc_as_bytes rb)
  intro s hs
  unfold misc.trusted.from_utf8_lossy
  apply (WP.spec_ok _).mpr
  intro hu
  rw [← hs] at hu
  have hv := (Defs.isUtf8_iff_isValidUTF8 _).1 hu
  exact ⟨s, by simp [hv], hs⟩

/-- A length-encoded `RawBytes` read through `parse_unchecked`, re-wrapped as the same type:
    `checkedLenencStr`. -/
theorem lenenc_parse_rewrap (h64 : Target64) (buf : io.ParseBuf) :
    (do
      let (r, buf1) ←
        io.ParseBuf.parse_unchecked
          (misc.raw.bytes.RawBytes.Insts.Mysql_commonProtoMyDeserialize
          misc.raw.int.LenEnc.Insts.Mysql_commonMiscRawBytesBytesReprTuple) buf ()
      match r with
      | core.result.Result.Ok rb =>
        ok ((core.result.Result.Ok rb : core.result.Result
          (misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit) core.io.error.Error), buf1)
      | core.result.Result.Err e => ok (core.result.Result.Err e, buf1))
      ⦃ r rest => ((okPart r).map (fun x => cowList x.1), rest.val) = checkedLenencStr buf.val ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  apply WP.spec_bind (PCSUtil.lenenc_raw_deserialize' h64 buf)
  rintro ⟨r, rest⟩ h
  simp only [WP.uncurry'] at h
  cases r <;> simp_all [okPart]

end mysql_common.SBSsB
