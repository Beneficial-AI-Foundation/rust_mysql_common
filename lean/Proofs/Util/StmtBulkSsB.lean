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
