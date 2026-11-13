import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf
import Proofs.Io.BufMutExt
import Proofs.Misc.Raw.Int.VarLen

/-! Statements for `impl BytesRepr for VarLen` (spec file: `Specs/Misc/Raw/Bytes.lean`). Proofs: complete. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `VarLen::MAX_LEN`: `u32::MAX`. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN_spec :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN ⦃ m => m.val = 2 ^ 32 - 1 ⦄ := by
  unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.MAX_LEN
  simp [core.num.U32.MAX, U32.rMax]

/-- `VarLen::SIZE` is `None`. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE_eq :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE = none := by
  unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.SIZE; rfl

/-- `VarLen::serialize`: **Bug (format mismatch).** Appends the length as a *length-encoded integer*
    (`put_lenenc_int`), not as a JSONB varlen integer, which is what `deserialize` reads. The two
    agree only for lengths below 128. From 128 on the first length byte has bit 7 set, so
    `deserialize` takes the following byte(s) as part of the length and can silently read a wrong
    length: e.g. a 200-byte string starting with `'a'` is read as having length 12488
    (`Defs.jsonbVarLenRead_lenencInt_misread`); see `roundtrip_fails`. No `u32::MAX` truncation
    either. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize_spec (text : Slice U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + (lenencInt text.length).length + text.length ≤ Usize.max) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize text buf ⦃ buf' => buf'.val = buf.val ++ lenencInt text.length ++ text.val ⦄ := by
  unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.serialize
  step as ⟨ i1, hi1 ⟩
  have hi1' : i1.val = text.length := by subst hi1; simp
  step with io.BufMutExt.put_lenenc_int_spec buf i1 (by rw [hi1']; scalar_tac) as ⟨ v, hv ⟩
  step as ⟨ w, hw ⟩
  simp [hw, hv, hi1']

/-- `VarLen::deserialize`: total; a JSONB-varlen length then that many bytes (`jsonbVarLenStrRead`). -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest =>
      ((okPart r).map cowList, rest.val) = jsonbVarLenStrRead buf.val ⦄ := by
  unfold misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize
  step with misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf as ⟨ r, buf1, hr ⟩
  cases r with
  | Err e =>
    simp only [okPart, Option.map_none] at hr
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, okPart,
      jsonbVarLenStrRead, ← hr]
  | Ok val =>
    obtain ⟨i, _⟩ := val
    simp only [okPart, Option.map] at hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨ i1, hi1 ⟩
    have hi1' : i1.val = i.val := by
      subst hi1; apply UScalar.cast_val_mod_pow_of_inBounds_eq
      have : (2:Nat) ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
        apply Nat.pow_le_pow_right (by omega)
        rcases System.Platform.numBits_eq with h | h <;> simp [h]
      scalar_tac
    step with io.ParseBuf.checked_eat_spec buf1 i1 as ⟨ o, buf2, ho ⟩
    simp only [jsonbVarLenStrRead, ← hr]
    split at ho
    · obtain ⟨ho1, ho2⟩ := ho
      cases o with
      | none => simp at ho1
      | some x =>
        simp at ho1
        rw [hi1'] at *
        simp [okPart, cowList, ho1, ho2, ‹i.val ≤ Slice.length buf1›]
    · obtain ⟨ho1, ho2⟩ := ho
      subst ho1 ho2
      rw [hi1'] at *
      simp [okPart, misc.unexpected_buf_eof, misc.io_error_msg, ‹¬ i.val ≤ Slice.length buf2›]

/-- Round trip of `serialize` holds only for strings shorter than 128 bytes (see the bug on `serialize`). -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip (s : List U8) (hs : s.length < 128) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = lenencInt s.length ++ s ++ tail) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => (okPart r).map cowList = some s ∧ rest.val = tail ⦄ := by
  have hl : lenencInt s.length = [byte s.length] := by simp [lenencInt]; omega
  have hb : (byte s.length).val = s.length := by
    show (BitVec.ofNat 8 s.length).toNat = s.length
    simp; omega
  have hc : jsonbVarLenStrRead buf.val = (some s, tail) := by
    rw [h, hl]
    have hj : jsonbVarLenRead (byte s.length :: (s ++ tail)) = (some s.length, s ++ tail) := by
      simp [jsonbVarLenRead, List.findIdx?_cons, hb, hs, base128]
      omega
    simp only [List.cons_append, List.nil_append]
    rw [jsonbVarLenStrRead, hj]
    simp
  apply WP.spec_mono (misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf)
  rintro ⟨r, rest⟩ hr
  simp only [hc, WP.uncurry'_pair, Prod.mk.injEq] at hr
  exact hr

private theorem byte_val (k : Nat) : (byte k).val = k % 256 := by
  show (BitVec.ofNat 8 k).toNat = k % 256
  simp

private theorem fd_arith (a b c : Nat) (ha : 128 ≤ a) (ha' : a < 256) (hb : 128 ≤ b) (hb' : b < 256)
    (hc : c < 128) (h : a + 256 * b + 65536 * c = 125 + 128 * (a % 128 + 128 * (b % 128 + 128 * c))) :
    False := by
  omega

private theorem fd_no_solution (n : Nat) (h1 : 128 ≤ n % 256) (h2 : 128 ≤ n / 256 % 256)
    (hb : n / 256 / 256 % 256 < 128) (hlt : n < 16777216)
    (hmv : n = 125 + 128 * (n % 128 + 128 * (n / 256 % 128 + 128 * (n / 256 / 256 % 128)))) : False := by
  have k1 : n % 128 = n % 256 % 128 := (Nat.mod_mod_of_dvd _ (by decide)).symm
  have k2 : n / 256 % 128 = n / 256 % 256 % 128 := (Nat.mod_mod_of_dvd _ (by decide)).symm
  have e1 := Nat.mod_add_div n 256
  have e2 := Nat.mod_add_div (n / 256) 256
  have e3 : n / 256 / 256 < 128 := by
    have : n / 256 / 256 < 256 := by
      rw [Nat.div_div_eq_div_mul]; exact Nat.div_lt_of_lt_mul (by simpa using hlt)
    rw [Nat.mod_eq_of_lt this] at hb; exact hb
  rw [k1, k2, Nat.mod_eq_of_lt e3] at hmv
  have ha' := Nat.mod_lt n (show 256 > 0 by decide)
  have hb' := Nat.mod_lt (n / 256) (show 256 > 0 by decide)
  clear k1 k2 hb hlt
  generalize n / 256 / 256 = c at *
  generalize n / 256 % 256 = b at *
  generalize n / 256 = q at *
  generalize n % 256 = a at *
  subst e2
  exact fd_arith a b c h1 ha' h2 hb' e3 (by omega)

private theorem fc_arith (a b : Nat) (ha : 128 ≤ a) (ha' : a < 256) (_hb : b < 128)
    (h : a + 256 * b = 124 + 128 * (a % 128 + 128 * b)) : False := by
  omega

private theorem fc_no_solution (n : Nat) (h1 : 128 ≤ n % 256)
    (hb : n / 256 % 256 < 128) (hlt : n < 65536)
    (hmv : n = 124 + 128 * (n % 128 + 128 * (n / 256 % 128))) : False := by
  have k1 : n % 128 = n % 256 % 128 := (Nat.mod_mod_of_dvd _ (by decide)).symm
  have e1 := Nat.mod_add_div n 256
  have e3 : n / 256 < 128 := by
    have : n / 256 < 256 := Nat.div_lt_of_lt_mul (by simpa using hlt)
    rw [Nat.mod_eq_of_lt this] at hb; exact hb
  rw [k1, Nat.mod_eq_of_lt e3] at hmv
  have ha' := Nat.mod_lt n (show 256 > 0 by decide)
  clear k1 hb hlt
  generalize n / 256 = b at *
  generalize n % 256 = a at *
  exact fc_arith a b h1 ha' e3 (by omega)

private theorem jsonbVarLenRead_some {bs : List U8} {m : Nat} {rest : List U8}
    (h : jsonbVarLenRead bs = (some m, rest)) :
    ∃ j, j < 5 ∧ j < bs.length ∧ rest = bs.drop (j+1) ∧ m = base128 (bs.take (j+1)) ∧
      (∃ b, bs[j]? = some b ∧ b.val < 128) ∧ ∀ i < j, ∀ b, bs[i]? = some b → 128 ≤ b.val := by
  unfold jsonbVarLenRead at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i j hj
    rw [List.findIdx?_eq_some_iff_getElem] at hj
    obtain ⟨hjl, hp, hlt⟩ := hj
    simp only [List.length_take] at hjl
    split at h
    · simp only [Prod.mk.injEq, Option.some.injEq] at h
      refine ⟨j, by omega, by omega, h.2.symm, h.1.symm, ⟨bs[j]'(by omega), by simp, ?_⟩, ?_⟩
      · simpa using hp
      · intro i hi b hb
        have := hlt i hi
        simp only [List.getElem_take, decide_eq_true_eq, not_lt] at this
        rw [List.getElem?_eq_getElem (by omega)] at hb
        simp only [Option.some.injEq] at hb
        rw [← hb]; exact this
    · simp at h

/-- **Bug (format mismatch).** For every length `≥ 128`, `deserialize` does not read back what
    `serialize` writes: it fails or leaves a different rest. (From 128 to 250 the single lenenc
    byte has bit 7 set; from 251 on the lenenc header is `0xFC`/`0xFD`/`0xFE` plus 2/3/8 bytes, and
    the JSONB reader never stops after exactly the header with the right value: for `0xFC`/`0xFD`
    the equations have no solution, and the 9-byte `0xFE` header is longer than the 5 bytes the
    JSONB reader accepts.) -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.roundtrip_fails (s tail : List U8) (hs : 128 ≤ s.length ∧ s.length < 2 ^ 64)
    (buf : io.ParseBuf) (h : buf.val = lenencInt s.length ++ s ++ tail) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize () buf ⦃ r rest => ((okPart r).map cowList, rest.val) ≠ (some s, tail) ⦄ := by
  apply WP.spec_mono (misc.raw.int.VarLen.Insts.Mysql_commonMiscRawBytesBytesReprTuple.deserialize_spec buf)
  rintro ⟨r, rest'⟩ hr hc
  simp only [WP.uncurry'_pair] at hr hc
  have hstr : jsonbVarLenStrRead buf.val = (some s, tail) := by rw [← hr, hc]
  rw [h] at hstr
  unfold jsonbVarLenStrRead at hstr
  split at hstr
  · simp at hstr
  · rename_i m rest hm
    split at hstr
    · rename_i hle
      simp only [Prod.mk.injEq, Option.some.injEq] at hstr
      obtain ⟨hs1, hs2⟩ := hstr
      have hmn : m = s.length := by rw [← hs1]; simp; omega
      have hrest : rest = s ++ tail := by rw [← hs1, ← hs2, List.take_append_drop]
      obtain ⟨j, hj5, hjl, hr, hmv, ⟨b, hb, hb128⟩, hbig⟩ := jsonbVarLenRead_some hm
      have hlen : (lenencInt s.length).length = j + 1 := by
        have := congrArg List.length hr
        simp [hrest] at this hjl; omega
      have hP : (lenencInt s.length ++ s ++ tail).take (j+1) = lenencInt s.length := by
        rw [← hlen, List.append_assoc, List.take_left]
      rw [hP, hmn] at hmv
      by_cases c1 : s.length < 251
      · have hL : lenencInt s.length = [byte s.length] := by simp [lenencInt, c1]
        rw [hL] at hlen hb; simp at hlen; subst hlen
        simp at hb; subst hb; simp [byte_val] at hb128; omega
      by_cases c2 : s.length < 65536
      · have hL : lenencInt s.length = [byte 252, byte s.length, byte (s.length/256)] := by
          simp [lenencInt, c1, c2, leBytes]
        rw [hL] at hlen hb hbig hmv; simp at hlen; subst hlen
        have h1 := hbig 1 (by omega) (byte s.length) (by simp)
        simp at hb; subst hb
        simp only [byte_val] at hb128 h1
        simp [base128, byte_val] at hmv
        exact fc_no_solution _ h1 hb128 c2 hmv
      by_cases c3 : s.length < 16777216
      · have hL : lenencInt s.length =
            [byte 253, byte s.length, byte (s.length/256), byte (s.length/256/256)] := by
          simp [lenencInt, c1, c2, c3, leBytes]
        rw [hL] at hlen hb hbig hmv; simp at hlen; subst hlen
        have h1 := hbig 1 (by omega) (byte s.length) (by simp)
        have h2 := hbig 2 (by omega) (byte (s.length/256)) (by simp)
        simp at hb; subst hb
        simp only [byte_val] at hb128 h1 h2
        simp [base128, byte_val] at hmv
        exact fd_no_solution _ h1 h2 hb128 c3 hmv
      · have : (lenencInt s.length).length = 9 := by simp [lenencInt, c1, c2, c3, leBytes]
        omega
    · simp at hstr

end mysql_common
