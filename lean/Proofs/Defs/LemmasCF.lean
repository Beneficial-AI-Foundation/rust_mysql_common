import Defs
import Proofs.Defs.Lemmas
import Proofs.Util.ParseBuf

/-! Facts about the stage c–f definitions (spec file: `Specs/DefsCF.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common

namespace Defs

private theorem bitsToNat_lt (l : List Bool) : bitsToNat l < 2 ^ l.length := by
  induction l with
  | nil => simp [bitsToNat]
  | cons b l ih => simp only [bitsToNat, List.length_cons, pow_succ]; split <;> omega

private theorem testBit_bitsToNat (l : List Bool) (k : Nat) : (bitsToNat l).testBit k = l.getD k false := by
  induction l generalizing k with
  | nil => simp [bitsToNat]
  | cons b l ih =>
    cases k with
    | zero => simp only [bitsToNat, Nat.testBit_zero]; cases b <;> simp
    | succ k =>
      rw [Nat.testBit_succ, show (bitsToNat (b :: l)) / 2 = bitsToNat l by simp only [bitsToNat]; split <;> omega, ih]
      simp

/-- A NULL bitmap has `nullBitmapLen` bytes, and its bit for field `i` is `nulls[i]`. -/
theorem nullBitmap_spec (off : Nat) (nulls : List Bool) :
    (nullBitmap off nulls).length = nullBitmapLen off nulls.length ∧
    ∀ i, bitmapBit off (nullBitmap off nulls) i = nulls.getD i false := by
  refine ⟨by simp [nullBitmap], fun i => ?_⟩
  simp only [bitmapBit, bitAt, nullBitmap]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hj : (i + off) / 8 < nullBitmapLen off nulls.length
  · rw [List.getElem?_range hj]
    simp only [Option.map_some, Option.getD_some]
    set c := ((List.replicate off false ++ nulls).drop (8 * ((i + off) / 8))).take 8 with hc
    have hcl : c.length ≤ 8 := by simp [hc]
    have hlt : bitsToNat c < 256 :=
      lt_of_lt_of_le (bitsToNat_lt c) (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hcl)
    rw [PBUtil.byte_val, Nat.mod_eq_of_lt hlt, testBit_bitsToNat, hc]
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (Nat.mod_lt _ (by norm_num)),
      List.getElem?_drop, show 8 * ((i + off) / 8) + (i + off) % 8 = off + i by omega,
      List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left,
      ← List.getD_eq_getElem?_getD]
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp only [Option.map_none, Option.getD_none, PBUtil.byte_val, Nat.zero_mod, Nat.zero_testBit]
    have : nulls.length ≤ i := by simp only [nullBitmapLen] at hj; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]; rfl

private theorem checkedLenencStr_lenencStr' (s t : List U8) (hs : s.length < 2 ^ 64) :
    checkedLenencStr (lenencStr s ++ t) = (some s, t) := by
  simp only [lenencStr, checkedLenencStr, List.append_assoc, PBUtil.checkedLenencInt_lenencInt _ _ hs]
  simp

private theorem textRead_lenencStr' (s t : List U8) (hs : s.length < 2 ^ 64) :
    textRead (lenencStr s ++ t) = (some (.bytes s), t) := by
  have hc := checkedLenencStr_lenencStr' s t hs
  obtain ⟨b, r, he, hb⟩ : ∃ b r, lenencStr s ++ t = b :: r ∧ b.val ≠ 0xFB := by
    simp only [lenencStr, lenencInt]
    split_ifs with h1 h2 h3
    · exact ⟨_, _, rfl, by rw [PBUtil.byte_val]; omega⟩
    · exact ⟨_, _, rfl, by rw [PBUtil.byte_val]; omega⟩
    · exact ⟨_, _, rfl, by rw [PBUtil.byte_val]; omega⟩
    · exact ⟨_, _, rfl, by rw [PBUtil.byte_val]; omega⟩
  rw [he]; simp only [textRead, hb, ↓reduceIte]; rw [← he, hc]

/-- The text-row reader reads back a row of `NULL`s and byte strings. -/
theorem textRowRead_textEnc (vs : List Val) (hv : ∀ v ∈ vs, isTextVal v = true)
    (hs : ∀ s, Val.bytes s ∈ vs → s.length < 2 ^ 64) (t : List U8) :
    textRowRead vs.length ((vs.map textEnc).flatten ++ t) = (some vs, t) := by
  induction vs with
  | nil => simp [textRowRead]
  | cons v vs ih =>
    have ih' := ih (fun w hw => hv w (List.mem_cons_of_mem _ hw))
      (fun s hm => hs s (List.mem_cons_of_mem _ hm))
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, textRowRead]
    have hv0 := hv v List.mem_cons_self
    cases v with
    | null =>
      simp only [textEnc, List.singleton_append, textRead, PBUtil.byte_val]
      simp [ih', consRead]
    | bytes s =>
      simp only [textEnc]
      rw [textRead_lenencStr' _ _ (hs s List.mem_cons_self)]
      simp [ih', consRead]
    | _ => simp [isTextVal] at hv0

private theorem leBytesI_eq (k : Nat) (x : Int) :
    leBytesI k x = leBytes k (x % (2 ^ (8 * k) : Int)).toNat := rfl

private theorem emod_toNat_lt (k : Nat) (x : Int) : (x % (2 ^ (8 * k) : Int)).toNat < 2 ^ (8 * k) := by
  have hP : (0 : Int) < 2 ^ (8 * k) := by positivity
  have h1 := Int.emod_lt_of_pos x hP
  have h2 := Int.emod_nonneg x (ne_of_gt hP)
  have hc : ((2 ^ (8 * k) : Nat) : Int) = (2 : Int) ^ (8 * k) := by norm_cast
  omega

private theorem readIntVal_int (k : Nat) (hk : 0 < k) (u : Bool) (x : Int)
    (hr : if u = true then 0 ≤ x ∧ x < 2 ^ (8 * k) else -2 ^ (8 * k - 1) ≤ x ∧ x < 2 ^ (8 * k - 1))
    (t : List U8) : readIntVal k u (leBytesI k x ++ t) = (some (.int x), t) := by
  have hn := emod_toNat_lt k x
  have hl : leNat (leBytesI k x) = (x % (2 ^ (8 * k) : Int)).toNat := by
    rw [leBytesI_eq, PBUtil.leNat_leBytes, Nat.mod_eq_of_lt hn]
  simp only [readIntVal, leBytesI_eq, PBUtil.readLE_leBytes _ _ _ hn]
  cases u with
  | true =>
    simp only [↓reduceIte] at hr ⊢
    rw [Int.emod_eq_of_lt hr.1 hr.2, Int.toNat_of_nonneg hr.1]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
    rw [← hl, toSigned_leNat_leBytesI k x hk hr]

private theorem readIntVal_uint (k : Nat) (u : Bool) (x : Nat)
    (hr : x < if u = true then 2 ^ (8 * k) else 2 ^ (8 * k - 1))
    (t : List U8) : readIntVal k u (leBytes k x ++ t) = (some (.int x), t) := by
  have h2 : 2 ^ (8 * k - 1) ≤ 2 ^ (8 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn : x < 2 ^ (8 * k) := by split at hr <;> omega
  simp only [readIntVal, PBUtil.readLE_leBytes _ _ _ hn]
  cases u with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
    rw [PBUtil.toSigned_of_lt _ _ hr]

private theorem binRead_narrow (ct : constants.ColumnType) (k : Nat) (hw : intWidth ct = some k)
    (u : Bool) (bs : List U8) : binRead ct u bs = readIntVal k u bs := by
  cases ct <;> simp [intWidth] at hw <;> subst hw <;> rfl

/-- The binary value decoder reads back a `Value` encoded at its column's type (`binEncAt`), when it fits the column (`binFitsAt`), up to `binNormAt`. -/
theorem binRead_binEncAt (ct : constants.ColumnType) (unsigned : Bool) (v : value.Value)
    (hf : binFitsAt ct unsigned (Val.ofValue v)) (t : List U8) :
    binRead ct unsigned (binEncAt ct (Val.ofValue v) ++ t) = (some (binNormAt ct unsigned (Val.ofValue v)), t) := by
  cases hw : intWidth ct with
  | none =>
    have e1 : binEncAt ct (Val.ofValue v) = binEnc (Val.ofValue v) := by simp only [binEncAt, hw]
    have e2 : binNormAt ct unsigned (Val.ofValue v) = binNorm unsigned (Val.ofValue v) := by
      simp only [binNormAt, hw]
    have hc : binCompatible (Val.ofValue v) ct := by simpa [binFitsAt, hw] using hf
    rw [e1, e2]; exact binRead_binEnc v ct unsigned t hc
  | some k =>
    have hk : 0 < k := by cases ct <;> simp [intWidth] at hw <;> omega
    simp only [binFitsAt, hw] at hf
    rw [binRead_narrow ct k hw]
    rcases hf with ⟨x, hx, hr⟩ | ⟨x, hx, hr⟩
    · rw [hx]; simp only [binEncAt, binNormAt, hw]; exact readIntVal_int k hk unsigned x hr t
    · rw [hx]; simp only [binEncAt, binNormAt, hw]; exact readIntVal_uint k unsigned x hr t

/-- Every column type's code is a byte, and decodes back to it. -/
theorem columnTypeOfCode_columnTypeCode (ct : constants.ColumnType) :
    columnTypeCode ct < 256 ∧ columnTypeOfCode (columnTypeCode ct) = some ct := by
  cases ct <;> exact ⟨by simp [columnTypeCode], rfl⟩

private theorem lenencStrs_flatten (ss : List (List U8)) (hs : ∀ s ∈ ss, s.length < 2 ^ 64) (r : List U8) :
    lenencStrs ss.length ((ss.map lenencStr).flatten ++ r) = (some ss, r) := by
  induction ss with
  | nil => simp [lenencStrs]
  | cons s ss ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, lenencStrs,
      checkedLenencStr_lenencStr' _ _ (hs s List.mem_cons_self),
      ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))]

private theorem colDef_strs (c : ColDef) (X : List U8) :
    lenencStr c.catalog ++ lenencStr c.schema ++ lenencStr c.table ++ lenencStr c.orgTable
      ++ lenencStr c.colName ++ lenencStr c.orgName ++ X =
    ([c.catalog, c.schema, c.table, c.orgTable, c.colName, c.orgName].map lenencStr).flatten ++ X := by
  simp [List.append_assoc]

private theorem leBytes_two (n : Nat) : leBytes 2 n = [byte n, byte (n / 256)] := by simp [leBytes]

private theorem leBytes_four (n : Nat) :
    leBytes 4 n = [byte n, byte (n / 256), byte (n / 256 / 256), byte (n / 256 / 256 / 256)] := by
  simp [leBytes]

/-- The crate's column definition reader reads back the protocol layout (fields in range). -/
theorem colDefRead_colDefEnc (c : ColDef) (t : List U8)
    (hs : ∀ s ∈ [c.catalog, c.schema, c.table, c.orgTable, c.colName, c.orgName], s.length < 2 ^ 64)
    (hc : c.charset < 2 ^ 16) (hl : c.length < 2 ^ 32) (hf : c.flags < 2 ^ 16) (hd : c.decimals < 256) :
    colDefRead (colDefEnc c ++ t) = (some c, t) := by
  obtain ⟨hct, hty⟩ := columnTypeOfCode_columnTypeCode c.type
  have e : colDefEnc c ++ t = ([c.catalog, c.schema, c.table, c.orgTable, c.colName, c.orgName].map lenencStr).flatten
      ++ ([byte 0x0c] ++ leBytes 2 c.charset ++ leBytes 4 c.length ++ [byte (columnTypeCode c.type)]
        ++ leBytes 2 c.flags ++ [byte c.decimals, byte 0, byte 0] ++ t) := by
    rw [← colDef_strs]; simp [colDefEnc, List.append_assoc]
  rw [colDefRead, e, show 6 = [c.catalog, c.schema, c.table, c.orgTable, c.colName, c.orgName].length from rfl,
    lenencStrs_flatten _ hs]
  simp only [leBytes_two, leBytes_four, List.cons_append, List.nil_append]
  simp [PBUtil.byte_val, Nat.mod_eq_of_lt hct, hty, leNat]
  split_ifs with h13
  · omega
  · obtain ⟨a1, a2, a3, a4, a5, a6, cs, len, ty, fl, dec⟩ := c
    simp only at hc hl hf hd ⊢
    simp only [Prod.mk.injEq, Option.some.injEq, ColDef.mk.injEq, true_and, and_true]
    refine ⟨by omega, by omega, by omega, by omega⟩

/-- **The `Column` serialization bug, made precise**: what `MySerialize for Column` writes (`colDefEncCrate`) is read back by the crate's own reader without an error, but with `character_set` the low 16 bits of the column length and `column_length` the rest of the length plus the character set shifted by 16 bits. -/
theorem colDefRead_colDefEncCrate (c : ColDef) (t : List U8)
    (hs : ∀ s ∈ [c.catalog, c.schema, c.table, c.orgTable, c.colName, c.orgName], s.length < 2 ^ 64)
    (hc : c.charset < 2 ^ 16) (hl : c.length < 2 ^ 32) (hf : c.flags < 2 ^ 16) (hd : c.decimals < 256) :
    colDefRead (colDefEncCrate c ++ t) =
      (some { c with charset := c.length % 2 ^ 16, length := c.length / 2 ^ 16 + 2 ^ 16 * c.charset }, t) := by
  obtain ⟨hct, hty⟩ := columnTypeOfCode_columnTypeCode c.type
  have e : colDefEncCrate c ++ t = ([c.catalog, c.schema, c.table, c.orgTable, c.colName, c.orgName].map lenencStr).flatten
      ++ ([byte 0x0c] ++ leBytes 4 c.length ++ leBytes 2 c.charset ++ [byte (columnTypeCode c.type)]
        ++ leBytes 2 c.flags ++ [byte c.decimals, byte 0, byte 0] ++ t) := by
    rw [← colDef_strs]; simp [colDefEncCrate, List.append_assoc]
  rw [colDefRead, e, show 6 = [c.catalog, c.schema, c.table, c.orgTable, c.colName, c.orgName].length from rfl,
    lenencStrs_flatten _ hs]
  simp only [leBytes_two, leBytes_four, List.cons_append, List.nil_append]
  simp [PBUtil.byte_val, Nat.mod_eq_of_lt hct, hty, leNat]
  split_ifs with h13
  · omega
  · obtain ⟨a1, a2, a3, a4, a5, a6, cs, len, ty, fl, dec⟩ := c
    simp only at hc hl hf hd ⊢
    simp only [Prod.mk.injEq, Option.some.injEq, ColDef.mk.injEq, true_and, and_true]
    refine ⟨by omega, by omega, by omega, by omega⟩

private theorem lenencStr_ne_nil (s : List U8) : lenencStr s ≠ [] := by
  simp only [lenencStr, lenencInt]; split_ifs <;> simp

private theorem lenencStr_head (s : List U8) (hs : s ≠ []) (h64 : s.length < 2 ^ 64) :
    ∃ b r, lenencStr s = b :: r ∧ 0 < b.val := by
  have hp : 0 < s.length := List.length_pos_of_ne_nil hs
  simp only [lenencStr, lenencInt]
  split_ifs with h1 h2 h3
  · exact ⟨_, _, rfl, by rw [PBUtil.byte_val]; omega⟩
  · exact ⟨_, _, rfl, by rw [PBUtil.byte_val]; omega⟩
  · exact ⟨_, _, rfl, by rw [PBUtil.byte_val]; omega⟩
  · exact ⟨_, _, rfl, by rw [PBUtil.byte_val]; omega⟩

private theorem okStatusRead_enc (st w : Nat) (hs : st < 2 ^ 16) (hw : w < 2 ^ 16) (T : List U8) :
    okStatusRead (leBytes 2 st ++ (leBytes 2 w ++ T)) = ((statusRead st).map (fun s => (s, w)), T) := by
  simp only [leBytes_two, List.cons_append, List.nil_append, okStatusRead]
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, leNat,
    PBUtil.byte_val, List.length_cons]
  have h4 : ¬ (T.length + 1 + 1 + 1 + 1 < 4) := by omega
  have e1 : st % 256 + 256 * (st / 256 % 256 + 256 * 0) = st := by omega
  have e2 : w % 256 + 256 * (w / 256 % 256 + 256 * 0) = w := by omega
  simp only [h4, ↓reduceIte, e1, e2]

private theorem okTailRead_enc (caps : Nat) (compact : Bool) (b : OkBody)
    (hssi : (hasFlag caps CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = [])
    (hl : b.info.length < 2 ^ 64 ∧ b.sessionStateInfo.length < 2 ^ 64) :
    okTailRead caps b.status
      (if hasFlag caps CLIENT_SESSION_TRACK then
          (if compact ∧ b.info = [] ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED = false then []
           else lenencStr b.info)
            ++ (if hasFlag b.status SERVER_SESSION_STATE_CHANGED then lenencStr b.sessionStateInfo else [])
        else if b.info = [] then [] else lenencStr b.info) = (some (b.info, b.sessionStateInfo), []) := by
  obtain ⟨hl1, hl2⟩ := hl
  by_cases hcst : hasFlag caps CLIENT_SESSION_TRACK = true
  · by_cases hssc : hasFlag b.status SERVER_SESSION_STATE_CHANGED = true
    · have hne : lenencStr b.info ++ lenencStr b.sessionStateInfo ≠ [] := by simp [lenencStr_ne_nil]
      simp only [hcst, hssc, ↓reduceIte, Bool.true_eq_false, and_false, okTailRead, ne_eq, hne,
        not_false_eq_true, and_self, checkedLenencStr_lenencStr' _ _ hl1]
      rw [← List.append_nil (lenencStr b.sessionStateInfo), checkedLenencStr_lenencStr' _ _ hl2]
    · have hs0 : b.sessionStateInfo = [] := by simp_all
      simp only [Bool.not_eq_true] at hssc
      simp only [hcst, hssc, ↓reduceIte, Bool.false_eq_true, List.append_nil, and_true, okTailRead, hs0]
      by_cases hci : compact = true ∧ b.info = []
      · simp [hci]
      · have hne : lenencStr b.info ≠ [] := lenencStr_ne_nil _
        simp only [hci, ↓reduceIte, ne_eq, hne, not_false_eq_true, and_self]
        rw [← List.append_nil (lenencStr b.info), checkedLenencStr_lenencStr' _ _ hl1]
  · have hs0 : b.sessionStateInfo = [] := by simp_all
    simp only [Bool.not_eq_true] at hcst
    simp only [hcst, Bool.false_eq_true, ↓reduceIte, okTailRead, false_and, hs0]
    by_cases hi : b.info = []
    · simp [hi]
    · obtain ⟨b0, r0, he, hb0⟩ := lenencStr_head b.info hi hl1
      simp only [hi, ↓reduceIte, he, hb0]
      rw [← he, ← List.append_nil (lenencStr b.info), checkedLenencStr_lenencStr' _ _ hl1]

/-- The OK packet reader reads back both forms of an OK packet (status with known flags, session state only when both flags are set). -/
theorem okPacketRead_okPacketEnc (caps : Nat) (compact : Bool) (b : OkBody)
    (hb : b.affectedRows < 2 ^ 64 ∧ b.lastInsertId < 2 ^ 64 ∧ b.status < 2 ^ 16 ∧
      statusRead b.status = some b.status ∧ b.warnings < 2 ^ 16)
    (hssi : (hasFlag caps CLIENT_SESSION_TRACK ∧ hasFlag b.status SERVER_SESSION_STATE_CHANGED) ∨
      b.sessionStateInfo = [])
    (hl : b.info.length < 2 ^ 64 ∧ b.sessionStateInfo.length < 2 ^ 64) :
    okPacketRead .commonOk caps (okPacketEnc 0x00 caps compact b) = (some b.toPkt, []) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  have ht := okTailRead_enc caps compact b hssi hl
  simp only [okPacketEnc, List.cons_append, okPacketRead, OkKind.header, PBUtil.byte_val, OkKind.bodyRead, List.append_assoc,
    okBodyRead, PBUtil.checkedLenencInt_lenencInt _ _ h1, PBUtil.checkedLenencInt_lenencInt _ _ h2,
    okStatusRead_enc _ _ h3 h5, h4, Option.map_some, ht, Nat.zero_mod, ne_eq, not_true_eq_false, ↓reduceIte]

private theorem leBytes_three (n : Nat) : leBytes 3 n = [byte n, byte (n / 256), byte (n / 256 / 256)] := by
  simp [leBytes]

/-- The ERR packet reader reads back a packet that fits the capabilities. -/
theorem errPacketRead_errPacketEnc (caps : Nat) (e : ErrPkt) (hc : errCompatible caps e)
    (hcode : ∀ code st msg, e = .error code st msg → code < 2 ^ 16 ∧ ∀ s, st = some s → s.length = 5)
    (hp : ∀ p, e = .progress p → p.stage < 256 ∧ p.maxStage < 256 ∧ p.info.length < 2 ^ 64) :
    errPacketRead caps (errPacketEnc e) = (some e, []) := by
  cases e with
  | error code state msg =>
    obtain ⟨hc1, hs⟩ := hcode code state msg rfl
    obtain ⟨hi, hff⟩ := hc
    have ecode : code % 256 + 256 * (code / 256 % 256 + 256 * 0) = code := by omega
    have hnp : ¬ (code = 0xFFFF ∧ hasFlag caps CLIENT_PROGRESS_OBSOLETE = true) := by
      rintro ⟨h1, h2⟩; rcases hff with h | h <;> simp_all
    cases state with
    | none =>
      have h41 : hasFlag caps CLIENT_PROTOCOL_41 = false := by simpa using hi
      simp only [errPacketEnc, leBytes_two, List.cons_append, List.nil_append, errPacketRead,
        List.length_cons, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, leNat,
        PBUtil.byte_val, ecode, List.getD_cons_zero, serverErrorRead, h41]
      split_ifs <;> first | rfl | omega | simp_all
    | some s =>
      have h41 : hasFlag caps CLIENT_PROTOCOL_41 = true := by simpa using hi
      have h5 := hs s rfl
      have htk : (s ++ msg).take 5 = s := by
        rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
      have hdr : (s ++ msg).drop 5 = msg := by
        rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
      simp only [errPacketEnc, leBytes_two, List.cons_append, List.nil_append, errPacketRead,
        List.length_cons, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, leNat,
        PBUtil.byte_val, ecode, List.getD_cons_zero, serverErrorRead, h41, htk, hdr, List.length_append, h5]
      split_ifs <;> first | rfl | omega
  | progress p =>
    obtain ⟨hst, hms, hil⟩ := hp p rfl
    obtain ⟨hpf, hpr⟩ := hc
    have epr : p.progress % 256 + 256 * (p.progress / 256 % 256 + 256 * (p.progress / 256 / 256 % 256 + 256 * 0))
        = p.progress := by omega
    have hcl : checkedLenencStr (lenencStr p.info) = (some p.info, []) := by
      simpa using checkedLenencStr_lenencStr' p.info [] hil
    simp only [errPacketEnc, progressEnc, leBytes_two, leBytes_three, List.cons_append, List.nil_append,
      errPacketRead, progressRead, List.length_cons, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
      List.take_zero, leNat, PBUtil.byte_val, List.getD_cons_zero, List.getD_cons_succ, hpf, hcl,
      Nat.mod_eq_of_lt hst, Nat.mod_eq_of_lt hms, epr]
    split_ifs <;> first | rfl | omega | simp_all


/-! ## Packet framing -/

/-- An empty payload is one empty chunk. -/
theorem frame_nil (seq : Nat) : frame seq [] = [byte 0, byte 0, byte 0, byte seq] := by
  rw [frame]
  simp [leBytes, maxPayloadLen]

/-- A payload shorter than `2^24 - 1` is one chunk. -/
theorem frame_short (seq : Nat) (p : List U8) (h : p.length < maxPayloadLen) :
    frame seq p = leBytes 3 p.length ++ byte seq :: p := by
  rw [frame]
  simp [h]

/-- The chunks of a payload: its bytes plus a 4-byte header per chunk. -/
theorem frame_length (seq : Nat) (p : List U8) :
    (frame seq p).length = p.length + 4 * frameCount p.length := by
  induction h : p.length using Nat.strong_induction_on generalizing seq p with
  | _ n ih =>
    rw [frame]
    split_ifs with hp
    · simp [frameCount, Nat.div_eq_of_lt (h ▸ hp)]; omega
    · have hM : maxPayloadLen = 2 ^ 24 - 1 := rfl
      have h1 := ih (n - maxPayloadLen) (by rw [hM] at hp ⊢; omega) (seq + 1) (p.drop maxPayloadLen) (by simp [h])
      simp only [List.length_append, List.length_cons, PBUtil.length_leBytes, List.length_take, h1, h, frameCount]
      have : n / maxPayloadLen = (n - maxPayloadLen) / maxPayloadLen + 1 := by
        rw [hM] at hp ⊢; omega
      rw [this]; rw [hM] at hp ⊢; omega

/-- One step of the chunk reader keeps the state valid. -/
theorem chunkStep_valid (st : ChunkState) (hv : st.Valid) (src dst : List U8) (max : Nat) :
    (chunkStep st src dst max).2.1.Valid := by
  cases st with
  | idle =>
    simp only [chunkStep]
    split_ifs with h1 h2 h3 h4 <;> simp_all [ChunkState.Valid]
    have := PBUtil.leNat_lt (src.take 3)
    have : 2 ^ (8 * (src.take 3).length) ≤ 2 ^ 24 :=
      Nat.pow_le_pow_right (by norm_num) (by simp; omega)
    omega
  | chunk seq len =>
    simp only [chunkStep]
    split_ifs <;> simp_all [ChunkState.Valid]

private theorem chunkStep_middle_len (st : ChunkState) (src dst : List U8) (max : Nat) (s : U8)
    (st' : ChunkState) (src' dst' : List U8)
    (h : chunkStep st src dst max = (.Ok (some (.Middle s)), st', src', dst')) :
    src'.length + 4 ≤ src.length := by
  cases st with
  | idle =>
    simp only [chunkStep] at h
    split_ifs at h with h1 h2 h3 h4 h5 <;> simp_all
    obtain ⟨_, _, h, _⟩ := h; subst h; simp; omega
  | chunk seq len =>
    simp only [chunkStep] at h
    split_ifs at h with h1 h2 <;> simp_all
    obtain ⟨_, _, h, _⟩ := h; subst h; simp; omega

private theorem plainDecodeAux_fuel_le (f g : Nat) (seq : U8) (st : ChunkState) (src dst : List U8)
    (max : Nat) (comp : Option U8) (hf : src.length + 1 ≤ f) (hg : src.length + 1 ≤ g) :
    plainDecodeAux f seq st src dst max comp = plainDecodeAux g seq st src dst max comp := by
  induction f generalizing g seq st src dst with
  | zero => omega
  | succ f ih =>
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    simp only [plainDecodeAux]
    rcases hc : chunkStep st src dst max with ⟨r, st', src', dst'⟩
    rcases r with _ | e
    · rename_i o
      rcases o with _ | info
      · rfl
      · have := chunkStep_middle_len st src dst max
        cases info
        all_goals simp only
        all_goals split_ifs <;> first | rfl | exact ih _ _ _ _ _ (by have := this _ _ _ _ hc; omega) (by have := this _ _ _ _ hc; omega)
    · rfl

/-- The fuel of `plainDecode` is enough: more fuel gives the same result. -/
theorem plainDecodeAux_fuel (f : Nat) (seq : U8) (st : ChunkState) (src dst : List U8) (max : Nat) (comp : Option U8)
    (hf : src.length + 1 ≤ f) :
    plainDecodeAux f seq st src dst max comp = plainDecode seq st src dst max comp :=
  plainDecodeAux_fuel_le _ _ _ _ _ _ _ _ hf (le_refl _)

private theorem plainDecodeAux_valid (f : Nat) (seq : U8) (st : ChunkState) (hv : st.Valid) (src dst : List U8) (max : Nat) (comp : Option U8) :
    (plainDecodeAux f seq st src dst max comp).2.2.1.Valid := by
  induction f generalizing seq st src dst with
  | zero => simpa [plainDecodeAux] using hv
  | succ f ih =>
    have hs := chunkStep_valid st hv src dst max
    simp only [plainDecodeAux]
    rcases hc : chunkStep st src dst max with ⟨r, st', src', dst'⟩
    rw [hc] at hs
    rcases r with _ | e
    · rename_i o
      rcases o with _ | info
      · exact hs
      · cases info
        all_goals
          simp only
          split_ifs <;> first | exact hs | exact ih _ _ hs _ _
    · exact hs

/-- The packet reader keeps the state valid. -/
theorem plainDecode_valid (seq : U8) (st : ChunkState) (hv : st.Valid) (src dst : List U8) (max : Nat) (comp : Option U8) :
    (plainDecode seq st src dst max comp).2.2.1.Valid :=
  plainDecodeAux_valid _ _ _ hv _ _ _ _

/-! ## Helpers for the codec lemmas -/

private theorem byte_congr (a b : Nat) (h : a % 256 = b % 256) : byte a = byte b := by
  simp only [byte]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

private theorem byte_byte_add (n k : Nat) : byte ((byte n).val + k) = byte (n + k) :=
  byte_congr _ _ (by rw [PBUtil.byte_val]; omega)

private theorem byte_val_self (u : U8) : byte u.val = u := by
  apply UScalar.eq_of_val_eq; rw [PBUtil.byte_val]; have := u.hBounds; simp at this ⊢

private theorem drop4 (h : List U8) (hh : h.length = 3) (b : U8) (q : List U8) :
    (h ++ b :: q).drop 4 = q := by
  rw [show 4 = h.length + 1 by omega, List.drop_append]; simp

private theorem hdr_facts (L : Nat) (hL : L < 2 ^ 24) (b : U8) (q : List U8) :
    (leBytes 3 L ++ b :: q).length = 4 + q.length ∧
    leNat ((leBytes 3 L ++ b :: q).take 3) = L ∧
    (leBytes 3 L ++ b :: q).getD 3 (byte 0) = b ∧
    (leBytes 3 L ++ b :: q).drop 4 = q := by
  have hl := PBUtil.length_leBytes 3 L
  refine ⟨by simp [hl]; omega, ?_, ?_, drop4 _ hl _ _⟩
  · rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega), PBUtil.leNat_leBytes]
    exact Nat.mod_eq_of_lt (by simpa using hL)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp [hl]

private theorem chunkStep_chunk_hdr (s : U8) (L : Nat) (h : List U8) (hh : h.length = 3) (b : U8)
    (q dst : List U8) (max : Nat) :
    chunkStep (.chunk s L) (h ++ b :: q) dst max =
      if L ≤ q.length then
        (.Ok (some (if (dst.length + L) % maxPayloadLen = 0 then .Middle s else .Last s)), .idle,
          q.drop L, dst ++ q.take L)
      else (.Ok none, .chunk s L, h ++ b :: q, dst) := by
  have hd := drop4 h hh b q
  have hlen : (h ++ b :: q).length = 4 + q.length := by simp [hh]; omega
  simp only [chunkStep, hd, hlen]
  by_cases hq : L ≤ q.length
  · have h4 : 4 + L ≤ 4 + q.length := by omega
    have hdd : (h ++ b :: q).drop (4 + L) = q.drop L := by rw [← List.drop_drop, hd]
    simp [h4, hq, hdd]
  · have h4 : ¬ 4 + L ≤ 4 + q.length := by omega
    simp [h4, hq]

private theorem chunkStep_idle_hdr (L n : Nat) (hL : L < 2 ^ 24) (q dst : List U8) (max : Nat) :
    chunkStep .idle (leBytes 3 L ++ byte n :: q) dst max =
      if L = 0 then (.Ok (some (.Last (byte n))), .idle, q, dst)
      else if max < dst.length + L then (.Err .PacketTooLarge, .idle, leBytes 3 L ++ byte n :: q, dst)
      else chunkStep (.chunk (byte n) L) (leBytes 3 L ++ byte n :: q) dst max := by
  obtain ⟨h1, h2, h3, h4⟩ := hdr_facts L hL (byte n) q
  have h5 : ¬ (4 + q.length < 4) := by omega
  simp only [chunkStep, h1, h2, h3, h4, h5, ↓reduceIte]

private theorem frame_long (n : Nat) (p : List U8) (h : ¬ p.length < maxPayloadLen) :
    frame n p = leBytes 3 maxPayloadLen ++ byte n ::
      (p.take maxPayloadLen ++ frame (n + 1) (p.drop maxPayloadLen)) := by
  rw [frame]; simp [h]

private theorem frame_ne_nil (n : Nat) (p : List U8) : frame n p ≠ [] := by
  intro h; have := frame_length n p; rw [h] at this; simp [frameCount] at this

private theorem frameCount_long (L : Nat) (h : ¬ L < maxPayloadLen) :
    frameCount L = frameCount (L - maxPayloadLen) + 1 := by
  have hM : maxPayloadLen = 16777215 := rfl
  simp only [frameCount]; rw [hM] at h ⊢; omega

private theorem pd_frame_aux (L : Nat) : ∀ (p : List U8), p.length = L → ∀ (n : Nat) (tail dst : List U8)
    (max : Nat) (comp : Option U8), dst.length % maxPayloadLen = 0 → dst.length + p.length ≤ max →
    plainDecode (byte n) .idle (frame n p ++ tail) dst max comp =
      (.Ok true, byte (n + frameCount p.length), .idle, tail, dst ++ p) := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro p hp n tail dst max comp hd hm
  have hM : maxPayloadLen = 16777215 := rfl
  unfold plainDecode
  simp only [plainDecodeAux]
  by_cases hs : p.length < maxPayloadLen
  · rw [frame_short _ _ hs]
    simp only [List.append_assoc, List.cons_append]
    rw [chunkStep_idle_hdr _ _ (by rw [hM] at hs; omega)]
    have hfc : frameCount p.length = 1 := by
      simp only [frameCount]; rw [hM] at hs ⊢; simp [Nat.div_eq_of_lt hs]
    by_cases h0 : p.length = 0
    · have : p = [] := List.eq_nil_of_length_eq_zero h0
      subst this
      simp [chunkInfoSeq, byte_byte_add, frameCount]
    · have hmx : ¬ max < dst.length + p.length := by omega
      simp only [h0, hmx, ↓reduceIte]
      rw [chunkStep_chunk_hdr _ _ _ (PBUtil.length_leBytes 3 _)]
      have hle : p.length ≤ (p ++ tail).length := by simp
      have hmod : ¬ (dst.length + p.length) % maxPayloadLen = 0 := by rw [hM] at hs hd ⊢; omega
      simp [hmod, hfc, chunkInfoSeq, byte_byte_add]
  · rw [frame_long _ _ hs]
    simp only [List.append_assoc, List.cons_append]
    rw [chunkStep_idle_hdr _ _ (by rw [hM]; omega)]
    have h0 : ¬ maxPayloadLen = 0 := by rw [hM]; omega
    have hmx : ¬ max < dst.length + maxPayloadLen := by omega
    simp only [h0, hmx, ↓reduceIte]
    rw [chunkStep_chunk_hdr _ _ _ (PBUtil.length_leBytes 3 _)]
    have htk : (p.take maxPayloadLen).length = maxPayloadLen := by simp; omega
    have hle : maxPayloadLen ≤ (p.take maxPayloadLen ++ (frame (n + 1) (p.drop maxPayloadLen) ++ tail)).length := by
      simp only [List.length_append]; omega
    have hmod : (dst.length + maxPayloadLen) % maxPayloadLen = 0 := by rw [hM] at hd ⊢; omega
    have hdrop : (p.take maxPayloadLen ++ (frame (n + 1) (p.drop maxPayloadLen) ++ tail)).drop maxPayloadLen
        = frame (n + 1) (p.drop maxPayloadLen) ++ tail := by
      rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega)]; simp
    have htake : (p.take maxPayloadLen ++ (frame (n + 1) (p.drop maxPayloadLen) ++ tail)).take maxPayloadLen
        = p.take maxPayloadLen := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have hne : frame (n + 1) (p.drop maxPayloadLen) ++ tail ≠ [] := by simp [frame_ne_nil]
    simp only [hle, hmod, hdrop, htake, ↓reduceIte, chunkInfoSeq, ne_eq, not_true_eq_false, false_and, hne]
    rw [plainDecodeAux_fuel _ _ _ _ _ _ _ (by simp only [List.length_append, List.length_cons]; omega),
      byte_byte_add, ih (L - maxPayloadLen) (by omega) _ (by simp; omega)]
    · rw [frameCount_long _ hs, List.length_drop, List.append_assoc, List.take_append_drop,
        show n + 1 + frameCount (p.length - maxPayloadLen) = n + (frameCount (p.length - maxPayloadLen) + 1) by omega]
    · simp only [List.length_append, htk]; rw [hM] at hd ⊢; omega
    · simp only [List.length_append, htk, List.length_drop]; omega

/-- The crate's packet reader reads back the chunks of a payload (the reference version of the codec round trip). -/
theorem plainDecode_frame (seq : U8) (p tail : List U8) (max : Nat) (hmax : p.length ≤ max)
    (comp : Option U8) :
    plainDecode seq .idle (frame seq.val p ++ tail) [] max comp =
      (.Ok true, byte (seq.val + frameCount p.length), .idle, tail, p) := by
  have := pd_frame_aux p.length p rfl seq.val tail [] max comp (by simp) (by simpa using hmax)
  rwa [byte_val_self, List.nil_append] at this

private theorem take_hdr (h : List U8) (hh : h.length = 3) (b : U8) (q : List U8) (k : Nat) (hk : 4 ≤ k) :
    (h ++ b :: q).take k = h ++ b :: q.take (k - 4) := by
  rw [List.take_append, List.take_of_length_le (by omega), hh,
    show k - 3 = (k - 4) + 1 by omega, List.take_succ_cons]

private theorem drop_hdr (h : List U8) (hh : h.length = 3) (b : U8) (q : List U8) (k : Nat) (hk : 4 ≤ k) :
    (h ++ b :: q).drop k = q.drop (k - 4) := by
  rw [List.drop_append, List.drop_of_length_le (by omega), hh,
    show k - 3 = (k - 4) + 1 by omega, List.drop_succ_cons, List.nil_append]

private theorem plainDecode_congr_step (seq : U8) (st1 st2 : ChunkState) (src dst : List U8) (max : Nat)
    (comp : Option U8) (h : chunkStep st1 src dst max = chunkStep st2 src dst max) :
    plainDecode seq st1 src dst max comp = plainDecode seq st2 src dst max comp := by
  unfold plainDecode; simp only [plainDecodeAux, h]

/-- The pending case: a prefix that ends inside the first chunk's payload. -/
private theorem pd_pending (L n : Nat) (hL0 : 0 < L) (hL : L < 2 ^ 24) (rest tail dst : List U8)
    (max : Nat) (comp : Option U8) (hmx : dst.length + L ≤ max) (k : Nat) (hk : 4 ≤ k)
    (hq : (rest.take (k - 4)).length < L) :
    plainDecode (byte n) .idle ((leBytes 3 L ++ byte n :: rest).take k) dst max comp =
      (.Ok false, byte n, .chunk (byte n) L, (leBytes 3 L ++ byte n :: rest).take k, dst) ∧
    plainDecode (byte n) (.chunk (byte n) L)
        ((leBytes 3 L ++ byte n :: rest).take k ++ (leBytes 3 L ++ byte n :: rest).drop k ++ tail) dst max comp =
      plainDecode (byte n) .idle ((leBytes 3 L ++ byte n :: rest) ++ tail) dst max comp := by
  have hl := PBUtil.length_leBytes 3 L
  have h0 : ¬ L = 0 := by omega
  have h1 : ¬ max < dst.length + L := by omega
  constructor
  · rw [take_hdr _ hl _ _ _ hk]
    unfold plainDecode
    simp only [plainDecodeAux]
    rw [chunkStep_idle_hdr _ _ hL]
    simp only [h0, h1, ↓reduceIte]
    rw [chunkStep_chunk_hdr _ _ _ hl]
    have : ¬ L ≤ (rest.take (k - 4)).length := by omega
    simp only [this, ↓reduceIte]
  · rw [List.take_append_drop]
    apply plainDecode_congr_step
    simp only [List.append_assoc, List.cons_append]
    rw [chunkStep_idle_hdr _ _ hL]
    simp only [h0, h1, ↓reduceIte]

private theorem pd_resume_aux (L : Nat) : ∀ (p : List U8), p.length = L → ∀ (n k : Nat) (tail dst : List U8)
    (max : Nat) (comp : Option U8), k < (frame n p).length → dst.length % maxPayloadLen = 0 →
    dst.length + p.length ≤ max →
    ∀ (r : core.result.Result Bool proto.codec.error.PacketCodecError) (seq1 : U8) (st1 : ChunkState)
      (src1 dst1 : List U8),
    plainDecode (byte n) .idle ((frame n p).take k) dst max comp = (r, seq1, st1, src1, dst1) →
    r = .Ok false ∧
    plainDecode seq1 st1 (src1 ++ (frame n p).drop k ++ tail) dst1 max comp =
      (.Ok true, byte (n + frameCount p.length), .idle, tail, dst ++ p) := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro p hpL n k tail dst max comp hk hd hm r seq1 st1 src1 dst1 h
  have hM : maxPayloadLen = 16777215 := rfl
  have full := pd_frame_aux _ p rfl n tail dst max comp hd hm
  by_cases hk4 : k < 4
  · have hlen : ((frame n p).take k).length = k := by simp; omega
    have e : plainDecode (byte n) .idle ((frame n p).take k) dst max comp =
        (.Ok false, byte n, .idle, (frame n p).take k, dst) := by
      unfold plainDecode; simp only [plainDecodeAux, chunkStep, hlen, hk4, ↓reduceIte]
    rw [e] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, ?_⟩; rw [List.take_append_drop]; exact full
  by_cases hs : p.length < maxPayloadLen
  · rw [frame_short _ _ hs] at h hk full ⊢
    have hl := PBUtil.length_leBytes 3 p.length
    simp only [List.length_append, List.length_cons, hl] at hk
    obtain ⟨h1, h2⟩ := pd_pending p.length n (by omega) (by rw [hM] at hs; omega) p tail dst max comp
      (by omega) k (by omega) (by simp; omega)
    rw [h1] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, by rw [h2]; exact full⟩
  · rw [frame_long _ _ hs] at h hk full ⊢
    have hl := PBUtil.length_leBytes 3 maxPayloadLen
    have htk : (p.take maxPayloadLen).length = maxPayloadLen := by simp; omega
    simp only [List.length_append, List.length_cons, hl, htk] at hk
    by_cases hp : k - 4 < maxPayloadLen
    · obtain ⟨h1, h2⟩ := pd_pending maxPayloadLen n (by rw [hM]; omega) (by rw [hM]; omega)
        (p.take maxPayloadLen ++ frame (n + 1) (p.drop maxPayloadLen)) tail dst max comp
        (by omega) k (by omega) (by simp only [List.length_take, List.length_append, htk]; omega)
      rw [h1] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, by rw [h2]; exact full⟩
    · -- the whole first chunk is in the prefix
      have h0 : ¬ maxPayloadLen = 0 := by rw [hM]; omega
      have hmx : ¬ max < dst.length + maxPayloadLen := by omega
      have hrt : (p.take maxPayloadLen ++ frame (n + 1) (p.drop maxPayloadLen)).take (k - 4) =
          p.take maxPayloadLen ++ (frame (n + 1) (p.drop maxPayloadLen)).take (k - 4 - maxPayloadLen) := by
        rw [List.take_append, List.take_of_length_le (by omega), htk]
      have hrd : (p.take maxPayloadLen ++ frame (n + 1) (p.drop maxPayloadLen)).drop (k - 4) =
          (frame (n + 1) (p.drop maxPayloadLen)).drop (k - 4 - maxPayloadLen) := by
        rw [List.drop_append, List.drop_of_length_le (by omega), htk, List.nil_append]
      rw [drop_hdr _ hl _ _ _ (by omega), hrd]
      have hfl : ((leBytes 3 maxPayloadLen ++ byte n :: (p.take maxPayloadLen ++
          frame (n + 1) (p.drop maxPayloadLen))).take k).length = k := by
        simp only [List.length_take, List.length_append, List.length_cons, hl, htk]; omega
      unfold plainDecode at h
      rw [hfl] at h
      simp only [plainDecodeAux] at h
      rw [take_hdr _ hl _ _ _ (by omega), chunkStep_idle_hdr _ _ (by rw [hM]; omega)] at h
      simp only [h0, hmx, ↓reduceIte] at h
      rw [chunkStep_chunk_hdr _ _ _ hl, hrt] at h
      have hle : maxPayloadLen ≤ (p.take maxPayloadLen ++
          (frame (n + 1) (p.drop maxPayloadLen)).take (k - 4 - maxPayloadLen)).length := by
        simp only [List.length_append, htk]; omega
      have hmod : (dst.length + maxPayloadLen) % maxPayloadLen = 0 := by rw [hM] at hd ⊢; omega
      have hdr : (p.take maxPayloadLen ++
          (frame (n + 1) (p.drop maxPayloadLen)).take (k - 4 - maxPayloadLen)).drop maxPayloadLen =
          (frame (n + 1) (p.drop maxPayloadLen)).take (k - 4 - maxPayloadLen) := by
        rw [List.drop_append, List.drop_of_length_le (by omega), htk, Nat.sub_self, List.drop_zero,
          List.nil_append]
      have htt : (p.take maxPayloadLen ++
          (frame (n + 1) (p.drop maxPayloadLen)).take (k - 4 - maxPayloadLen)).take maxPayloadLen =
          p.take maxPayloadLen := by
        rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
      simp only [hle, hmod, hdr, htt, ↓reduceIte, chunkInfoSeq, ne_eq, not_true_eq_false, false_and,
        byte_byte_add] at h
      have hfull' := pd_frame_aux _ (p.drop maxPayloadLen) rfl (n + 1) tail (dst ++ p.take maxPayloadLen)
        max comp (by simp only [List.length_append, htk]; rw [hM] at hd ⊢; omega)
        (by simp only [List.length_append, htk, List.length_drop]; omega)
      have hfin : byte (n + 1 + frameCount (p.drop maxPayloadLen).length) = byte (n + frameCount p.length) := by
        rw [frameCount_long _ hs, List.length_drop,
          show n + 1 + frameCount (p.length - maxPayloadLen) = n + (frameCount (p.length - maxPayloadLen) + 1) by omega]
      have hpp : dst ++ p.take maxPayloadLen ++ p.drop maxPayloadLen = dst ++ p := by
        rw [List.append_assoc, List.take_append_drop]
      by_cases he : k - 4 - maxPayloadLen = 0
      · rw [he] at h ⊢
        simp only [List.take_zero, ↓reduceIte, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        rw [List.drop_zero, List.nil_append, hfull', hfin, hpp]
      · have hne : (frame (n + 1) (p.drop maxPayloadLen)).take (k - 4 - maxPayloadLen) ≠ [] := by
          simp [frame_ne_nil]; omega
        simp only [hne, ↓reduceIte] at h
        have hj : ((frame (n + 1) (p.drop maxPayloadLen)).take (k - 4 - maxPayloadLen)).length + 1 ≤ k := by
          have := List.length_take_le (k - 4 - maxPayloadLen) (frame (n + 1) (p.drop maxPayloadLen))
          clear hM hd hmod h full hfull' hfin
          omega
        rw [plainDecodeAux_fuel _ _ _ _ _ _ _ hj] at h
        obtain ⟨hr, h2⟩ := ih (L - maxPayloadLen) (by omega) (p.drop maxPayloadLen) (by simp; omega) (n + 1)
          (k - 4 - maxPayloadLen) tail (dst ++ p.take maxPayloadLen) max comp (by omega)
          (by simp only [List.length_append, htk]; rw [hM] at hd ⊢; omega)
          (by simp only [List.length_append, htk, List.length_drop]; omega) r seq1 st1 src1 dst1 h
        exact ⟨hr, by rw [h2, hfin, hpp]⟩

/-- Resumption: on a strict prefix of the chunks the reader needs more input; continuing from the state it returns, on what it left followed by the rest of the chunks, reads the whole packet. -/
theorem plainDecode_resume (seq : U8) (p tail : List U8) (k : Nat) (hk : k < (frame seq.val p).length) (max : Nat)
    (hmax : p.length ≤ max) (comp : Option U8)
    (r : core.result.Result Bool proto.codec.error.PacketCodecError) (seq1 : U8) (st1 : ChunkState)
    (src1 dst1 : List U8)
    (h1 : plainDecode seq .idle ((frame seq.val p).take k) [] max comp = (r, seq1, st1, src1, dst1)) :
    r = .Ok false ∧
    plainDecode seq1 st1 (src1 ++ (frame seq.val p).drop k ++ tail) dst1 max comp =
      (.Ok true, byte (seq.val + frameCount p.length), .idle, tail, p) := by
  have := pd_resume_aux p.length p rfl seq.val k tail [] max comp hk (by simp) (by simpa using hmax)
    r seq1 st1 src1 dst1 (by rw [byte_val_self]; exact h1)
  simpa using this

private theorem chunkStep_frame_first (n : Nat) (p tail dst : List U8) (max : Nat)
    (hm : dst.length + p.length ≤ max) :
    ∃ info st' src' dst', chunkStep .idle (frame n p ++ tail) dst max = (.Ok (some info), st', src', dst') ∧
      chunkInfoSeq info = byte n := by
  have hM : maxPayloadLen = 16777215 := rfl
  by_cases hs : p.length < maxPayloadLen
  · rw [frame_short _ _ hs]
    simp only [List.append_assoc, List.cons_append]
    rw [chunkStep_idle_hdr _ _ (by rw [hM] at hs; omega)]
    by_cases h0 : p.length = 0
    · simp only [h0, ↓reduceIte]; exact ⟨_, _, _, _, rfl, rfl⟩
    · have hmx : ¬ max < dst.length + p.length := by omega
      simp only [h0, hmx, ↓reduceIte]
      rw [chunkStep_chunk_hdr _ _ _ (PBUtil.length_leBytes 3 _)]
      have hle : p.length ≤ (p ++ tail).length := by simp
      simp only [hle, ↓reduceIte]
      split_ifs <;> exact ⟨_, _, _, _, rfl, rfl⟩
  · rw [frame_long _ _ hs]
    simp only [List.append_assoc, List.cons_append]
    rw [chunkStep_idle_hdr _ _ (by rw [hM]; omega)]
    have h0 : ¬ maxPayloadLen = 0 := by rw [hM]; omega
    have hmx : ¬ max < dst.length + maxPayloadLen := by omega
    simp only [h0, hmx, ↓reduceIte]
    rw [chunkStep_chunk_hdr _ _ _ (PBUtil.length_leBytes 3 _)]
    have htk : (p.take maxPayloadLen).length = maxPayloadLen := by simp; omega
    have hle : maxPayloadLen ≤ (p.take maxPayloadLen ++ (frame (n + 1) (p.drop maxPayloadLen) ++ tail)).length := by
      simp only [List.length_append]; omega
    simp only [hle, ↓reduceIte]
    split_ifs <;> exact ⟨_, _, _, _, rfl, rfl⟩

/-- Chunks with an unexpected sequence id (outside compressed mode) are out of sync; the expected id is kept. -/
theorem plainDecode_outOfSync (seq s : U8) (hs : s ≠ seq) (p tail : List U8) (max : Nat) (hmax : p.length ≤ max) :
    (plainDecode seq .idle (frame s.val p ++ tail) [] max none).1 = .Err .PacketsOutOfSync ∧
    (plainDecode seq .idle (frame s.val p ++ tail) [] max none).2.1 = seq := by
  obtain ⟨info, st', src', dst', hc, hi⟩ := chunkStep_frame_first s.val p tail [] max (by simpa using hmax)
  rw [byte_val_self] at hi
  have hne : seq ≠ chunkInfoSeq info ∧ none ≠ some (chunkInfoSeq info) := ⟨by rw [hi]; exact hs.symm, by simp⟩
  unfold plainDecode
  obtain ⟨hne1, hne2⟩ := hne
  simp only [plainDecodeAux, hc, ne_eq, hne1, hne2, not_false_eq_true, and_self, ↓reduceIte]

end Defs
