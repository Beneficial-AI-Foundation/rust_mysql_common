import Defs
import Proofs.Util.ParseBuf
import Proofs.Util.SharedBasic
import Proofs.Util.IntAndMisc
import Proofs.Util.ParamsAsSql

/-! Helper lemmas for the replication-command proofs (`Proofs/Packets/{ComRegisterSlave,
ComTableDump,ComBinlogDump,ComBinlogDumpGtid,GnoInterval,Sid,Tag,SemiSyncAckPacket}.lean`,
`Proofs/Packets/BinlogRequest/*.lean`, and the GTID/SID lemmas of
`Proofs/Defs/LemmasStmtSession.lean`): reading back the layouts of `Defs/BinlogCmd.lean`. -/

set_option autoImplicit false

open Aeneas Aeneas.Std mysql_common Defs mysql_common.PBUtil mysql_common.Shared

namespace mysql_common.Replication

/-! ## Little-endian numbers -/

theorem leNat_append (a b : List U8) : leNat (a ++ b) = leNat a + 2 ^ (8 * a.length) * leNat b := by
  induction a with
  | nil => simp [leNat]
  | cons x a ih =>
    simp only [List.cons_append, leNat, ih, List.length_cons]
    rw [show 8 * (a.length + 1) = 8 + 8 * a.length by ring, pow_add]
    ring

theorem take_leBytes_append (k n : Nat) (t : List U8) : (leBytes k n ++ t).take k = leBytes k n := by
  rw [List.take_append_of_le_length (by rw [length_leBytes]), List.take_of_length_le (by rw [length_leBytes])]

theorem drop_leBytes_append (k n : Nat) (t : List U8) : (leBytes k n ++ t).drop k = t := by
  rw [List.drop_append_of_le_length (by rw [length_leBytes])]; simp [length_leBytes]

theorem leNat_take_leBytes_append (k n : Nat) (t : List U8) (hn : n < 2 ^ (8 * k)) :
    leNat ((leBytes k n ++ t).take k) = n := by
  rw [take_leBytes_append, leNat_leBytes, Nat.mod_eq_of_lt hn]

theorem usize_max_ge : 2 ^ 32 - 1 ≤ Usize.max := by
  have h1 := Usize.max_def; rw [Usize.numBits_def] at h1
  have := IntAndMisc.usize_pow_ge
  omega

/-! ## Length-prefixed strings -/

theorem checkedLenPrefixed_leBytes (k : Nat) (s t : List U8) (hs : s.length < 2 ^ (8 * k)) :
    checkedLenPrefixed k (leBytes k s.length ++ (s ++ t)) = (some s, t) := by
  simp [checkedLenPrefixed, readLE_leBytes k s.length _ hs]

/-! ## `COM_REGISTER_SLAVE` -/

theorem regSlaveRead_regSlaveEnc (r : RegSlave)
    (hr : r.serverId < 2 ^ 32 ∧ r.hostname.length ≤ 255 ∧ r.user.length ≤ 255 ∧
      r.password.length ≤ 255 ∧ r.port < 2 ^ 16 ∧ r.rank < 2 ^ 32 ∧ r.masterId < 2 ^ 32)
    (tail : List U8) :
    regSlaveRead (regSlaveEnc r ++ tail) = (some r, tail) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
  obtain ⟨sid, hn, us, pw, port, rank, mid⟩ := r
  simp only at h1 h2 h3 h4 h5 h6 h7
  have e : regSlaveEnc ⟨sid, hn, us, pw, port, rank, mid⟩ ++ tail =
      byte 0x15 :: (leBytes 4 sid ++ (u8LenStr hn ++ (u8LenStr us ++ (u8LenStr pw ++
        (leBytes 2 port ++ leBytes 4 rank ++ leBytes 4 mid ++ tail))))) := by
    simp [regSlaveEnc, List.take_of_length_le h2, List.take_of_length_le h3,
      List.take_of_length_le h4, List.append_assoc]
  rw [e]
  have hl : ¬ (byte 0x15 :: (leBytes 4 sid ++ (u8LenStr hn ++ (u8LenStr us ++ (u8LenStr pw ++
        (leBytes 2 port ++ leBytes 4 rank ++ leBytes 4 mid ++ tail)))))).length < 5 := by
    simp [length_leBytes]
  have hb : ¬ (byte 0x15).val ≠ 0x15 := by simp [byte_val]
  unfold regSlaveRead
  simp only [hl, ↓reduceIte, List.getD_cons_zero, hb, List.drop_succ_cons, List.drop_zero]
  have hd : (leBytes 4 sid ++ (u8LenStr hn ++ (u8LenStr us ++ (u8LenStr pw ++
        (leBytes 2 port ++ leBytes 4 rank ++ leBytes 4 mid ++ tail))))).drop 4 =
      u8LenStr hn ++ (u8LenStr us ++ (u8LenStr pw ++
        (leBytes 2 port ++ leBytes 4 rank ++ leBytes 4 mid ++ tail))) := drop_leBytes_append _ _ _
  simp only [hd, leNat_take_leBytes_append 4 sid _ h1]
  rw [checkedLenPrefixed_u8LenStr _ _ h2]
  simp only
  rw [checkedLenPrefixed_u8LenStr _ _ h3]
  simp only
  rw [checkedLenPrefixed_u8LenStr _ _ h4]
  simp only
  have h10 : ¬ (leBytes 2 port ++ (leBytes 4 rank ++ (leBytes 4 mid ++ tail))).length < 10 := by
    simp [length_leBytes]; omega
  simp only [List.append_assoc, h10, ↓reduceIte, leNat_take_leBytes_append 2 port _ h5]
  have d2 : (leBytes 2 port ++ (leBytes 4 rank ++ (leBytes 4 mid ++ tail))).drop 2 =
      leBytes 4 rank ++ (leBytes 4 mid ++ tail) := drop_leBytes_append _ _ _
  have d6 : (leBytes 2 port ++ (leBytes 4 rank ++ (leBytes 4 mid ++ tail))).drop 6 =
      leBytes 4 mid ++ tail := by
    rw [show 6 = 2 + 4 from rfl, ← List.drop_drop, d2, drop_leBytes_append]
  have d10 : (leBytes 2 port ++ (leBytes 4 rank ++ (leBytes 4 mid ++ tail))).drop 10 = tail := by
    rw [show 10 = 6 + 4 from rfl, ← List.drop_drop, d6, drop_leBytes_append]
  rw [d2, d6, d10, leNat_take_leBytes_append 4 rank _ h6, leNat_take_leBytes_append 4 mid _ h7]

/-! ## GTID sets: intervals and SIDs -/

theorem length_le_flatMap {α β : Type} (f : α → List β) (l : List α) (a : α) (ha : a ∈ l) :
    (f a).length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp ha with rfl | h
    · omega
    · have := ih h; omega

theorem length_flatMap_gnoEnc (is : List (Nat × Nat)) : (is.flatMap gnoEnc).length = 16 * is.length := by
  induction is with
  | nil => simp
  | cons x is ih => simp [gnoEnc, length_leBytes, ih]; ring

theorem gnoChunks_flatMap (is : List (Nat × Nat)) (hb : ∀ i ∈ is, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64)
    (t : List U8) : gnoChunks is.length (is.flatMap gnoEnc ++ t) = is := by
  induction is with
  | nil => simp [gnoChunks]
  | cons x is ih =>
    obtain ⟨h1, h2⟩ := hb x (by simp)
    have e : (x :: is).flatMap gnoEnc ++ t = leBytes 8 x.1 ++ (leBytes 8 x.2 ++ (is.flatMap gnoEnc ++ t)) := by
      simp [gnoEnc]
    rw [List.length_cons, gnoChunks, e, leNat_take_leBytes_append 8 _ _ h1, drop_leBytes_append,
      leNat_take_leBytes_append 8 _ _ h2,
      show 16 = 8 + 8 from rfl, ← List.drop_drop, drop_leBytes_append, drop_leBytes_append,
      ih (fun i hi => hb i (by simp [hi]))]

/-- The intervals of a SID are read back (bounds in 64 bits, `16 * count ≤ usize::MAX`). -/
theorem intervalsRead_intervalsEnc (is : List (Nat × Nat)) (hb : ∀ i ∈ is, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64)
    (hn : 16 * is.length ≤ Usize.max) (t : List U8) :
    intervalsRead (intervalsEnc is ++ t) = .done (some is) t := by
  have hl : is.length < 2 ^ 64 := by have := usize_max_lt; omega
  have e : intervalsEnc is ++ t = leBytes 8 is.length ++ (is.flatMap gnoEnc ++ t) := by
    simp [intervalsEnc]
  have h8 : ¬ (leBytes 8 is.length ++ (is.flatMap gnoEnc ++ t)).length < 8 := by simp [length_leBytes]
  have hov : ¬ Usize.max < 16 * is.length := by omega
  have hr : ¬ (is.flatMap gnoEnc ++ t).length < 16 * is.length := by
    rw [List.length_append, length_flatMap_gnoEnc]; omega
  rw [e, intervalsRead]
  simp only [h8, ↓reduceIte, leNat_take_leBytes_append 8 _ _ (by simpa using hl), drop_leBytes_append,
    hov, hr, gnoChunks_flatMap is hb]
  rw [List.drop_append_of_le_length (by rw [length_flatMap_gnoEnc]), ← length_flatMap_gnoEnc,
    List.drop_length, List.nil_append]

/-- An untagged SID is read back, without its tag. -/
theorem sidRead_sidEnc (s : SidV) (hu : s.uuid.length = 16)
    (hb : ∀ i ∈ s.intervals, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64) (hn : 16 * s.intervals.length ≤ Usize.max)
    (t : List U8) :
    sidRead (sidEnc s ++ t) = .done (some { s with tag := none }) t := by
  have hl : ¬ (sidEnc s ++ t).length < 16 := by simp [sidEnc, hu]
  have hd : (sidEnc s ++ t).drop 16 = intervalsEnc s.intervals ++ t := by
    simp [sidEnc, hu]
  have ht : (sidEnc s ++ t).take 16 = s.uuid := by
    simp [sidEnc, hu]
  rw [sidRead]
  simp only [hl, ↓reduceIte, hd, intervalsRead_intervalsEnc _ hb hn, ht]

/-- Untagged SIDs (no tag) are read back, one after the other. -/
theorem sidsRead_sidEnc (ss : List SidV)
    (h : ∀ s ∈ ss, s.uuid.length = 16 ∧ s.tag = none ∧ (∀ i ∈ s.intervals, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64) ∧
      16 * s.intervals.length ≤ Usize.max)
    (t : List U8) :
    sidsRead false ss.length (ss.flatMap sidEnc ++ t) = .done (some ss) t := by
  induction ss with
  | nil => simp [sidsRead]
  | cons s ss ih =>
    obtain ⟨hu, htag, hb, hn⟩ := h s (by simp)
    have e : (s :: ss).flatMap sidEnc ++ t = sidEnc s ++ (ss.flatMap sidEnc ++ t) := by simp
    have hs : { s with tag := none } = s := by cases s; simp_all
    rw [List.length_cons, sidsRead, e]
    simp only [Bool.false_eq_true, ↓reduceIte, sidRead_sidEnc s hu hb hn, hs,
      ih (fun x hx => h x (by simp [hx]))]

theorem length_sidEnc (s : SidV) :
    (sidEnc s).length = s.uuid.length + 8 + 16 * s.intervals.length := by
  simp only [sidEnc, intervalsEnc, List.length_append, length_leBytes, length_flatMap_gnoEnc]; omega

theorem length_le_flatMap_sidEnc (ss : List SidV) : ss.length ≤ (ss.flatMap sidEnc).length := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := length_sidEnc s
    omega

/-- The untagged SID block is the `n_sids` word then the SIDs. -/
theorem sidBlock_untagged (ss : List SidV) (h : gtidTagged ss = false) :
    sidBlock ss = leBytes 8 ss.length ++ ss.flatMap sidEnc := by
  simp [sidBlock, h, nSidsHeader]

/-- `COM_BINLOG_DUMP_GTID` round trip (untagged format). -/
theorem gtidDumpRead_gtidDumpEnc (g : GtidDump) (hnotag : gtidTagged g.sids = false)
    (hf : g.flags &&& binlogDumpFlagsAll = g.flags) (hsid : g.serverId < 2 ^ 32)
    (hfn : g.filename.length < 2 ^ 32) (hpos : g.pos < 2 ^ 64)
    (hblk : (sidBlock g.sids).length < 2 ^ 32)
    (hs : ∀ s ∈ g.sids, s.uuid.length = 16 ∧ ∀ i ∈ s.intervals, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64)
    (tail : List U8) :
    gtidDumpRead (gtidDumpEnc g ++ tail) = .done (some g) tail := by
  obtain ⟨f, sid, fn, pos, ss⟩ := g
  simp only at hnotag hf hsid hfn hpos hblk hs
  have hf8 : f < 2 ^ 16 := by
    have := Nat.and_le_right (n := f) (m := binlogDumpFlagsAll)
    simp [binlogDumpFlagsAll] at this hf; omega
  have hB := sidBlock_untagged ss hnotag
  have hBl : (sidBlock ss).length = 8 + (ss.flatMap sidEnc).length := by
    rw [hB, List.length_append, length_leBytes]
  have hssl : ss.length < 2 ^ 32 := by have := length_le_flatMap_sidEnc ss; omega
  have hss : ∀ s ∈ ss, s.uuid.length = 16 ∧ s.tag = none ∧
      (∀ i ∈ s.intervals, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64) ∧ 16 * s.intervals.length ≤ Usize.max := by
    intro s hm
    obtain ⟨hu, hb⟩ := hs s hm
    have htag : s.tag = none := by
      simp only [gtidTagged, List.any_eq_false] at hnotag
      have := hnotag s hm
      cases h : s.tag <;> simp_all
    refine ⟨hu, htag, hb, ?_⟩
    have h1 := length_le_flatMap sidEnc ss s hm
    have h2 := length_sidEnc s
    have := usize_max_ge
    omega
  set B := sidBlock ss with hBdef
  set R := leBytes 8 pos ++ (leBytes 4 B.length ++ (B ++ tail)) with hR
  have e : gtidDumpEnc ⟨f, sid, fn, pos, ss⟩ ++ tail =
      byte 0x1E :: (leBytes 2 f ++ (leBytes 4 sid ++ (leBytes 4 fn.length ++ (fn ++ R)))) := by
    have h1 : min fn.length 4294967295 = fn.length := by omega
    have h2 : fn.take 4294967295 = fn := List.take_of_length_le (by omega)
    simp [gtidDumpEnc, h1, h2, hR, hBdef]
  rw [e]
  unfold gtidDumpRead
  have hl : ¬ (byte 0x1E :: (leBytes 2 f ++ (leBytes 4 sid ++ (leBytes 4 fn.length ++ (fn ++ R))))).length < 7 := by
    simp [length_leBytes]; omega
  have ht : (byte 0x1E :: (leBytes 2 f ++ (leBytes 4 sid ++ (leBytes 4 fn.length ++ (fn ++ R))))).take 7 =
      byte 0x1E :: (leBytes 2 f ++ leBytes 4 sid) := by
    rw [List.take_succ_cons, ← List.append_assoc, List.take_append_of_le_length (by simp [length_leBytes]),
      List.take_of_length_le (by simp [length_leBytes])]
  have hsid' : leNat (((byte 0x1E :: (leBytes 2 f ++ leBytes 4 sid)).drop 3).take 4) = sid := by
    rw [show 3 = 2 + 1 from rfl, List.drop_succ_cons, drop_leBytes_append, ← List.append_nil (leBytes 4 sid),
      leNat_take_leBytes_append 4 sid _ hsid]
  have hf' : leNat (((byte 0x1E :: (leBytes 2 f ++ leBytes 4 sid)).drop 1).take 2) = f := by
    simp only [List.drop_succ_cons, List.drop_zero, leNat_take_leBytes_append 2 f _ hf8]
  have hd : (byte 0x1E :: (leBytes 2 f ++ (leBytes 4 sid ++ (leBytes 4 fn.length ++ (fn ++ R))))).drop 7 =
      leBytes 4 fn.length ++ (fn ++ R) := by
    rw [show 7 = 6 + 1 from rfl, List.drop_succ_cons, show 6 = 2 + 4 from rfl, ← List.drop_drop,
      drop_leBytes_append, drop_leBytes_append]
  have hb : ¬ ((byte 0x1E).val ≠ 0x1E ∨ f &&& binlogDumpFlagsAll ≠ f) := by simp [byte_val, hf]
  simp only [hl, ↓reduceIte, ht, hsid', hf', hd, List.getD_cons_zero, hb]
  rw [checkedLenPrefixed_leBytes 4 fn R (by simpa using hfn)]
  simp only [hR, readLE_leBytes 8 pos _ (by simpa using hpos), readLE_leBytes 4 B.length _ (by simpa using hblk)]
  have hle : ¬ (B ++ tail).length < B.length := by simp
  simp only [hle, ↓reduceIte, List.take_left', List.drop_left']
  rw [hB, ← List.append_nil (ss.flatMap sidEnc), readLE_leBytes 8 _ _ (by omega)]
  have h56 : ¬ (ss.length / 2 ^ 56 = 1) := by
    rw [Nat.div_eq_of_lt (by omega)]; omega
  simp only [h56, decide_false, ↓reduceIte, Nat.mod_eq_of_lt (show ss.length < 2 ^ 56 by omega),
    sidsRead_sidEnc ss hss]

/-- The tagged `n_sids` word: format byte `1`, the count in bits 8–55. -/
theorem nSidsHeader_tagged (n : Nat) (hn : n < 2 ^ 48) :
    (nSidsHeader true n).length = 8 ∧ leNat (nSidsHeader true n) / 2 ^ 56 = 1 ∧
    (leNat (nSidsHeader true n) / 2 ^ 8) % 2 ^ 48 = n := by
  have hv : leNat (nSidsHeader true n) = 256 * n + 2 ^ 56 := by
    simp only [nSidsHeader, ↓reduceIte, List.cons_append, leNat, leNat_append, leNat_leBytes,
      length_leBytes, byte_val, Nat.mod_eq_of_lt hn]
    norm_num
    ring
  refine ⟨by simp [nSidsHeader, length_leBytes], ?_, ?_⟩
  · rw [hv]; omega
  · rw [hv]; omega

/-! ## The tagged format -/

/-- A valid tag has 1 to 32 bytes, all ASCII. -/
theorem tagBytesValid_spec {t : List U8} (h : tagBytesValid t = true) :
    0 < t.length ∧ t.length ≤ 32 ∧ ∀ b ∈ t, b.val < 128 := by
  cases t with
  | nil => simp [tagBytesValid] at h
  | cons c cs =>
    simp only [tagBytesValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨hl, hc⟩, hcs⟩ := h
    refine ⟨by simp, by simp; omega, ?_⟩
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · simp [tagFirstByte] at hc; omega
    · have := hcs b hb; simp [tagRestByte, tagFirstByte] at this; omega

/-- A valid tag is valid UTF-8 (it is ASCII). -/
theorem tagBytesValid_utf8 {t : List U8} (h : tagBytesValid t = true) :
    (Trusted.bytesOf t).IsValidUTF8 := by
  obtain ⟨s, hs⟩ := PASUtil.isUtf8_ascii t (tagBytesValid_spec h).2.2
  rw [← hs, CBTUtil.bytesOf_utf8]
  exact s.isValidUTF8

/-- A tagged SID whose tag (if any) is valid is read back. -/
theorem sidTaggedRead_sidTaggedEnc (s : SidV) (hu : s.uuid.length = 16)
    (ht : ∀ t, s.tag = some t → tagBytesValid t = true)
    (hb : ∀ i ∈ s.intervals, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64) (hn : 16 * s.intervals.length ≤ Usize.max)
    (t : List U8) :
    sidTaggedRead (sidTaggedEnc s ++ t) = .done (some s) t := by
  obtain ⟨uuid, tag, is⟩ := s
  simp only at hu ht hb hn ⊢
  have hl : ¬ (sidTaggedEnc ⟨uuid, tag, is⟩ ++ t).length < 16 := by simp [sidTaggedEnc, hu]
  have hd : (sidTaggedEnc ⟨uuid, tag, is⟩ ++ t).drop 16 =
      varlenUint (tag.getD []).length ++ (tag.getD [] ++ (intervalsEnc is ++ t)) := by
    simp [sidTaggedEnc, hu]
  have htk : (sidTaggedEnc ⟨uuid, tag, is⟩ ++ t).take 16 = uuid := by simp [sidTaggedEnc, hu]
  have hlen : (tag.getD []).length < 2 ^ 64 := by
    cases tag with
    | none => simp
    | some tg => have := (tagBytesValid_spec (ht tg rfl)).2.1; simp; omega
  rw [sidTaggedRead]
  simp only [hl, ↓reduceIte, hd, htk, IntAndMisc.varlenUintDecode_varlenUint' _ _ hlen]
  cases tag with
  | none => simp [intervalsRead_intervalsEnc _ hb hn]
  | some tg =>
    have hv := ht tg rfl
    have h0 := (tagBytesValid_spec hv).1
    simp [show tg.length ≠ 0 by omega, hv, tagBytesValid_utf8 hv, intervalsRead_intervalsEnc _ hb hn]

/-- Tagged SIDs whose tags (if any) are valid are read back, one after the other. -/
theorem sidsRead_sidTaggedEnc (ss : List SidV)
    (h : ∀ s ∈ ss, s.uuid.length = 16 ∧ (∀ t, s.tag = some t → tagBytesValid t = true) ∧
      (∀ i ∈ s.intervals, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64) ∧ 16 * s.intervals.length ≤ Usize.max)
    (t : List U8) :
    sidsRead true ss.length (ss.flatMap sidTaggedEnc ++ t) = .done (some ss) t := by
  induction ss with
  | nil => simp [sidsRead]
  | cons s ss ih =>
    obtain ⟨hu, htag, hb, hn⟩ := h s (by simp)
    have e : (s :: ss).flatMap sidTaggedEnc ++ t = sidTaggedEnc s ++ (ss.flatMap sidTaggedEnc ++ t) := by
      simp
    rw [List.length_cons, sidsRead, e]
    simp only [↓reduceIte, sidTaggedRead_sidTaggedEnc s hu htag hb hn,
      ih (fun x hx => h x (by simp [hx]))]

theorem length_sidTaggedEnc_ge (s : SidV) : 8 + 16 * s.intervals.length ≤ (sidTaggedEnc s).length := by
  simp only [sidTaggedEnc, intervalsEnc, List.length_append, length_leBytes, length_flatMap_gnoEnc]; omega

theorem length_le_flatMap_sidTaggedEnc (ss : List SidV) : ss.length ≤ (ss.flatMap sidTaggedEnc).length := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := length_sidTaggedEnc_ge s
    omega

/-- `COM_BINLOG_DUMP_GTID` round trip, with or without tags: every tag present is valid
    (`tagBytesValid`). -/
theorem gtidDumpRead_gtidDumpEnc_tagged (g : GtidDump)
    (hf : g.flags &&& binlogDumpFlagsAll = g.flags) (hsid : g.serverId < 2 ^ 32)
    (hfn : g.filename.length < 2 ^ 32) (hpos : g.pos < 2 ^ 64)
    (hblk : (sidBlock g.sids).length < 2 ^ 32)
    (hs : ∀ s ∈ g.sids, s.uuid.length = 16 ∧ (∀ t, s.tag = some t → tagBytesValid t = true) ∧
      ∀ i ∈ s.intervals, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64)
    (tail : List U8) :
    gtidDumpRead (gtidDumpEnc g ++ tail) = .done (some g) tail := by
  cases htg : gtidTagged g.sids with
  | false =>
    exact gtidDumpRead_gtidDumpEnc g htg hf hsid hfn hpos hblk
      (fun s hm => ⟨(hs s hm).1, (hs s hm).2.2⟩) tail
  | true =>
  obtain ⟨f, sid, fn, pos, ss⟩ := g
  simp only at htg hf hsid hfn hpos hblk hs
  have hf8 : f < 2 ^ 16 := by
    have := Nat.and_le_right (n := f) (m := binlogDumpFlagsAll)
    simp [binlogDumpFlagsAll] at this hf; omega
  have hB : sidBlock ss = nSidsHeader true ss.length ++ ss.flatMap sidTaggedEnc := by
    simp [sidBlock, htg]
  have hssl : ss.length < 2 ^ 32 := by
    have := length_le_flatMap_sidTaggedEnc ss
    rw [hB, List.length_append] at hblk; omega
  have hss : ∀ s ∈ ss, s.uuid.length = 16 ∧ (∀ t, s.tag = some t → tagBytesValid t = true) ∧
      (∀ i ∈ s.intervals, i.1 < 2 ^ 64 ∧ i.2 < 2 ^ 64) ∧ 16 * s.intervals.length ≤ Usize.max := by
    intro s hm
    obtain ⟨hu, ht, hb⟩ := hs s hm
    refine ⟨hu, ht, hb, ?_⟩
    have h1 := length_le_flatMap sidTaggedEnc ss s hm
    have h2 := length_sidTaggedEnc_ge s
    have := usize_max_ge
    rw [hB, List.length_append] at hblk
    omega
  set B := sidBlock ss with hBdef
  set R := leBytes 8 pos ++ (leBytes 4 B.length ++ (B ++ tail)) with hR
  have e : gtidDumpEnc ⟨f, sid, fn, pos, ss⟩ ++ tail =
      byte 0x1E :: (leBytes 2 f ++ (leBytes 4 sid ++ (leBytes 4 fn.length ++ (fn ++ R)))) := by
    have h1 : min fn.length 4294967295 = fn.length := by omega
    have h2 : fn.take 4294967295 = fn := List.take_of_length_le (by omega)
    simp [gtidDumpEnc, h1, h2, hR, hBdef]
  rw [e]
  unfold gtidDumpRead
  have hl : ¬ (byte 0x1E :: (leBytes 2 f ++ (leBytes 4 sid ++ (leBytes 4 fn.length ++ (fn ++ R))))).length < 7 := by
    simp [length_leBytes]; omega
  have ht : (byte 0x1E :: (leBytes 2 f ++ (leBytes 4 sid ++ (leBytes 4 fn.length ++ (fn ++ R))))).take 7 =
      byte 0x1E :: (leBytes 2 f ++ leBytes 4 sid) := by
    rw [List.take_succ_cons, ← List.append_assoc, List.take_append_of_le_length (by simp [length_leBytes]),
      List.take_of_length_le (by simp [length_leBytes])]
  have hsid' : leNat (((byte 0x1E :: (leBytes 2 f ++ leBytes 4 sid)).drop 3).take 4) = sid := by
    rw [show 3 = 2 + 1 from rfl, List.drop_succ_cons, drop_leBytes_append, ← List.append_nil (leBytes 4 sid),
      leNat_take_leBytes_append 4 sid _ hsid]
  have hf' : leNat (((byte 0x1E :: (leBytes 2 f ++ leBytes 4 sid)).drop 1).take 2) = f := by
    simp only [List.drop_succ_cons, List.drop_zero, leNat_take_leBytes_append 2 f _ hf8]
  have hd : (byte 0x1E :: (leBytes 2 f ++ (leBytes 4 sid ++ (leBytes 4 fn.length ++ (fn ++ R))))).drop 7 =
      leBytes 4 fn.length ++ (fn ++ R) := by
    rw [show 7 = 6 + 1 from rfl, List.drop_succ_cons, show 6 = 2 + 4 from rfl, ← List.drop_drop,
      drop_leBytes_append, drop_leBytes_append]
  have hb : ¬ ((byte 0x1E).val ≠ 0x1E ∨ f &&& binlogDumpFlagsAll ≠ f) := by simp [byte_val, hf]
  simp only [hl, ↓reduceIte, ht, hsid', hf', hd, List.getD_cons_zero, hb]
  rw [checkedLenPrefixed_leBytes 4 fn R (by simpa using hfn)]
  simp only [hR, readLE_leBytes 8 pos _ (by simpa using hpos), readLE_leBytes 4 B.length _ (by simpa using hblk)]
  have hle : ¬ (B ++ tail).length < B.length := by simp
  simp only [hle, ↓reduceIte, List.take_left', List.drop_left']
  obtain ⟨hHl, hH1, hH2⟩ := nSidsHeader_tagged ss.length (by omega)
  have hr8 : readLE 8 (nSidsHeader true ss.length ++ ss.flatMap sidTaggedEnc) =
      some (leNat (nSidsHeader true ss.length), ss.flatMap sidTaggedEnc) := by
    simp [readLE, hHl]
  have hsr := sidsRead_sidTaggedEnc ss hss []
  rw [List.append_nil] at hsr
  rw [hB, hr8]
  generalize leNat (nSidsHeader true ss.length) = v at hH1 hH2 ⊢
  split
  · rename_i heq; simp at heq
  · rename_i raw blk heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hdec : decide (v / 2 ^ 56 = 1) = true := decide_eq_true hH1
    have hif : (if v / 2 ^ 56 = 1 then v / 2 ^ 8 % 2 ^ 48 else v % 2 ^ 56) = ss.length := by
      split_ifs
      exact hH2
    rw [hdec, hif, hsr]

/-! ## What the readers leave is a suffix of their input -/

theorem readLE_rest {k : Nat} {bs : List U8} {n : Nat} {r : List U8} (h : readLE k bs = some (n, r)) :
    r = bs.drop k := by
  unfold readLE at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  · simp at h

theorem checkedLenPrefixed_suffix (k : Nat) (bs : List U8) : (checkedLenPrefixed k bs).2 <:+ bs := by
  unfold checkedLenPrefixed
  split
  · exact List.suffix_refl _
  · rename_i n rest h
    have := readLE_rest h
    subst this
    split
    · exact (List.drop_suffix _ _).trans (List.drop_suffix _ _)
    · exact List.drop_suffix _ _

theorem varlenUintDecode_suffix {bs : List U8} {n : Nat} {r : List U8}
    (h : varlenUintDecode bs = some (n, r)) : r <:+ bs := by
  cases bs with
  | nil => simp [varlenUintDecode] at h
  | cons b rest =>
    simp only [varlenUintDecode] at h
    split at h
    · rw [readLE_rest h]
      exact (List.drop_suffix _ _).trans (List.suffix_cons _ _)
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]; exact List.drop_suffix _ _
      · simp at h

theorem intervalsRead_suffix {bs : List U8} {o : Option (List (Nat × Nat))} {r : List U8}
    (h : intervalsRead bs = .done o r) : r <:+ bs := by
  unfold intervalsRead at h
  split at h
  · simp only [ReadOut.done.injEq] at h; rw [← h.2]
  · dsimp only at h
    split at h
    · simp at h
    · split at h
      · simp only [ReadOut.done.injEq] at h; rw [← h.2]; exact List.drop_suffix _ _
      · simp only [ReadOut.done.injEq] at h; rw [← h.2]
        exact (List.drop_suffix _ _).trans (List.drop_suffix _ _)

theorem sidTaggedRead_suffix {bs : List U8} {o : Option SidV} {r : List U8}
    (h : sidTaggedRead bs = .done o r) : r <:+ bs := by
  unfold sidTaggedRead at h
  split at h
  · simp only [ReadOut.done.injEq] at h; rw [← h.2]
  · dsimp only at h
    split at h
    · simp only [ReadOut.done.injEq] at h; rw [← h.2]; exact List.drop_suffix _ _
    · rename_i tl r' hv
      have h1 : r' <:+ bs := (varlenUintDecode_suffix hv).trans (List.drop_suffix _ _)
      have hints : ∀ (tag : Option (List U8)) (x : List U8), x <:+ bs →
          (match intervalsRead x with
            | .done (some is) rest => ReadOut.done (some (⟨bs.take 16, tag, is⟩ : SidV)) rest
            | .done none rest => .done none rest
            | .panic e => .panic e
            | .unknown => .unknown) = ReadOut.done o r → r <:+ bs := by
        intro tag x hx hm
        split at hm
        · rename_i is rest hi
          simp only [ReadOut.done.injEq] at hm; rw [← hm.2]; exact (intervalsRead_suffix hi).trans hx
        · rename_i rest hi
          simp only [ReadOut.done.injEq] at hm; rw [← hm.2]; exact (intervalsRead_suffix hi).trans hx
        · simp at hm
        · simp at hm
      split at h
      · exact hints none r' h1 h
      · split at h
        · simp only [ReadOut.done.injEq] at h; rw [← h.2]; exact h1
        · split at h
          · simp only [ReadOut.done.injEq] at h; rw [← h.2]; exact h1
          · split at h
            · exact hints _ _ ((List.drop_suffix _ _).trans h1) h
            · simp only [ReadOut.done.injEq] at h; rw [← h.2]; exact (List.drop_suffix _ _).trans h1

end mysql_common.Replication
