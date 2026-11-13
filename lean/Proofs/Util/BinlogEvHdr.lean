import Defs
import Proofs.Util.ParseBuf
import Proofs.Util.IntAndMisc
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf
import Proofs.Misc.Raw.Int.RawInt
import Proofs.Misc.Raw.Int.U8
import Proofs.Misc.Raw.Int.LeU16
import Proofs.Misc.Raw.Int.LeU32
import Proofs.Misc.Raw.Const.RawConst
import Proofs.Misc.Raw.Flags.RawFlags

/-! Helper lemmas for the binlog event header/footer, `Event`, FDE and query-event proofs
(`Proofs/Binlog/Events/{Mod,FormatDescriptionEvent,QueryEvent,ExecuteLoadQueryEvent,
BeginLoadQueryEvent}`, `Proofs/Defs/LemmasBinlogEvents.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.EvHdrUtil

/-! ## Bytes -/

theorem leBytes_leNat (l : List U8) : leBytes l.length (leNat l) = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.length_cons, leBytes, leNat]
    have hb : b.val < 256 := by scalar_tac
    congr 1
    · rw [show (b.val + 256 * leNat l) = b.val + 256 * leNat l from rfl]
      unfold byte; cases b; simp only [UScalar.val] at *
      congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    · rw [show (b.val + 256 * leNat l) / 256 = leNat l by omega]
      exact ih

theorem leBytes_leNat_take (k : Nat) (l : List U8) (h : k ≤ l.length) :
    leBytes k (leNat (l.take k)) = l.take k := by
  have := leBytes_leNat (l.take k)
  rwa [List.length_take, Nat.min_eq_left h] at this

theorem leNat_leBytes_lt (k n : Nat) (h : n < 2 ^ (8 * k)) : leNat (leBytes k n) = n := by
  rw [PBUtil.leNat_leBytes, Nat.mod_eq_of_lt h]

theorem leBytes_of_val (k : Nat) (n : Nat) (l : List U8) (h : n = leNat (l.take k)) (hl : k ≤ l.length) :
    leBytes k n = l.take k := by
  rw [h]; exact leBytes_leNat_take k l hl

theorem singleton_of_val (x : U8) (l : List U8) (h : x.val = leNat (l.take 1)) (hl : 1 ≤ l.length) :
    [x] = l.take 1 := by
  have e : [x] = leBytes 1 x.val := by
    simp only [leBytes]; congr 1; unfold byte; cases x; simp [UScalar.val]
  rw [e]; exact leBytes_of_val 1 _ l h hl

theorem take_append_of_drop {l r : List U8} (k : Nat) (h : r = l.drop k) : l = l.take k ++ r := by
  rw [h, List.take_append_drop]

theorem byte_val_self (x : U8) : byte x.val = x := by
  unfold byte; cases x; simp [UScalar.val]

theorem evHeaderEnc_len (h : binlog.events.BinlogEventHeader) : (evHeaderEnc h).length = 19 := by
  simp [evHeaderEnc]

theorem leBytes_inj (k x y : Nat) (hx : x < 2 ^ (8 * k)) (hy : y < 2 ^ (8 * k))
    (h : leBytes k x = leBytes k y) : x = y := by
  have := congrArg leNat h
  rwa [leNat_leBytes_lt k x hx, leNat_leBytes_lt k y hy] at this

theorem leBytes_inj32 (x y : U32) (h : leBytes 4 x.val = leBytes 4 y.val) : x = y :=
  UScalar.eq_of_val_eq (leBytes_inj 4 _ _ (by scalar_tac) (by scalar_tac) h)

theorem leBytes_inj16 (x y : U16) (h : leBytes 2 x.val = leBytes 2 y.val) : x = y :=
  UScalar.eq_of_val_eq (leBytes_inj 2 _ _ (by scalar_tac) (by scalar_tac) h)

theorem evHeaderEnc_inj (a b : binlog.events.BinlogEventHeader) (h : evHeaderEnc a = evHeaderEnc b) : a = b := by
  obtain ⟨⟨t1, p1⟩, ⟨e1, q1⟩, ⟨s1, r1⟩, ⟨z1, u1⟩, ⟨l1, v1⟩, ⟨f1, w1⟩⟩ := a
  obtain ⟨⟨t2, p2⟩, ⟨e2, q2⟩, ⟨s2, r2⟩, ⟨z2, u2⟩, ⟨l2, v2⟩, ⟨f2, w2⟩⟩ := b
  simp only [evHeaderEnc] at h
  obtain ⟨h, h6⟩ := List.append_inj h (by simp)
  obtain ⟨h, h5⟩ := List.append_inj h (by simp)
  obtain ⟨h, h4⟩ := List.append_inj h (by simp)
  obtain ⟨h, h3⟩ := List.append_inj h (by simp)
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  simp only [List.cons.injEq, and_true] at h2
  cases p1; cases p2; cases q1; cases q2; cases r1; cases r2; cases u1; cases u2; cases v1; cases v2; cases w1; cases w2
  rw [leBytes_inj32 _ _ h1, h2, leBytes_inj32 _ _ h3, leBytes_inj32 _ _ h4, leBytes_inj32 _ _ h5, leBytes_inj16 _ _ h6]

theorem sat_add_val {ty : UScalarTy} (x y : UScalar ty) :
    (UScalar.saturating_add x y).val = min (UScalar.max ty) (x.val + y.val) := by
  have h : min (UScalar.max ty) (x.val + y.val) < 2 ^ ty.numBits := by
    have h1 : UScalar.max ty = 2 ^ ty.numBits - 1 := by rw [UScalar.max]
    have h2 : 0 < 2 ^ ty.numBits := Nat.pow_pos (by norm_num)
    omega
  simp only [UScalar.saturating_add, UScalar.val, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

theorem sat_add_usize (x y : Usize) :
    (core.num.Usize.saturating_add x y).val = min Usize.max (x.val + y.val) := by
  have := sat_add_val x y
  rw [UScalar.max_USize_eq] at this
  exact this

/-! ## `parse_unchecked` of fixed-size integers, as `Ok` results -/

theorem pu_rawint {T P : Type} (inst : misc.raw.int.IntRepr T P) (buf : io.ParseBuf) (k : Nat) (g : P → Nat)
    (h : inst.deserialize buf ⦃ r rest => (okPart r).map g = some (leNat (buf.val.take k)) ∧ rest.val = buf.val.drop k ⦄) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple inst) buf ()
      ⦃ r rest => ∃ v, r = .Ok v ∧ g v.1 = leNat (buf.val.take k) ∧ rest.val = buf.val.drop k ⦄ := by
  have := _root_.mysql_common.rawint_parse_unchecked_spec inst buf
    (fun o rest => o.map g = some (leNat (buf.val.take k)) ∧ rest.val = buf.val.drop k) h
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  cases r with
  | Ok v => exact ⟨v, rfl, by simpa [okPart] using h1, h2⟩
  | Err e => simp [okPart] at h1

theorem pu_rawconst {T P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P) (buf : io.ParseBuf) (k : Nat) (g : P → Nat)
    (h : inst.deserialize buf ⦃ r rest => (okPart r).map g = some (leNat (buf.val.take k)) ∧ rest.val = buf.val.drop k ⦄) :
    io.ParseBuf.parse_unchecked (misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple U inst) buf ()
      ⦃ r rest => ∃ v, r = .Ok v ∧ g v.1 = leNat (buf.val.take k) ∧ rest.val = buf.val.drop k ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec U inst buf
    (fun o rest => o.map g = some (leNat (buf.val.take k)) ∧ rest.val = buf.val.drop k) h
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  cases r with
  | Ok v => exact ⟨v, rfl, by simpa [okPart] using h1, h2⟩
  | Err e => simp [okPart] at h1

theorem pu_rawflags {T U B : Type} (fl : bitflags.traits.Flags T B) (inst : misc.raw.int.IntRepr U B) (buf : io.ParseBuf) (k : Nat) (g : B → Nat)
    (h : inst.deserialize buf ⦃ r rest => (okPart r).map g = some (leNat (buf.val.take k)) ∧ rest.val = buf.val.drop k ⦄) :
    io.ParseBuf.parse_unchecked (misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple fl inst) buf ()
      ⦃ r rest => ∃ v, r = .Ok v ∧ g v.1 = leNat (buf.val.take k) ∧ rest.val = buf.val.drop k ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have := misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple.deserialize_spec fl inst buf
    (fun o rest => o.map g = some (leNat (buf.val.take k)) ∧ rest.val = buf.val.drop k) h
  apply WP.spec_mono this
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  cases r with
  | Ok v => exact ⟨v, rfl, by simpa [okPart] using h1, h2⟩
  | Err e => simp [okPart] at h1

@[step] theorem pu_leu32 (buf : io.ParseBuf) (h : 4 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32) buf ()
      ⦃ r rest => ∃ v, r = .Ok v ∧ v.1.val = leNat (buf.val.take 4) ∧ rest.val = buf.val.drop 4 ⦄ := by
  have h' := misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec buf h
  exact pu_rawint misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32 buf 4 (fun x : U32 => x.val) h'

@[step] theorem pu_leu16 (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16) buf ()
      ⦃ r rest => ∃ v, r = .Ok v ∧ v.1.val = leNat (buf.val.take 2) ∧ rest.val = buf.val.drop 2 ⦄ := by
  have h' := misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec buf h
  exact pu_rawint misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16 buf 2 (fun x : U16 => x.val) h'

@[step] theorem pu_u8 (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      U8.Insts.Mysql_commonMiscRawIntIntReprU8) buf ()
      ⦃ r rest => ∃ v, r = .Ok v ∧ v.1.val = leNat (buf.val.take 1) ∧ rest.val = buf.val.drop 1 ⦄ := by
  have h' := U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec buf h
  exact pu_rawint U8.Insts.Mysql_commonMiscRawIntIntReprU8 buf 1 (fun x : U8 => x.val) h'

@[step] theorem pu_const_u8 (U : Type) (buf : io.ParseBuf) (h : 1 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw._const.RawConst.Insts.Mysql_commonProtoMyDeserializeDeTuple U
      U8.Insts.Mysql_commonMiscRawIntIntReprU8) buf ()
      ⦃ r rest => ∃ v, r = .Ok v ∧ v.1.val = leNat (buf.val.take 1) ∧ rest.val = buf.val.drop 1 ⦄ := by
  have h' := U8.Insts.Mysql_commonMiscRawIntIntReprU8.deserialize_spec buf h
  exact pu_rawconst U U8.Insts.Mysql_commonMiscRawIntIntReprU8 buf 1 (fun x : U8 => x.val) h'

@[step] theorem pu_flags_leu16 {T : Type} (fl : bitflags.traits.Flags T U16) (buf : io.ParseBuf) (h : 2 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.flags.RawFlags.Insts.Mysql_commonProtoMyDeserializeDeTuple fl
      misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16) buf ()
      ⦃ r rest => ∃ v, r = .Ok v ∧ v.1.val = leNat (buf.val.take 2) ∧ rest.val = buf.val.drop 2 ⦄ :=
  pu_rawflags fl _ buf 2 (·.val) (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.deserialize_spec buf h)

@[step] theorem pu_usize (buf : io.ParseBuf) (n : Usize) :
    io.ParseBuf.parse_unchecked io.ParseBuf.Insts.Mysql_commonProtoMyDeserializeDeUsize buf n ⦃ r rest =>
      if n.val ≤ buf.length then
        ∃ pb, r = .Ok pb ∧ pb.val = buf.val.take n.val ∧ rest.val = buf.val.drop n.val
      else okPart r = none ∧ rest = buf ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  apply WP.spec_mono (PBUtil.deserialize_usize_ok n buf)
  rintro ⟨r, rest⟩ h
  split_ifs at h ⊢
  · obtain ⟨h1, h2⟩ := h
    cases r with
    | Ok pb => exact ⟨pb, rfl, by simpa [okPart] using h1, h2⟩
    | Err e => simp [okPart] at h1
  · exact h

/-! ## The readers consume everything -/

theorem queryRead_tail (p : Nat) (bs : List U8) (v : QueryView) (t : List U8) (ht : queryRead p bs = some (v, t)) : t = [] := by
  simp only [queryRead, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at ht
  aesop

theorem tmRead_tail (p : Nat) (bs : List U8) (v : TmView) (t : List U8) (ht : tmRead p bs = some (v, t)) : t = [] := by
  unfold tmRead at ht
  split at ht <;> (simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at ht; aesop)

theorem fdeRead_tail (bs : List U8) (v : FdeView) (t : List U8) (ht : fdeRead bs = some (v, t)) : t = [] := by
  unfold fdeRead at ht
  split at ht
  · simp at ht
  · split at ht
    · simp at ht
    · split at ht
      · simp at ht
      · simp only [Option.some.injEq, Prod.mk.injEq] at ht; exact ht.2.symm

theorem rotateRead_tail (bs : List U8) (v : Nat × List U8) (t : List U8) (ht : rotateRead bs = some (v, t)) : t = [] := by
  unfold rotateRead at ht
  split at ht
  · simp only [Option.some.injEq, Prod.mk.injEq] at ht; exact ht.2.symm
  · simp at ht

end mysql_common.EvHdrUtil
