import Proofs.Util.BinlogValue
import Proofs.Binlog.Misc.TimeFromPacked
import Proofs.Binlog.Misc.DatetimeFromPacked
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedVariables false

/-! `BinlogValue::deserialize` per column type against `Defs.binlogRead` (helpers for
`Proofs/Binlog/Value/BinlogValue.lean`). -/
open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.BinlogUtil
open constants.ColumnType

local notation "BVdes" => binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize

/-- How a crate result relates to the intended `BinlogOut`. -/
def binRel : BinlogOut → core.result.Result binlog.value.BinlogValue core.io.error.Error → io.ParseBuf → Prop
  | .ok v rest', r, rest => (okPart r).map binlogValView = some (some v) ∧ rest.val = rest'
  | .err rest', r, rest => okPart r = none ∧ rest.val = rest'
  | _, _, _ => True

theorem slice_parse_eq (buf : io.ParseBuf) (n : Usize) :
    io.ParseBuf.parse SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize buf n =
      SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize n buf :=
  io.ParseBuf.parse_of_size_none _ _ _ (by simp [SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize, SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE])

theorem binlogStr_long (k : Nat) (bs : List U8) (hk : k ≤ bs.length) (hn : leNat (bs.take k) ≤ (bs.drop k).length) :
    binlogStr k bs = .ok (.bytes ((bs.drop k).take (leNat (bs.take k)))) ((bs.drop k).drop (leNat (bs.take k))) := by
  have : leNat (bs.take k) ≤ bs.length - k := by simpa using hn
  simp [binlogStr, checkedLenPrefixed, readLE, hk, this]

theorem binlogStr_short1 (k : Nat) (bs : List U8) (hk : ¬ k ≤ bs.length) : binlogStr k bs = .err bs := by
  simp [binlogStr, checkedLenPrefixed, readLE, hk]

theorem binlogStr_short2 (k : Nat) (bs : List U8) (hk : k ≤ bs.length) (hn : ¬ leNat (bs.take k) ≤ (bs.drop k).length) :
    binlogStr k bs = .err (bs.drop k) := by
  have : ¬ leNat (bs.take k) ≤ bs.length - k := by simpa using hn
  simp [binlogStr, checkedLenPrefixed, readLE, hk, this]

theorem leNat_take_lt (bs : List U8) (k : Nat) : leNat (bs.take k) < 2 ^ (8 * k) := by
  have := PBUtil.leNat_lt (bs.take k)
  have : 2 ^ (8 * (bs.take k).length) ≤ 2 ^ (8 * k) := Nat.pow_le_pow_right (by norm_num) (by simp)
  omega

set_option hygiene false in
/-- A `k`-byte length prefix read with `rparse`, then that many bytes: `binlogStr k`. -/
local macro "lenpref_tac " rparse:term:max k:term:max : tactic => `(tactic| (
  step with $rparse as ⟨r, buf1, hr⟩
  split_ifs at hr with hk
  · obtain ⟨⟨xv, xu⟩, rfl⟩ : ∃ x, r = .Ok x := by cases r <;> simp_all [okPart]
    simp only [okPart, Option.map, Option.some.injEq] at hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, Std.uncurry_apply_pair,
      misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref, lift, slice_parse_eq]
    have hc : (UScalar.cast .Usize xv).val = leNat (buf.val.take $k) := by
      rw [IntAndMisc.cast_usize_small _ (by have := leNat_take_lt buf.val $k; norm_num at this; omega)]; exact hr.1
    step with SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec (UScalar.cast .Usize xv) buf1 as ⟨r1, buf2, hr1⟩
    have hkl : $k ≤ buf.val.length := by simpa [Slice.length] using hk
    split_ifs at hr1 with hn
    · obtain ⟨v1, rfl⟩ : ∃ x, r1 = .Ok x := by cases r1 <;> simp_all [okPart]
      simp only [okPart, Option.map, Option.some.injEq] at hr1
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
      step*
      rw [binlogStr_long _ _ hkl (by rw [← hc, ← hr.2]; simpa [Slice.length] using hn)]
      simp only [binRel, okPart, Option.map, binlogValView, Val.ofValue]
      have hv : v.val = v1.val := by rw [v1_post]; rfl
      exact ⟨by rw [hv, hr1.1, hc, hr.2], by rw [hr1.2, hc, hr.2]⟩
    · obtain ⟨hr1a, rfl⟩ := hr1
      cases r1 with
      | Ok _ => simp [okPart] at hr1a
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, from_residual_eq, WP.spec_ok]
        rw [binlogStr_short2 _ _ hkl (by rw [← hc, ← hr.2]; simpa [Slice.length] using hn)]
        simp [binRel, okPart, hr.2]
  · obtain ⟨hra, rfl⟩ := hr
    cases r with
    | Ok _ => simp [okPart] at hra
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, from_residual_eq, WP.spec_ok]
      rw [binlogStr_short1 _ _ (by simpa [Slice.length] using hk)]
      simp [binRel, okPart]))

theorem effType_ne (x : constants.ColumnType) (md : List U8) (h : x ≠ MYSQL_TYPE_TYPED_ARRAY) : binlogEffType x md = x := by
  cases x <;> first | rfl | exact absurd rfl h

theorem effType_idem (ct : constants.ColumnType) (md : List U8) :
    binlogEffType (binlogEffType ct md) md = binlogEffType ct md := by
  by_cases hc : ct = MYSQL_TYPE_TYPED_ARRAY
  · subst hc
    rcases md with _ | ⟨b, l⟩
    · rfl
    · by_cases ht : binlogEffType MYSQL_TYPE_TYPED_ARRAY (b :: l) = MYSQL_TYPE_TYPED_ARRAY
      · rw [ht]; exact ht
      · exact effType_ne _ _ ht
  · rw [effType_ne ct md hc, effType_ne ct md hc]

theorem binlogRead_eff (ct : constants.ColumnType) (md : List U8) (uns : Bool) (bs : List U8)
    (hne : ¬(ct = MYSQL_TYPE_TYPED_ARRAY ∧ md = [])) :
    binlogRead ct md uns bs = binlogRead (binlogEffType ct md) md uns bs := by
  by_cases hc : ct = MYSQL_TYPE_TYPED_ARRAY
  · subst hc
    rcases md with _ | ⟨b, l⟩
    · exact absurd ⟨rfl, rfl⟩ hne
    · generalize ht : binlogEffType MYSQL_TYPE_TYPED_ARRAY (b :: l) = t'
      cases t' <;> (unfold binlogRead; simp only [ht]) <;> rfl
  · rw [effType_ne ct md hc]

theorem binlogBug_eff (ct : constants.ColumnType) (md : List U8) (uns : Bool) (bs : List U8) :
    binlogBug ct md uns bs = binlogBug (binlogEffType ct md) md uns bs := by
  unfold binlogBug; rw [effType_idem]

theorem meta_of_nopanic (t : constants.ColumnType) (md : List U8) (uns : Bool) (bs : List U8)
    (ht : ¬(t = MYSQL_TYPE_TYPED_ARRAY ∧ md = [])) (hp : ∀ e, binlogRead t md uns bs ≠ .panic e) :
    binlogMetaLen (binlogEffType t md) ≤ md.length := by
  by_contra hlt
  unfold binlogRead at hp
  split at hp
  · exact ht ⟨rfl, rfl⟩
  · exact hp _ (if_pos (by omega))

theorem flags_spec (uns : Bool) :
    (do let f ← constants.ColumnFlags.empty; constants.ColumnFlags.set f constants.ColumnFlags.UNSIGNED_FLAG uns)
      ⦃ f => isUnsigned f = uns ⦄ := by
  step with constants.ColumnFlags.empty_spec as ⟨f, hf⟩
  step with constants.ColumnFlags.set_spec as ⟨g, hg⟩
  unfold isUnsigned
  rw [hg, hf]
  cases uns <;> simp [andNot, constants.ColumnFlags.UNSIGNED_FLAG] <;> decide

set_option hygiene false in
local macro "pre_tac " t:term:max : tactic => `(tactic| (
  rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
  simp only [Std.uncurry_apply_pair,
    show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq $t MYSQL_TYPE_TYPED_ARRAY = ok false from rfl,
    show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq $t MYSQL_TYPE_STRING = ok false from rfl,
    Std.bind_ok, Bool.false_eq_true, ite_false, lift]))

set_option hygiene false in
local macro "errty_tac " t:term:max : tactic => `(tactic| (
  pre_tac $t
  step with IntAndMisc.io_error_msg_spec as ⟨e⟩
  simp [binlogRead, binlogEffType, binlogMetaLen, binRel, okPart]))

set_option hygiene false in
local macro "binty_tac " t:term:max : tactic => `(tactic| (
  pre_tac $t
  step with constants.ColumnFlags.empty_spec as ⟨f, hf⟩
  step with constants.ColumnFlags.set_spec as ⟨g, hg⟩
  have hu : isUnsigned g = uns := by
    unfold isUnsigned; rw [hg, hf]; cases uns <;> simp [andNot, constants.ColumnFlags.UNSIGNED_FLAG] <;> decide
  step with value.Value.deserialize_bin_spec h64 $t g rfl buf as ⟨r, rest, hr⟩
  rw [hu] at hr
  simp only [binlogRead, binlogEffType, binlogMetaLen, Nat.not_lt_zero, ite_false]
  rw [← hr]
  cases r <;> simp [binRel, BinlogOut.ofRead, okPart, binlogValView]))

set_option hygiene false in
/-- A fixed-size `RawInt` read: closes the short-input branch; leaves the success branch with
`hx : xv.val = leNat (take k)` and `hb1 : buf1 = drop k`. -/
local macro "rawint_tac " rparse:term:max k:term:max : tactic => `(tactic| (
  step with $rparse as ⟨r, buf1, hr⟩
  split_ifs at hr with hk
  case neg =>
    obtain ⟨hra, hrb⟩ := hr
    have hk' : ¬ $k ≤ buf.val.length := by simpa [Slice.length] using hk
    cases r with
    | Ok _ => simp [okPart] at hra
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, from_residual_eq, WP.spec_ok, WP.uncurry'_pair]
      simp [hrb, binlogRead, binlogEffType, binlogMetaLen, binlogNum, readLE, binRel, okPart, hk']
  obtain ⟨⟨xv, xu⟩, rfl⟩ : ∃ x, r = .Ok x := by cases r <;> simp_all [okPart]
  simp only [okPart, Option.map, Option.some.injEq] at hr
  obtain ⟨hx, hb1⟩ := hr
  have hkl : $k ≤ buf.val.length := by simpa [Slice.length] using hk
  have hxb := leNat_take_lt buf.val $k
  simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, Std.uncurry_apply_pair,
    misc.raw.int.RawInt.Insts.CoreOpsDerefDeref.deref, lift]))

set_option hygiene false in
/-- `n` bytes of the input (`n_bytes.val = N`), as `Bytes`: `binlogTake N`. -/
local macro "take_tac " nb:term:max N:term:max hn:term:max : tactic => `(tactic| (
  rw [slice_parse_eq]
  step with SharedDeSliceU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec $nb buf as ⟨r, buf1, hr⟩
  split_ifs at hr with hk
  case neg =>
    obtain ⟨hra, hrb⟩ := hr
    cases r with
    | Ok _ => simp [okPart] at hra
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, from_residual_eq, WP.spec_ok, WP.uncurry'_pair]
      have hk' : ¬ $N ≤ buf.val.length := by rw [← $hn:term]; simpa [Slice.length] using hk
      simp only [binlogTake, hk', ite_false]
      simp [hrb, binRel, okPart]
  obtain ⟨v1, rfl⟩ : ∃ x, r = .Ok x := by cases r <;> simp_all [okPart]
  simp only [okPart, Option.map, Option.some.injEq] at hr
  simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
  step*
  have hk' : $N ≤ buf.val.length := by rw [← $hn:term]; simpa [Slice.length] using hk
  have hv : v.val = v1.val := by rw [v1_post]; rfl
  simp only [binlogTake, hk', ite_true, binRel, okPart, Option.map, binlogValView, Val.ofValue]
  exact ⟨by rw [hv, hr.1, $hn:term], by rw [hr.2, $hn:term]⟩))

theorem and31 (x : Nat) : x &&& 31 = x % 32 := Nat.and_two_pow_sub_one_eq_mod x 5
theorem and15 (x : Nat) : x &&& 15 = x % 16 := Nat.and_two_pow_sub_one_eq_mod x 4

set_option hygiene false in
local macro "blob_tac " T:term:max : tactic => `(tactic| (
  have hm1 : 1 ≤ md.val.length := by simpa [binlogMetaLen] using hmeta
  obtain ⟨m0, t, hmd⟩ : ∃ m0 t, md.val = m0 :: t := by
    rcases h : md.val with _ | ⟨a, t⟩ <;> simp_all
  pre_tac $T
  simp only [index0 md m0 _ hmd, Std.bind_ok]
  have hg : (md.val.getD 0 (byte 0)) = m0 := by simp [hmd]
  split
  case h_1 =>
    rw [show binlogRead $T md.val uns buf.val = binlogStr 1 buf.val by
      simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 1 from by omega, ite_false, hg]; rfl]
    lenpref_tac (U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec buf) 1
  case h_2 =>
    rw [show binlogRead $T md.val uns buf.val = binlogStr 2 buf.val by
      simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 1 from by omega, ite_false, hg]; rfl]
    lenpref_tac (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.parse_rawint_spec buf) 2
  case h_3 =>
    rw [show binlogRead $T md.val uns buf.val = binlogStr 3 buf.val by
      simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 1 from by omega, ite_false, hg]; rfl]
    lenpref_tac (misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf) 3
  case h_4 =>
    rw [show binlogRead $T md.val uns buf.val = binlogStr 4 buf.val by
      simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 1 from by omega, ite_false, hg]; rfl]
    lenpref_tac (misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf) 4
  case h_5 n1 n2 n3 n4 =>
    have hv : ¬ (1 ≤ m0.val ∧ m0.val ≤ 4) := by
      intro ⟨a, b⟩
      have : m0.val = 1 ∨ m0.val = 2 ∨ m0.val = 3 ∨ m0.val = 4 := by omega
      rcases this with h | h | h | h
      · exact n1 (UScalar.eq_of_val_eq (by simpa [PBUtil.val_mk] using h))
      · exact n2 (UScalar.eq_of_val_eq (by simpa [PBUtil.val_mk] using h))
      · exact n3 (UScalar.eq_of_val_eq (by simpa [PBUtil.val_mk] using h))
      · exact n4 (UScalar.eq_of_val_eq (by simpa [PBUtil.val_mk] using h))
    step with IntAndMisc.io_error_msg_spec as ⟨e⟩
    simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 1 from by omega, ite_false, hg, hv]
    simp [binRel, okPart]))

theorem hcast64_u32 (x : U32) : (UScalar.hcast .I64 x).val = x.val := by
  rw [UScalar.hcast_val_eq]; have := x.hBounds; simp only [IScalarTy.numBits]; unfold Int.bmod
  have : ((x.val : Int) % ((2^64 : Nat) : Int)) = x.val := Int.emod_eq_of_lt (by omega) (by simp at this ⊢; omega)
  simp only [this]; split_ifs <;> simp at * <;> omega

theorem hcast64_u16 (x : U16) : (UScalar.hcast .I64 x).val = x.val := by
  rw [UScalar.hcast_val_eq]; have := x.hBounds; simp only [IScalarTy.numBits]; unfold Int.bmod
  have : ((x.val : Int) % ((2^64 : Nat) : Int)) = x.val := Int.emod_eq_of_lt (by omega) (by simp at this ⊢; omega)
  simp only [this]; split_ifs <;> simp at * <;> omega

theorem hcast64_u8 (x : U8) : (UScalar.hcast .I64 x).val = x.val := by
  rw [UScalar.hcast_val_eq]; have := x.hBounds; simp only [IScalarTy.numBits]; unfold Int.bmod
  have : ((x.val : Int) % ((2^64 : Nat) : Int)) = x.val := Int.emod_eq_of_lt (by omega) (by simp at this ⊢; omega)
  simp only [this]; split_ifs <;> simp at * <;> omega


theorem deser_MYSQL_TYPE_DECIMAL (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_DECIMAL ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_DECIMAL md.val uns buf.val) :
    BVdes (MYSQL_TYPE_DECIMAL, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_DECIMAL md.val uns buf.val) r rest ⦄ := by
  errty_tac MYSQL_TYPE_DECIMAL

theorem deser_MYSQL_TYPE_NULL (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_NULL ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_NULL md.val uns buf.val) :
    BVdes (MYSQL_TYPE_NULL, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_NULL md.val uns buf.val) r rest ⦄ := by
  errty_tac MYSQL_TYPE_NULL

theorem deser_MYSQL_TYPE_DATE (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_DATE ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_DATE md.val uns buf.val) :
    BVdes (MYSQL_TYPE_DATE, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_DATE md.val uns buf.val) r rest ⦄ := by
  errty_tac MYSQL_TYPE_DATE

theorem deser_MYSQL_TYPE_UNKNOWN (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_UNKNOWN ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_UNKNOWN md.val uns buf.val) :
    BVdes (MYSQL_TYPE_UNKNOWN, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_UNKNOWN md.val uns buf.val) r rest ⦄ := by
  errty_tac MYSQL_TYPE_UNKNOWN

theorem deser_MYSQL_TYPE_TINY (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_TINY ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_TINY md.val uns buf.val) :
    BVdes (MYSQL_TYPE_TINY, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_TINY md.val uns buf.val) r rest ⦄ := by
  binty_tac MYSQL_TYPE_TINY

theorem deser_MYSQL_TYPE_SHORT (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_SHORT ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_SHORT md.val uns buf.val) :
    BVdes (MYSQL_TYPE_SHORT, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_SHORT md.val uns buf.val) r rest ⦄ := by
  binty_tac MYSQL_TYPE_SHORT

theorem deser_MYSQL_TYPE_LONG (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_LONG ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_LONG md.val uns buf.val) :
    BVdes (MYSQL_TYPE_LONG, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_LONG md.val uns buf.val) r rest ⦄ := by
  binty_tac MYSQL_TYPE_LONG

theorem deser_MYSQL_TYPE_LONGLONG (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_LONGLONG ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_LONGLONG md.val uns buf.val) :
    BVdes (MYSQL_TYPE_LONGLONG, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_LONGLONG md.val uns buf.val) r rest ⦄ := by
  binty_tac MYSQL_TYPE_LONGLONG

theorem deser_MYSQL_TYPE_FLOAT (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_FLOAT ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_FLOAT md.val uns buf.val) :
    BVdes (MYSQL_TYPE_FLOAT, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_FLOAT md.val uns buf.val) r rest ⦄ := by
  binty_tac MYSQL_TYPE_FLOAT

theorem deser_MYSQL_TYPE_DOUBLE (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_DOUBLE ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_DOUBLE md.val uns buf.val) :
    BVdes (MYSQL_TYPE_DOUBLE, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_DOUBLE md.val uns buf.val) r rest ⦄ := by
  binty_tac MYSQL_TYPE_DOUBLE

theorem deser_MYSQL_TYPE_TIMESTAMP (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_TIMESTAMP ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_TIMESTAMP md.val uns buf.val) :
    BVdes (MYSQL_TYPE_TIMESTAMP, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_TIMESTAMP md.val uns buf.val) r rest ⦄ := by
  pre_tac MYSQL_TYPE_TIMESTAMP
  rawint_tac (misc.raw.int.LeU32.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf) 4
  simp [WP.spec_ok, WP.uncurry'_pair, binlogRead, binlogEffType, binlogMetaLen, binlogNum, readLE, hkl, binRel, okPart, binlogValView,
    Val.ofValue, hb1, ← hx, hcast64_u32]

theorem deser_MYSQL_TYPE_INT24 (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_INT24 ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_INT24 md.val uns buf.val) :
    BVdes (MYSQL_TYPE_INT24, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_INT24 md.val uns buf.val) r rest ⦄ := by
  pre_tac MYSQL_TYPE_INT24
  cases uns
  · simp only [Bool.false_eq_true, ite_false]
    rawint_tac (misc.raw.int.LeI24.Insts.Mysql_commonMiscRawIntIntReprI32.parse_rawint_spec buf) 3
    have hlt : leNat (buf.val.take 3) < 2 ^ 23 := by
      by_contra hc; exact hb (by simp only [binlogBug, binlogEffType]; exact ⟨trivial, hkl, by omega⟩)
    simp [WP.spec_ok, WP.uncurry'_pair, binlogRead, binlogEffType, binlogMetaLen, binlogNum, readLE, hkl, binRel, okPart, binlogValView,
      Val.ofValue, hb1, cast64_i32, hx, toSigned, hlt]
    omega
  · simp only [ite_true]
    rawint_tac (misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf) 3
    simp [WP.spec_ok, WP.uncurry'_pair, binlogRead, binlogEffType, binlogMetaLen, binlogNum, readLE, hkl, binRel, okPart, binlogValView,
      Val.ofValue, hb1, ← hx, hcast64_u32]

theorem deser_MYSQL_TYPE_TIME (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_TIME ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_TIME md.val uns buf.val) :
    BVdes (MYSQL_TYPE_TIME, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_TIME md.val uns buf.val) r rest ⦄ := by
  pre_tac MYSQL_TYPE_TIME
  rawint_tac (misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf) 3
  have hlt : leNat (buf.val.take 3) < 2 ^ 23 ∧ leNat (buf.val.take 3) / 10000 < 256 := by
    by_contra hc; exact hb (by simp only [binlogBug, binlogEffType]; exact ⟨hkl, by omega⟩)
  step*
  have hts : toSigned 24 (leNat (buf.val.take 3)) = (leNat (buf.val.take 3) : Int) := by
    unfold toSigned; rw [if_pos (by omega)]
  simp only [WP.spec_ok, WP.uncurry'_pair, binlogRead, binlogEffType, binlogMetaLen, binlogNum, readLE, hkl, binRel,
    okPart, binlogValView, Val.ofValue, hb1, oldTimeVal, hts, Int.natAbs_natCast, if_true, Nat.not_lt_zero, ite_false,
    Option.map, Option.some.injEq, Val.time.injEq, BinlogOut.ok.injEq]
  simp only [UScalar.cast_val_eq, UScalarTy.numBits] at *
  and_intros <;> first | rfl | (simp; done) | omega

theorem deser_MYSQL_TYPE_DATETIME (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_DATETIME ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_DATETIME md.val uns buf.val) :
    BVdes (MYSQL_TYPE_DATETIME, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_DATETIME md.val uns buf.val) r rest ⦄ := by
  pre_tac MYSQL_TYPE_DATETIME
  rawint_tac (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.parse_rawint_spec buf) 8
  step*
  simp only [WP.spec_ok, WP.uncurry'_pair, binlogRead, binlogEffType, binlogMetaLen, binlogNum, readLE, hkl, binRel,
    okPart, binlogValView, Val.ofValue, hb1, if_true, Nat.not_lt_zero, ite_false,
    Option.map, Option.some.injEq, Val.date.injEq]
  simp only [UScalar.cast_val_eq, UScalarTy.numBits] at *
  and_intros <;> first | rfl | (simp; done) | omega

theorem deser_MYSQL_TYPE_YEAR (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_YEAR ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_YEAR md.val uns buf.val) :
    BVdes (MYSQL_TYPE_YEAR, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_YEAR md.val uns buf.val) r rest ⦄ := by
  pre_tac MYSQL_TYPE_YEAR
  rawint_tac (U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec buf) 1
  have hy0 : leNat (buf.val.take 1) ≠ 0 := by
    intro h0; apply hb; simp only [binlogBug, binlogEffType]
    rcases hbuf : buf.val with _ | ⟨c, l⟩
    · simp [hbuf] at hkl
    · simp [hbuf, leNat] at h0 ⊢; omega
  have hyv : (UScalar.hcast IScalarTy.I32 xv).val = leNat (buf.val.take 1) := by
    rw [UScalar.hcast_val_eq, hx]; have := hxb; simp only [IScalarTy.numBits]; unfold Int.bmod
    have : ((leNat (buf.val.take 1) : Int) % ((2^32 : Nat) : Int)) = leNat (buf.val.take 1) := Int.emod_eq_of_lt (by omega) (by norm_num at this ⊢; omega)
    simp only [this]; split_ifs <;> norm_num at * <;> omega
  have := ConvInts.usize_max_ge
  have hlen := ConvInts.decimalBytes_length (1900 + (leNat (buf.val.take 1) : Int)) (by norm_num at hxb; omega)
  step
  step with i128_to_string_spec' as ⟨st, hst⟩
  have hi : (IScalar.cast IScalarTy.I128 i1).val = 1900 + (leNat (buf.val.take 1) : Int) := by rw [cast128_i32, i1_post, hyv]
  rw [hi] at hst
  step with string_into_bytes_spec' st (by rw [hst]; omega) as ⟨v, hv⟩
  simp only [WP.spec_ok, WP.uncurry'_pair, binlogRead, binlogEffType, binlogMetaLen, binlogNum, readLE, hkl, binRel,
    okPart, binlogValView, Val.ofValue, hb1, if_true, Nat.not_lt_zero, ite_false, hy0,
    Option.map, Option.some.injEq, Val.bytes.injEq, hv, hst, and_true]

theorem deser_MYSQL_TYPE_NEWDATE (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_NEWDATE ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_NEWDATE md.val uns buf.val) :
    BVdes (MYSQL_TYPE_NEWDATE, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_NEWDATE md.val uns buf.val) r rest ⦄ := by
  pre_tac MYSQL_TYPE_NEWDATE
  rawint_tac (misc.raw.int.LeU24.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec buf) 3
  step*
  simp only [WP.spec_ok, WP.uncurry'_pair, binlogRead, binlogEffType, binlogMetaLen, binlogNum, readLE, hkl, binRel,
    okPart, binlogValView, Val.ofValue, hb1, if_true, Nat.not_lt_zero, ite_false,
    Option.map, Option.some.injEq, Val.date.injEq]
  simp only [UScalar.cast_val_eq, UScalarTy.numBits, UScalar.val_and, Nat.shiftRight_eq_div_pow] at *
  simp only [UScalar.val_and, show (31#u32 : U32).val = 31 from rfl, show (15#u32 : U32).val = 15 from rfl, and31, and15] at *
  and_intros <;> first | rfl | (simp; done) | omega

theorem deser_MYSQL_TYPE_BIT (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_BIT ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_BIT md.val uns buf.val) :
    BVdes (MYSQL_TYPE_BIT, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_BIT md.val uns buf.val) r rest ⦄ := by
  have hm2 : 2 ≤ md.val.length := by simpa [binlogMetaLen] using hmeta
  obtain ⟨m0, m1, t, hmd⟩ : ∃ m0 m1 t, md.val = m0 :: m1 :: t := by
    rcases h : md.val with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp_all
  pre_tac MYSQL_TYPE_BIT
  simp only [index0 md m0 _ hmd, index1 md m0 m1 t hmd, Std.bind_ok]
  have c0 := IntAndMisc.cast_usize_small m0 (by have := u8_lt m0; omega)
  have c1 := IntAndMisc.cast_usize_small m1 (by have := u8_lt m1; omega)
  have b0 := u8_lt m0
  have b1 := u8_lt m1
  have := IntAndMisc.usize_pow_ge
  step*
  have hn : n_bytes.val = ((md.val.getD 1 (byte 0)).val * 8 + (md.val.getD 0 (byte 0)).val + 7) / 8 := by
    rw [n_bytes_post, n_bits_post, i2_post, c0, c1, Nat.ceilDiv_eq_add_pred_div]; simp [hmd]
  simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 2 from by omega, ite_false]
  take_tac n_bytes (((md.val.getD 1 (byte 0)).val * 8 + (md.val.getD 0 (byte 0)).val + 7) / 8) hn

theorem deser_MYSQL_TYPE_TINY_BLOB (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_TINY_BLOB ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_TINY_BLOB md.val uns buf.val) :
    BVdes (MYSQL_TYPE_TINY_BLOB, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_TINY_BLOB md.val uns buf.val) r rest ⦄ := by
  blob_tac MYSQL_TYPE_TINY_BLOB

theorem deser_MYSQL_TYPE_MEDIUM_BLOB (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_MEDIUM_BLOB ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_MEDIUM_BLOB md.val uns buf.val) :
    BVdes (MYSQL_TYPE_MEDIUM_BLOB, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_MEDIUM_BLOB md.val uns buf.val) r rest ⦄ := by
  blob_tac MYSQL_TYPE_MEDIUM_BLOB

theorem deser_MYSQL_TYPE_LONG_BLOB (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_LONG_BLOB ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_LONG_BLOB md.val uns buf.val) :
    BVdes (MYSQL_TYPE_LONG_BLOB, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_LONG_BLOB md.val uns buf.val) r rest ⦄ := by
  blob_tac MYSQL_TYPE_LONG_BLOB

theorem deser_MYSQL_TYPE_BLOB (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_BLOB ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_BLOB md.val uns buf.val) :
    BVdes (MYSQL_TYPE_BLOB, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_BLOB md.val uns buf.val) r rest ⦄ := by
  blob_tac MYSQL_TYPE_BLOB

theorem deser_MYSQL_TYPE_GEOMETRY (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_GEOMETRY ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_GEOMETRY md.val uns buf.val) :
    BVdes (MYSQL_TYPE_GEOMETRY, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_GEOMETRY md.val uns buf.val) r rest ⦄ := by
  blob_tac MYSQL_TYPE_GEOMETRY

theorem deser_MYSQL_TYPE_VECTOR (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_VECTOR ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_VECTOR md.val uns buf.val) :
    BVdes (MYSQL_TYPE_VECTOR, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_VECTOR md.val uns buf.val) r rest ⦄ := by
  blob_tac MYSQL_TYPE_VECTOR

theorem deser_MYSQL_TYPE_SET (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_SET ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_SET md.val uns buf.val) :
    BVdes (MYSQL_TYPE_SET, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_SET md.val uns buf.val) r rest ⦄ := by
  have hm2 : 2 ≤ md.val.length := by simpa [binlogMetaLen] using hmeta
  obtain ⟨m0, m1, t, hmd⟩ : ∃ m0 m1 t, md.val = m0 :: m1 :: t := by
    rcases h : md.val with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp_all
  pre_tac MYSQL_TYPE_SET
  simp only [index1 md m0 m1 t hmd, Std.bind_ok]
  have hn : (UScalar.cast .Usize m1).val = (md.val.getD 1 (byte 0)).val := by
    rw [IntAndMisc.cast_usize_small m1 (by have := u8_lt m1; omega)]; simp [hmd]
  simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 2 from by omega, ite_false]
  take_tac (UScalar.cast .Usize m1) ((md.val.getD 1 (byte 0)).val) hn

theorem deser_MYSQL_TYPE_ENUM (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_ENUM ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_ENUM md.val uns buf.val) :
    BVdes (MYSQL_TYPE_ENUM, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_ENUM md.val uns buf.val) r rest ⦄ := by
  have hm2 : 2 ≤ md.val.length := by simpa [binlogMetaLen] using hmeta
  obtain ⟨m0, m1, t, hmd⟩ : ∃ m0 m1 t, md.val = m0 :: m1 :: t := by
    rcases h : md.val with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp_all
  pre_tac MYSQL_TYPE_ENUM
  simp only [index1 md m0 m1 t hmd, Std.bind_ok]
  have hg : (md.val.getD 1 (byte 0)) = m1 := by simp [hmd]
  split
  case h_1 =>
    rw [show binlogRead MYSQL_TYPE_ENUM md.val uns buf.val = binlogNum 1 buf.val (fun n => .int n) by
      simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 2 from by omega, ite_false, hg]; rfl]
    rawint_tac (U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec buf) 1
    simp [WP.spec_ok, WP.uncurry'_pair, binlogNum, readLE, hkl, binRel,
      okPart, binlogValView, Val.ofValue, hb1, ← hx, hcast64_u8]
  case h_2 =>
    rw [show binlogRead MYSQL_TYPE_ENUM md.val uns buf.val = binlogNum 2 buf.val (fun n => .int n) by
      simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 2 from by omega, ite_false, hg]; rfl]
    rawint_tac (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.parse_rawint_spec buf) 2
    simp [WP.spec_ok, WP.uncurry'_pair, binlogNum, readLE, hkl, binRel,
      okPart, binlogValView, Val.ofValue, hb1, ← hx, hcast64_u16]
  case h_3 n1 n2 =>
    have hv1 : m1.val ≠ 1 := fun h => n1 (UScalar.eq_of_val_eq (by simpa [PBUtil.val_mk] using h))
    have hv2 : m1.val ≠ 2 := fun h => n2 (UScalar.eq_of_val_eq (by simpa [PBUtil.val_mk] using h))
    step with IntAndMisc.io_error_msg_spec as ⟨e⟩
    simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 2 from by omega, ite_false, hg, hv1, hv2]
    simp [binRel, okPart]

theorem deser_MYSQL_TYPE_VARCHAR (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_VARCHAR ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_VARCHAR md.val uns buf.val) :
    BVdes (MYSQL_TYPE_VARCHAR, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_VARCHAR md.val uns buf.val) r rest ⦄ := by
  have hm2 : 2 ≤ md.val.length := by simpa [binlogMetaLen] using hmeta
  obtain ⟨m0, m1, t, hmd⟩ : ∃ m0 m1 t, md.val = m0 :: m1 :: t := by
    rcases h : md.val with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp_all
  pre_tac MYSQL_TYPE_VARCHAR
  simp only [index0 md m0 _ hmd, index1 md m0 m1 t hmd, Std.bind_ok]
  have b0 := u8_lt m0
  have b1 := u8_lt m1
  step as ⟨i4, i4_post, i4_post1⟩
  have hlen : (UScalar.cast .Usize (UScalar.cast .U16 m0 ||| i4)).val = m0.val + 256 * m1.val := by
    have c0 : (UScalar.cast .U16 m0).val = m0.val := by rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
    have c1 : (UScalar.cast .U16 m1).val = m1.val := by rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
    rw [c1, Nat.shiftLeft_eq] at i4_post
    have hi4 : i4.val = m1.val * 256 := by rw [i4_post]; simp [U16.size, U16.numBits]; omega
    have hor : (UScalar.cast .U16 m0 ||| i4).val = m0.val + 256 * m1.val := by
      rw [UScalar.val_or, c0, hi4, Nat.lor_comm, show m1.val * 256 = m1.val <<< 8 by rw [Nat.shiftLeft_eq],
        ← Nat.shiftLeft_add_eq_or_of_lt (by omega : m0.val < 2 ^ 8), Nat.shiftLeft_eq]; ring
    rw [IntAndMisc.cast_usize_small _ (by rw [hor]; omega), hor]
  have hg0 : (md.val.getD 0 (byte 0)) = m0 := by simp [hmd]
  have hg1 : (md.val.getD 1 (byte 0)) = m1 := by simp [hmd]
  split_ifs with hlt
  · have hlt' : m0.val + 256 * m1.val < 256 := by rw [← hlen]; scalar_tac
    rw [show binlogRead MYSQL_TYPE_VARCHAR md.val uns buf.val = binlogStr 1 buf.val by
      simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 2 from by omega, ite_false, hg0, hg1, hlt', ite_true]]
    lenpref_tac (U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec buf) 1
  · have hlt' : ¬ m0.val + 256 * m1.val < 256 := by rw [← hlen]; scalar_tac
    rw [show binlogRead MYSQL_TYPE_VARCHAR md.val uns buf.val = binlogStr 2 buf.val by
      simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 2 from by omega, ite_false, hg0, hg1, hlt']]
    lenpref_tac (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.parse_rawint_spec buf) 2
theorem deser_MYSQL_TYPE_VAR_STRING (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_VAR_STRING ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_VAR_STRING md.val uns buf.val) :
    BVdes (MYSQL_TYPE_VAR_STRING, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_VAR_STRING md.val uns buf.val) r rest ⦄ := by
  have hm2 : 2 ≤ md.val.length := by simpa [binlogMetaLen] using hmeta
  obtain ⟨m0, m1, t, hmd⟩ : ∃ m0 m1 t, md.val = m0 :: m1 :: t := by
    rcases h : md.val with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp_all
  pre_tac MYSQL_TYPE_VAR_STRING
  simp only [index0 md m0 _ hmd, index1 md m0 m1 t hmd, Std.bind_ok]
  have b0 := u8_lt m0
  have b1 := u8_lt m1
  step as ⟨i4, i4_post, i4_post1⟩
  have hlen : (UScalar.cast .Usize (UScalar.cast .U16 m0 ||| i4)).val = m0.val + 256 * m1.val := by
    have c0 : (UScalar.cast .U16 m0).val = m0.val := by rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
    have c1 : (UScalar.cast .U16 m1).val = m1.val := by rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
    rw [c1, Nat.shiftLeft_eq] at i4_post
    have hi4 : i4.val = m1.val * 256 := by rw [i4_post]; simp [U16.size, U16.numBits]; omega
    have hor : (UScalar.cast .U16 m0 ||| i4).val = m0.val + 256 * m1.val := by
      rw [UScalar.val_or, c0, hi4, Nat.lor_comm, show m1.val * 256 = m1.val <<< 8 by rw [Nat.shiftLeft_eq],
        ← Nat.shiftLeft_add_eq_or_of_lt (by omega : m0.val < 2 ^ 8), Nat.shiftLeft_eq]; ring
    rw [IntAndMisc.cast_usize_small _ (by rw [hor]; omega), hor]
  have hg0 : (md.val.getD 0 (byte 0)) = m0 := by simp [hmd]
  have hg1 : (md.val.getD 1 (byte 0)) = m1 := by simp [hmd]
  split_ifs with hlt
  · have hlt' : m0.val + 256 * m1.val < 256 := by rw [← hlen]; scalar_tac
    rw [show binlogRead MYSQL_TYPE_VAR_STRING md.val uns buf.val = binlogStr 1 buf.val by
      simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 2 from by omega, ite_false, hg0, hg1, hlt', ite_true]]
    lenpref_tac (U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec buf) 1
  · have hlt' : ¬ m0.val + 256 * m1.val < 256 := by rw [← hlen]; scalar_tac
    rw [show binlogRead MYSQL_TYPE_VAR_STRING md.val uns buf.val = binlogStr 2 buf.val by
      simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 2 from by omega, ite_false, hg0, hg1, hlt']]
    lenpref_tac (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.parse_rawint_spec buf) 2

theorem deser_MYSQL_TYPE_STRING (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_STRING ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_STRING md.val uns buf.val) :
    BVdes (MYSQL_TYPE_STRING, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_STRING md.val uns buf.val) r rest ⦄ := by
  have hm2 : 2 ≤ md.val.length := by simpa [binlogMetaLen] using hmeta
  obtain ⟨m0, m1, t, hmd⟩ : ∃ m0 m1 t, md.val = m0 :: m1 :: t := by
    rcases h : md.val with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp_all
  have b0 := u8_lt m0
  have b1 := u8_lt m1
  have hg0 : (md.val.getD 0 (byte 0)) = m0 := by simp [hmd]
  have hg1 : (md.val.getD 1 (byte 0)) = m1 := by simp [hmd]
  rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
  simp only [Std.uncurry_apply_pair,
    show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_STRING MYSQL_TYPE_TYPED_ARRAY = ok false from rfl,
    show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_STRING MYSQL_TYPE_STRING = ok true from rfl,
    Std.bind_ok, Bool.false_eq_true, ite_false, ite_true, lift, index0 md m0 _ hmd, index1 md m0 m1 t hmd]
  have hrd : ∀ L : Nat, stringFieldLen m0.val m1.val = L →
      binlogRead MYSQL_TYPE_STRING md.val uns buf.val = binlogStr (if L < 256 then 1 else 2) buf.val := by
    intro L hL
    simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 2 from by omega, ite_false, hg0, hg1, hL]
  have c0 := IntAndMisc.cast_usize_small m0 (by omega)
  have c1 := IntAndMisc.cast_usize_small m1 (by omega)
  have v48 : (48#usize : Usize).val = 48 := by simp
  by_cases h0 : m0 ≥ 1#u8
  · have h0' : 1 ≤ m0.val := by scalar_tac
    have hsl := stringFieldLen_lt m0.val m1.val h0' b1
    simp only [h0, ite_true]
    by_cases h48 : (UScalar.cast UScalarTy.Usize m0 &&& 48#usize != 48#usize) = true
    · have h48' : m0.val &&& 48 ≠ 48 := by
        simp only [bne_iff_ne, ne_eq] at h48
        intro hc; apply h48; apply UScalar.eq_of_val_eq; rw [UScalar.val_and, c0, v48, hc]
      simp only [h48, ite_true]
      have hx : ((UScalar.cast UScalarTy.Usize m0 &&& 48#usize) ^^^ 48#usize).val = (m0.val &&& 48) ^^^ 48 := by
        rw [UScalar.val_xor, UScalar.val_and, c0, v48]
      have hxb : (m0.val &&& 48) ^^^ 48 < 2 ^ 6 :=
        Nat.xor_lt_two_pow (lt_of_le_of_lt Nat.and_le_right (by norm_num)) (by norm_num)
      step as ⟨i5, i5_post, i5_post1⟩
      case hy => cases System.Platform.numBits_eq <;> simp_all
      have hLv : (UScalar.cast UScalarTy.Usize m1 ||| i5).val = stringFieldLen m0.val m1.val := by
        rw [UScalar.val_or, c1, i5_post, hx]
        simp only [stringFieldLen, h0', ite_true, h48', ne_eq, not_false_eq_true]
        have hs : ((m0.val &&& 48) ^^^ 48) <<< 4 < Usize.size := by
          rw [Nat.shiftLeft_eq]; have : (m0.val &&& 48 ^^^ 48) * 2 ^ 4 < 1024 := by omega
          scalar_tac
        rw [Nat.mod_eq_of_lt hs]
      try simp only [Std.bind_ok]
      split_ifs with hlt
      · have hlt' : stringFieldLen m0.val m1.val < 256 := by rw [← hLv]; rw [UScalar.lt_equiv] at hlt; simpa using hlt
        rw [hrd _ rfl, if_pos hlt']
        lenpref_tac (U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec buf) 1
      · have hlt' : ¬ stringFieldLen m0.val m1.val < 256 := by rw [← hLv]; rw [UScalar.lt_equiv] at hlt; simpa using hlt
        rw [hrd _ rfl, if_neg hlt']
        lenpref_tac (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.parse_rawint_spec buf) 2
    · have h48' : m0.val &&& 48 = 48 := by
        rw [Bool.not_eq_true, bne_eq_false_iff_eq] at h48
        have := congrArg UScalar.val h48; rw [UScalar.val_and, c0, v48] at this; exact this
      rw [if_neg h48]
      simp only [Std.bind_ok]
      have hLv : (UScalar.cast UScalarTy.Usize m1).val = stringFieldLen m0.val m1.val := by
        rw [c1]; unfold stringFieldLen; rw [if_pos h0', if_neg (by rw [h48']; exact fun h => h rfl)]
      split_ifs with hlt
      · have hlt' : stringFieldLen m0.val m1.val < 256 := by rw [← hLv]; rw [UScalar.lt_equiv] at hlt; simpa using hlt
        rw [hrd _ rfl, if_pos hlt']
        lenpref_tac (U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec buf) 1
      · exfalso; rw [UScalar.lt_equiv, c1] at hlt; simp at hlt; omega
  · have h0' : m0.val = 0 := by scalar_tac
    simp only [h0, ite_false]
    step with io.ParseBuf.eat_u16_le_spec md (by simp [Slice.length]; omega) as ⟨pr, hi1, hmd2⟩
    obtain ⟨i1, mdr⟩ := pr
    simp only [Std.uncurry_apply_pair, Std.bind_ok] at *
    have hLv : (UScalar.cast UScalarTy.Usize i1).val = stringFieldLen m0.val m1.val := by
      rw [IntAndMisc.cast_usize_small _ (by have := i1.hBounds; simp at this; omega), hi1, hmd]
      simp [stringFieldLen, h0', leNat]
    split_ifs with hlt
    · have hlt' : stringFieldLen m0.val m1.val < 256 := by rw [← hLv]; rw [UScalar.lt_equiv] at hlt; simpa using hlt
      rw [hrd _ rfl, if_pos hlt']
      lenpref_tac (U8.Insts.Mysql_commonMiscRawIntIntReprU8.parse_rawint_spec buf) 1
    · have hlt' : ¬ stringFieldLen m0.val m1.val < 256 := by rw [← hLv]; rw [UScalar.lt_equiv] at hlt; simpa using hlt
      rw [hrd _ rfl, if_neg hlt']
      lenpref_tac (misc.raw.int.LeU16.Insts.Mysql_commonMiscRawIntIntReprU16.parse_rawint_spec buf) 2

theorem deser_MYSQL_TYPE_TIMESTAMP2 (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_TIMESTAMP2 ≤ md.val.length)
    (hno : binlogRead MYSQL_TYPE_TIMESTAMP2 md.val uns buf.val ≠ .opaque) :
    BVdes (MYSQL_TYPE_TIMESTAMP2, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_TIMESTAMP2 md.val uns buf.val) r rest ⦄ := by
  have hm1 : 1 ≤ md.val.length := by simpa [binlogMetaLen] using hmeta
  obtain ⟨m0, t, hmd⟩ : ∃ m0 t, md.val = m0 :: t := by
    rcases h : md.val with _ | ⟨a, t⟩ <;> simp_all
  have hg0 : (md.val.getD 0 (byte 0)) = m0 := by simp [hmd]
  pre_tac MYSQL_TYPE_TIMESTAMP2
  simp only [index0 md m0 _ hmd, Std.bind_ok]
  step with timestamp_spec buf m0 as ⟨r, rb, hr⟩
  simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 1 from by omega, ite_false, hg0] at hno ⊢
  rcases hT : timestamp2Read m0.val buf.val with _ | ⟨⟨sv, uv⟩, rest⟩
  · rw [hT] at hr
    simp only [Prod.mk.injEq] at hr
    cases r with
    | Ok _ => simp [okPart] at hr
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch, from_residual_eq, binRel, okPart, hr.2]
  · rw [hT] at hr hno
    simp only [Prod.mk.injEq] at hr
    obtain ⟨h1, h2⟩ := hr
    cases r with
    | Err _ => simp [okPart] at h1
    | Ok x =>
      obtain ⟨sec, usec⟩ := x
      simp only [okPart, Option.map, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨hs, hu⟩ := h1
      by_cases hu0 : uv = 0
      · have : usec = 0#i32 := IScalar.eq_of_val_eq (by rw [hu, hu0]; rfl)
        subst this
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, Std.uncurry_apply_pair]
        rw [if_pos trivial]
        simp only [hu0, ite_true]
        have := ConvInts.usize_max_ge
        have hsb : -2 ^ 31 ≤ sec.val ∧ sec.val < 2 ^ 31 := by have := sec.hBounds; simpa [IScalarTy.numBits] using this
        have hlen := ConvInts.decimalBytes_length sv (by omega)
        step with i128_to_string_spec' as ⟨st, hst⟩
        have hi : (IScalar.cast IScalarTy.I128 sec).val = sv := by rw [cast128_i32, hs]
        rw [hi] at hst
        step with string_into_bytes_spec' st (by rw [hst]; omega) as ⟨v, hv⟩
        simp only [WP.spec_ok, WP.uncurry'_pair, binRel, okPart, Option.map, binlogValView, Val.ofValue, hv, hst, h2, and_true, hu0, ite_true]
      · simp [hu0] at hno

theorem time2Read_lower (d : Nat) (bs t : List U8) (p : Int) (h : time2Read d bs = some (p, t)) : -2 ^ 63 < p := by
  unfold time2Read at h
  split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, -⟩ := h
  all_goals (try unfold packedMake)
  all_goals omega

theorem deser_MYSQL_TYPE_DATETIME2 (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_DATETIME2 ≤ md.val.length)
    (hp : ∀ e, binlogRead MYSQL_TYPE_DATETIME2 md.val uns buf.val ≠ .panic e) :
    BVdes (MYSQL_TYPE_DATETIME2, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_DATETIME2 md.val uns buf.val) r rest ⦄ := by
  have hm1 : 1 ≤ md.val.length := by simpa [binlogMetaLen] using hmeta
  obtain ⟨m0, t, hmd⟩ : ∃ m0 t, md.val = m0 :: t := by
    rcases h : md.val with _ | ⟨a, t⟩ <;> simp_all
  have hg0 : (md.val.getD 0 (byte 0)) = m0 := by simp [hmd]
  have hc : (UScalar.cast .U32 m0).val = m0.val := by
    rw [UScalar.cast_val_eq]; have := u8_lt m0; simp only [UScalarTy.numBits]; omega
  pre_tac MYSQL_TYPE_DATETIME2
  simp only [index0 md m0 _ hmd, Std.bind_ok]
  simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 1 from by omega, ite_false, hg0] at hp ⊢
  have hlow : ∀ p t, datetime2Read m0.val buf.val = some (p, t) → -2 ^ 63 ≤ p := by
    intro p t ht; rw [ht] at hp; by_contra hc'; exact hp .integerOverflow (by simp only; rw [if_pos (by omega)])
  step with datetime_spec buf (UScalar.cast .U32 m0) (by rw [hc]; exact hlow) as ⟨r, rb, hr⟩
  rw [hc] at hr
  rcases hT : datetime2Read m0.val buf.val with _ | ⟨p, rest⟩
  · rw [hT] at hr
    simp only [Prod.mk.injEq] at hr
    cases r with
    | Ok _ => simp [okPart] at hr
    | Err e => simp [binRel, okPart, hr.2]
  · rw [hT] at hr hp
    simp only [Prod.mk.injEq] at hr
    obtain ⟨h1, h2⟩ := hr
    have hne : ¬ p ≤ -2 ^ 63 := by intro hc'; exact hp .integerOverflow (by simp only; rw [if_pos hc'])
    cases r with
    | Err _ => simp [okPart] at h1
    | Ok pk =>
      simp only [okPart, Option.map, Option.some.injEq] at h1
      simp only [Std.bind_ok]
      step with mysql_common.binlog.misc.datetime_from_packed_spec pk (by omega) as ⟨v, hv⟩
      simp only [hne, ite_false, binRel, okPart, Option.map, binlogValView, hv, h1, h2, and_true]

theorem deser_MYSQL_TYPE_TIME2 (h64 : Target64) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hmeta : binlogMetaLen MYSQL_TYPE_TIME2 ≤ md.val.length) (hb : ¬ binlogBug MYSQL_TYPE_TIME2 md.val uns buf.val) :
    BVdes (MYSQL_TYPE_TIME2, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_TIME2 md.val uns buf.val) r rest ⦄ := by
  have hm1 : 1 ≤ md.val.length := by simpa [binlogMetaLen] using hmeta
  obtain ⟨m0, t, hmd⟩ : ∃ m0 t, md.val = m0 :: t := by
    rcases h : md.val with _ | ⟨a, t⟩ <;> simp_all
  have hg0 : (md.val.getD 0 (byte 0)) = m0 := by simp [hmd]
  have hc : (UScalar.cast .U32 m0).val = m0.val := by
    rw [UScalar.cast_val_eq]; have := u8_lt m0; simp only [UScalarTy.numBits]; omega
  simp only [binlogBug, binlogEffType, hg0] at hb
  pre_tac MYSQL_TYPE_TIME2
  simp only [index0 md m0 _ hmd, Std.bind_ok]
  simp only [binlogRead, binlogEffType, binlogMetaLen, show ¬ md.val.length < 1 from by omega, ite_false, hg0]
  step with time_spec buf (UScalar.cast .U32 m0) (by rw [hc]; exact hb) as ⟨r, rb, hr⟩
  rw [hc] at hr
  rcases hT : time2Read m0.val buf.val with _ | ⟨p, rest⟩
  · rw [hT] at hr
    simp only [Prod.mk.injEq] at hr
    cases r with
    | Ok _ => simp [okPart] at hr
    | Err e => simp [binRel, okPart, hr.2]
  · rw [hT] at hr
    simp only [Prod.mk.injEq] at hr
    obtain ⟨h1, h2⟩ := hr
    have hlo := time2Read_lower _ _ _ _ hT
    cases r with
    | Err _ => simp [okPart] at h1
    | Ok pk =>
      simp only [okPart, Option.map, Option.some.injEq] at h1
      simp only [Std.bind_ok]
      step with mysql_common.binlog.misc.time_from_packed_spec pk (by omega) as ⟨v, hv⟩
      simp only [binRel, okPart, Option.map, binlogValView, hv, h1, h2, and_true]

theorem deser_MYSQL_TYPE_TYPED_ARRAY (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf) (b : U8) (l : List U8)
    (hm : md.val = b :: l) (hcode : (columnTypeOfCode b.val).getD MYSQL_TYPE_TYPED_ARRAY = MYSQL_TYPE_TYPED_ARRAY) :
    BVdes (MYSQL_TYPE_TYPED_ARRAY, md, uns, part) buf ⦃ r rest => binRel (binlogRead MYSQL_TYPE_TYPED_ARRAY md.val uns buf.val) r rest ⦄ := by
  rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
  simp only [Std.uncurry_apply_pair, ct_eq_ta_true, Std.bind_ok, ite_true, index0 md b l hm,
    mysql_common.constants.ColumnType.Insts.CoreConvertTryFromU8UnknownColumnType.try_from_spec]
  have hbr : binlogRead MYSQL_TYPE_TYPED_ARRAY md.val uns buf.val = .err buf.val := by
    rw [hm]; unfold binlogRead; simp only [binlogEffType]; rw [← hm, hcode]; simp [binlogMetaLen]
  rw [hbr]
  rcases h : columnTypeOfCode b.val with _ | x
  · simp only [Std.bind_ok, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TYPED_ARRAY MYSQL_TYPE_STRING = ok false from rfl,
      Bool.false_eq_true, ite_false]
    step with IntAndMisc.io_error_msg_spec as ⟨e⟩
    simp [binRel, okPart]
  · rw [h] at hcode; simp only [Option.getD_some] at hcode; subst hcode
    simp only [Std.bind_ok, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TYPED_ARRAY MYSQL_TYPE_STRING = ok false from rfl,
      Bool.false_eq_true, ite_false]
    step with IntAndMisc.io_error_msg_spec as ⟨e⟩
    simp [binRel, okPart]

theorem deser_rel (h64 : Target64) (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (hne : ¬(ct = MYSQL_TYPE_TYPED_ARRAY ∧ md.val = []))
    (hb : ¬ binlogBug ct md.val uns buf.val) (hp : ∀ e, binlogRead ct md.val uns buf.val ≠ .panic e)
    (hno : binlogRead ct md.val uns buf.val ≠ .opaque) :
    BVdes (ct, md, uns, part) buf ⦃ r rest => binRel (binlogRead ct md.val uns buf.val) r rest ⦄ := by
  have hmeta := meta_of_nopanic ct md.val uns buf.val hne hp
  rw [binlogRead_eff _ _ _ _ hne] at hp hno ⊢
  rw [deser_eff ct md uns part buf hne]
  rw [binlogBug_eff] at hb
  generalize hT : binlogEffType ct md.val = t at *
  cases t
  case MYSQL_TYPE_DECIMAL => exact deser_MYSQL_TYPE_DECIMAL h64 md uns part buf hmeta hb
  case MYSQL_TYPE_NULL => exact deser_MYSQL_TYPE_NULL h64 md uns part buf hmeta hb
  case MYSQL_TYPE_DATE => exact deser_MYSQL_TYPE_DATE h64 md uns part buf hmeta hb
  case MYSQL_TYPE_UNKNOWN => exact deser_MYSQL_TYPE_UNKNOWN h64 md uns part buf hmeta hb
  case MYSQL_TYPE_TINY => exact deser_MYSQL_TYPE_TINY h64 md uns part buf hmeta hb
  case MYSQL_TYPE_SHORT => exact deser_MYSQL_TYPE_SHORT h64 md uns part buf hmeta hb
  case MYSQL_TYPE_LONG => exact deser_MYSQL_TYPE_LONG h64 md uns part buf hmeta hb
  case MYSQL_TYPE_LONGLONG => exact deser_MYSQL_TYPE_LONGLONG h64 md uns part buf hmeta hb
  case MYSQL_TYPE_FLOAT => exact deser_MYSQL_TYPE_FLOAT h64 md uns part buf hmeta hb
  case MYSQL_TYPE_DOUBLE => exact deser_MYSQL_TYPE_DOUBLE h64 md uns part buf hmeta hb
  case MYSQL_TYPE_TIMESTAMP => exact deser_MYSQL_TYPE_TIMESTAMP h64 md uns part buf hmeta hb
  case MYSQL_TYPE_INT24 => exact deser_MYSQL_TYPE_INT24 h64 md uns part buf hmeta hb
  case MYSQL_TYPE_TIME => exact deser_MYSQL_TYPE_TIME h64 md uns part buf hmeta hb
  case MYSQL_TYPE_DATETIME => exact deser_MYSQL_TYPE_DATETIME h64 md uns part buf hmeta hb
  case MYSQL_TYPE_YEAR => exact deser_MYSQL_TYPE_YEAR h64 md uns part buf hmeta hb
  case MYSQL_TYPE_NEWDATE => exact deser_MYSQL_TYPE_NEWDATE h64 md uns part buf hmeta hb
  case MYSQL_TYPE_BIT => exact deser_MYSQL_TYPE_BIT h64 md uns part buf hmeta hb
  case MYSQL_TYPE_TINY_BLOB => exact deser_MYSQL_TYPE_TINY_BLOB h64 md uns part buf hmeta hb
  case MYSQL_TYPE_MEDIUM_BLOB => exact deser_MYSQL_TYPE_MEDIUM_BLOB h64 md uns part buf hmeta hb
  case MYSQL_TYPE_LONG_BLOB => exact deser_MYSQL_TYPE_LONG_BLOB h64 md uns part buf hmeta hb
  case MYSQL_TYPE_BLOB => exact deser_MYSQL_TYPE_BLOB h64 md uns part buf hmeta hb
  case MYSQL_TYPE_GEOMETRY => exact deser_MYSQL_TYPE_GEOMETRY h64 md uns part buf hmeta hb
  case MYSQL_TYPE_VECTOR => exact deser_MYSQL_TYPE_VECTOR h64 md uns part buf hmeta hb
  case MYSQL_TYPE_SET => exact deser_MYSQL_TYPE_SET h64 md uns part buf hmeta hb
  case MYSQL_TYPE_ENUM => exact deser_MYSQL_TYPE_ENUM h64 md uns part buf hmeta hb
  case MYSQL_TYPE_VARCHAR => exact deser_MYSQL_TYPE_VARCHAR h64 md uns part buf hmeta hb
  case MYSQL_TYPE_VAR_STRING => exact deser_MYSQL_TYPE_VAR_STRING h64 md uns part buf hmeta hb
  case MYSQL_TYPE_STRING => exact deser_MYSQL_TYPE_STRING h64 md uns part buf hmeta hb
  case MYSQL_TYPE_TIME2 => exact deser_MYSQL_TYPE_TIME2 h64 md uns part buf hmeta hb
  case MYSQL_TYPE_TIMESTAMP2 => exact deser_MYSQL_TYPE_TIMESTAMP2 h64 md uns part buf hmeta hno
  case MYSQL_TYPE_DATETIME2 => exact deser_MYSQL_TYPE_DATETIME2 h64 md uns part buf hmeta hp
  case MYSQL_TYPE_JSON =>
    exfalso; apply hno; simp [binlogRead, binlogEffType, binlogMetaLen]
  case MYSQL_TYPE_NEWDECIMAL =>
    exfalso; apply hno
    have : ¬ md.val.length < 2 := by simp [binlogMetaLen] at hmeta; omega
    simp only [binlogRead, binlogEffType, binlogMetaLen, this, ite_false]
  case MYSQL_TYPE_TYPED_ARRAY =>
    have hc : ct = MYSQL_TYPE_TYPED_ARRAY := by
      by_contra hc; rw [effType_ne ct md.val hc] at hT; exact hc hT
    subst hc
    rcases hmd : md.val with _ | ⟨b, l⟩
    · exact absurd ⟨rfl, hmd⟩ hne
    · have := deser_MYSQL_TYPE_TYPED_ARRAY md uns part buf b l hmd (by rw [hmd] at hT; exact hT)
      rw [hmd] at this; exact this

theorem ne_ta_nil_of_not_panic (ct : constants.ColumnType) (md : List U8) (uns : Bool) (bs : List U8)
    (h : ∀ e, binlogRead ct md uns bs ≠ .panic e) : ¬(ct = MYSQL_TYPE_TYPED_ARRAY ∧ md = []) := by
  rintro ⟨rfl, rfl⟩; exact h .arrayOutOfBounds rfl

theorem deser_ok (h64 : Target64) (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (v : Val) (rest' : List U8) (hr : binlogRead ct md.val uns buf.val = .ok v rest')
    (hb : ¬ binlogBug ct md.val uns buf.val) :
    BVdes (ct, md, uns, part) buf ⦃ r rest => (okPart r).map binlogValView = some (some v) ∧ rest.val = rest' ⦄ := by
  have hp : ∀ e, binlogRead ct md.val uns buf.val ≠ .panic e := by intro e; rw [hr]; simp
  apply WP.spec_mono (deser_rel h64 ct md uns part buf (ne_ta_nil_of_not_panic _ _ _ _ hp) hb hp (by rw [hr]; simp))
  rintro ⟨r, rest⟩ h
  rw [hr] at h; exact h

theorem bug_not_err (ct : constants.ColumnType) (md : List U8) (uns : Bool) (bs rest' : List U8)
    (hr : binlogRead ct md uns bs = .err rest') : ¬ binlogBug ct md uns bs := by
  intro hb
  by_cases hne : ct = MYSQL_TYPE_TYPED_ARRAY ∧ md = []
  · obtain ⟨rfl, rfl⟩ := hne; simp [binlogBug, binlogEffType] at hb
  rw [binlogRead_eff _ _ _ _ hne] at hr
  unfold binlogBug at hb
  generalize binlogEffType ct md = t at *
  cases t <;> simp only at hb
  case MYSQL_TYPE_INT24 =>
    obtain ⟨-, h3, -⟩ := hb
    simp [binlogRead, binlogEffType, binlogMetaLen, binlogNum, readLE, h3] at hr
  case MYSQL_TYPE_TIME =>
    obtain ⟨h3, -⟩ := hb
    simp [binlogRead, binlogEffType, binlogMetaLen, binlogNum, readLE, h3] at hr
  case MYSQL_TYPE_YEAR =>
    rcases h : bs with _ | ⟨c, l⟩
    · simp [h] at hb
    · simp [h, binlogRead, binlogEffType, binlogMetaLen, binlogNum, readLE] at hr
  case MYSQL_TYPE_TIME2 =>
    obtain ⟨hd, h4, -⟩ := hb
    have hfb : fracBytes (md.getD 0 (byte 0)).val = 1 := by unfold fracBytes; rw [if_pos hd]
    have : time2Read ((md.getD 0 (byte 0)).val) bs ≠ none := by
      unfold time2Read; rw [if_neg (by rw [hfb]; omega)]; simp
    unfold binlogRead at hr
    simp only [binlogEffType, binlogMetaLen] at hr
    by_cases hml : md.length < 1
    · simp only [hml, ite_true] at hr; simp at hr
    · simp only [hml, ite_false] at hr
      revert hr this; cases time2Read ((md.getD 0 (byte 0)).val) bs <;> simp

theorem deser_err (h64 : Target64) (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (rest' : List U8) (hr : binlogRead ct md.val uns buf.val = .err rest') :
    BVdes (ct, md, uns, part) buf ⦃ r rest => okPart r = none ∧ rest.val = rest' ⦄ := by
  have hp : ∀ e, binlogRead ct md.val uns buf.val ≠ .panic e := by intro e; rw [hr]; simp
  apply WP.spec_mono (deser_rel h64 ct md uns part buf (ne_ta_nil_of_not_panic _ _ _ _ hp)
    (bug_not_err _ _ _ _ _ hr) hp (by rw [hr]; simp))
  rintro ⟨r, rest⟩ h
  rw [hr] at h; exact h

theorem deser_roundtrip (h64 : Target64) (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (v : Val) (bs tail : List U8) (he : binlogEnc ct md.val uns v = some bs)
    (hb : ¬ binlogEncBug ct md.val uns v) (h : buf.val = bs ++ tail) :
    BVdes (ct, md, uns, part) buf ⦃ r rest => (okPart r).map binlogValView = some (some v) ∧ rest.val = tail ⦄ := by
  have hr := binlogRead_binlogEnc' ct md.val uns v bs tail he
  have hnb := not_binlogBug_of_binlogEnc' ct md.val uns v bs tail he hb
  rw [← h] at hr hnb
  exact deser_ok h64 ct md uns part buf v tail hr hnb

theorem index_fail (md : Slice U8) (i : Usize) (h : md.val.length ≤ i.val) :
    Slice.index_usize md i = fail .arrayOutOfBounds := by
  unfold Slice.index_usize
  have : md[i]? = none := by
    simp [Slice.length] at *
    omega
  rw [this]

theorem deser_meta_panic (t : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (ht : t ≠ MYSQL_TYPE_TYPED_ARRAY) (hlt : md.val.length < binlogMetaLen t) :
    BVdes (t, md, uns, part) buf = fail (binlogMetaPanic t md.val) := by
  cases t <;> simp only [binlogMetaLen, Nat.not_lt_zero] at hlt
  case MYSQL_TYPE_BIT =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_BIT MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_BIT MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_BIT MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_BIT MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_NEWDECIMAL =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_NEWDECIMAL MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_NEWDECIMAL MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_NEWDECIMAL MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_NEWDECIMAL MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_ENUM =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_ENUM MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_ENUM MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_ENUM MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_ENUM MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_SET =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_SET MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_SET MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_SET MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_SET MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_VARCHAR =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_VARCHAR MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_VARCHAR MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_VARCHAR MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_VARCHAR MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_VAR_STRING =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_VAR_STRING MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_VAR_STRING MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_VAR_STRING MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_VAR_STRING MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_TIMESTAMP2 =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TIMESTAMP2 MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TIMESTAMP2 MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TIMESTAMP2 MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TIMESTAMP2 MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_DATETIME2 =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_DATETIME2 MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_DATETIME2 MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_DATETIME2 MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_DATETIME2 MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_TIME2 =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TIME2 MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TIME2 MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TIME2 MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TIME2 MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_TINY_BLOB =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TINY_BLOB MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TINY_BLOB MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TINY_BLOB MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_TINY_BLOB MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_MEDIUM_BLOB =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_MEDIUM_BLOB MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_MEDIUM_BLOB MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_MEDIUM_BLOB MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_MEDIUM_BLOB MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_LONG_BLOB =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_LONG_BLOB MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_LONG_BLOB MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_LONG_BLOB MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_LONG_BLOB MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_BLOB =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_BLOB MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_BLOB MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_BLOB MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_BLOB MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_GEOMETRY =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_GEOMETRY MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_GEOMETRY MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_GEOMETRY MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_GEOMETRY MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_VECTOR =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_VECTOR MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_VECTOR MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 0#usize (by simp [hmd]), index_fail md 1#usize (by simp [hmd])]
    · simp [hmd] at hlt
      all_goals simp [Std.uncurry_apply_pair, binlogMetaPanic, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_VECTOR MYSQL_TYPE_TYPED_ARRAY = ok false from rfl, show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_VECTOR MYSQL_TYPE_STRING = ok false from rfl, lift, index_fail md 1#usize (by simp [hmd]), index0 md a _ hmd]
    · simp [hmd] at hlt
  case MYSQL_TYPE_STRING =>
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    rcases hmd : md.val with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [Std.uncurry_apply_pair, binlogMetaPanic, lift, index_fail md 0#usize (by simp [hmd]),
        show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_STRING MYSQL_TYPE_TYPED_ARRAY = ok false from rfl,
        show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_STRING MYSQL_TYPE_STRING = ok true from rfl]
    · simp only [Std.uncurry_apply_pair, lift, index0 md a _ hmd, Std.bind_ok,
        show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_STRING MYSQL_TYPE_TYPED_ARRAY = ok false from rfl,
        show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_STRING MYSQL_TYPE_STRING = ok true from rfl, Bool.false_eq_true, ite_false, ite_true]
      by_cases h0 : a ≥ 1#u8
      · have : a.val ≠ 0 := by scalar_tac
        simp [h0, index_fail md 1#usize (by simp [hmd]), binlogMetaPanic, this]
      · have : a.val = 0 := by scalar_tac
        simp only [h0, ite_false, binlogMetaPanic, this, ite_true]
        rw [io.ParseBuf.eat_u16_le_panics md (by simp [Slice.length, hmd])]
        simp
    · simp [hmd] at hlt

theorem deser_panics (ct : constants.ColumnType) (md : Slice U8) (uns part : Bool) (buf : io.ParseBuf)
    (e : Error) (hr : binlogRead ct md.val uns buf.val = .panic e) :
    BVdes (ct, md, uns, part) buf = fail e := by
  by_cases hne : ct = MYSQL_TYPE_TYPED_ARRAY ∧ md.val = []
  · obtain ⟨rfl, hmd⟩ := hne
    have he : e = .arrayOutOfBounds := by
      unfold binlogRead at hr; rw [hmd] at hr; simp only [BinlogOut.panic.injEq] at hr; exact hr.symm
    subst he
    rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
    simp [Std.uncurry_apply_pair, ct_eq_ta_true, index_fail md 0#usize (by simp [hmd])]
  · have hid := effType_idem ct md.val
    rw [binlogRead_eff _ _ _ _ hne] at hr
    rw [deser_eff ct md uns part buf hne]
    generalize hT : binlogEffType ct md.val = t at *
    have hne' : ¬(t = MYSQL_TYPE_TYPED_ARRAY ∧ md.val = []) := by
      rintro ⟨h1, h2⟩; apply hne; refine ⟨?_, h2⟩; rw [h2] at hT; cases ct <;> simp_all [binlogEffType]
    by_cases hlt : md.val.length < binlogMetaLen t
    · have ht : t ≠ MYSQL_TYPE_TYPED_ARRAY := by intro h; subst h; simp [binlogMetaLen] at hlt
      have he : binlogRead t md.val uns buf.val = .panic (binlogMetaPanic t md.val) := by
        unfold binlogRead
        split
        · exact absurd ⟨rfl, by assumption⟩ hne'
        · simp only [hid, hlt, ite_true]
      rw [he] at hr
      simp only [BinlogOut.panic.injEq] at hr
      subst hr
      exact deser_meta_panic t md uns part buf ht hlt
    cases t
    case MYSQL_TYPE_TYPED_ARRAY =>
      exfalso
      rcases hmd : md.val with _ | ⟨b, l⟩
      · exact hne' ⟨rfl, hmd⟩
      · rw [hmd] at hr hid
        unfold binlogRead at hr
        simp only [hid, binlogMetaLen, Nat.not_lt_zero, ite_false] at hr
        simp at hr
    case MYSQL_TYPE_DATETIME2 =>
      have hm1 : 1 ≤ md.val.length := by simp only [binlogMetaLen] at hlt; omega
      obtain ⟨m0, l, hmd⟩ : ∃ m0 l, md.val = m0 :: l := by
        rcases h : md.val with _ | ⟨a, l⟩ <;> simp_all
      have hg0 : (md.val.getD 0 (byte 0)) = m0 := by simp [hmd]
      have hc : (UScalar.cast .U32 m0).val = m0.val := by
        rw [UScalar.cast_val_eq]; have := u8_lt m0; simp only [UScalarTy.numBits]; omega
      unfold binlogRead at hr
      simp only [binlogEffType, hlt, ite_false, hg0] at hr
      rcases hT2 : datetime2Read m0.val buf.val with _ | ⟨p, rest⟩
      · rw [hT2] at hr; simp at hr
      · rw [hT2] at hr
        by_cases hp : p ≤ -2 ^ 63
        · simp only [hp, ite_true, BinlogOut.panic.injEq] at hr
          subst hr
          rw [binlog.value.BinlogValue.Insts.Mysql_commonProtoMyDeserializeDeTupleColumnTypeSharedDeSliceU8BoolBool.deserialize]
          simp only [Std.uncurry_apply_pair,
            show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_DATETIME2 MYSQL_TYPE_TYPED_ARRAY = ok false from rfl,
            show constants.ColumnType.Insts.CoreCmpPartialEqColumnType.eq MYSQL_TYPE_DATETIME2 MYSQL_TYPE_STRING = ok false from rfl,
            Std.bind_ok, Bool.false_eq_true, ite_false, lift, index0 md m0 _ hmd]
          by_cases hlt2 : p < -2 ^ 63
          · rw [datetime_overflow buf (UScalar.cast .U32 m0) ⟨p, rest, by rw [hc]; exact hT2, hlt2⟩]
            simp
          · have heq : p = -2 ^ 63 := by omega
            obtain ⟨⟨r, rb⟩, he, hr2⟩ := PBUtil.spec_eq_ok (datetime_spec buf (UScalar.cast .U32 m0)
              (by intro p' t' ht'; rw [hc, hT2] at ht'; simp at ht'; omega))
            rw [hc, hT2] at hr2
            simp only [Prod.mk.injEq] at hr2
            obtain ⟨h1, -⟩ := hr2
            cases r with
            | Err _ => simp [okPart] at h1
            | Ok pk =>
              simp only [okPart, Option.map, Option.some.injEq] at h1
              rw [he]
              simp only [Std.bind_ok, Std.uncurry_apply_pair]
              rw [mysql_common.binlog.misc.datetime_from_packed_min pk (by omega)]
              simp
        · simp only [hp, ite_false] at hr; simp at hr
    all_goals
      unfold binlogRead at hr
      simp only [binlogEffType, hlt, ite_false] at hr
      first
        | (simp at hr; done)
        | (revert hr; simp [BinlogOut.ofRead, binlogNum, binlogTake, binlogStr]; done)
        | (revert hr; simp [BinlogOut.ofRead, binlogNum, binlogTake, binlogStr]; (repeat' split) <;> simp; done)

end mysql_common.BinlogUtil
