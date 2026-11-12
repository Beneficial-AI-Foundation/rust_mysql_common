import Defs

/-! Statements for `impl SeqRepr for LeU32` (spec file: `Specs/Misc/Raw/Seq.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `LeU32::MAX_LEN`: `u32::MAX`. -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN_spec :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN ⦃ m => m.val = 2 ^ 32 - 1 ⦄ := by
  sorry

/-- `LeU32::SIZE` is `None`. -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.SIZE_eq :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.SIZE = none := by
  sorry

/-- `LeU32::serialize`: appends the item count (at most `MAX_LEN`) as a 4-byte little-endian integer, then the serializations of the first that many items: a longer sequence is silently truncated. -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize_spec {T : Type} (ser : proto.MySerialize T) (enc : T → List U8)
    (hser : ∀ (x : T) (b : alloc.vec.Vec U8), b.length + (enc x).length ≤ Usize.max →
      ser.serialize x b ⦃ b' => b'.val = b.val ++ enc x ⦄)
    (seq : Slice T) (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 + (seq.val.flatMap enc).length ≤ Usize.max) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize ser seq buf ⦃ buf' =>
      buf'.val = buf.val ++ leBytes 4 (min seq.length (2 ^ 32 - 1)) ++ (seq.val.take (2 ^ 32 - 1)).flatMap enc ⦄ := by
  sorry

/-- `LeU32::deserialize`: reads back a 4-byte count followed by that many serialized items (hypotheses as for `Unknown`). -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_roundtrip {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (xs : List T) (enc : T → List U8)
    (hde : ∀ (x : T) (tail : List U8) (b : io.ParseBuf), b.val = enc x ++ tail →
      io.ParseBuf.parse de b () ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o)
    (hfix : ∀ c, o = some c → (∀ x, (enc x).length = c.val) ∧ c.val * xs.length ≤ Usize.max)
    (hlen : xs.length ≤ (2 ^ 32 - 1)) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 4 xs.length ++ xs.flatMap enc ++ tail) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize cl de () buf ⦃ r rest => (okPart r).map cowList = some xs ∧ rest.val = tail ⦄ := by
  sorry

/-- `LeU32::deserialize` does not panic if the item parser does not, provided `SIZE * count`
    does not overflow, where `count` is the length prefix read from the (untrusted) input.
    **Crash path.** The count comes from the wire, up to `u32::MAX`. For a fixed-size item the
    unchecked product `SIZE * count` overflows for a large count (a panic in a debug build, a
    wrap-around in release); and before that, `Vec::with_capacity(count)` (modelled as free) asks
    for `count * size_of::<T>()` bytes, which aborts the process for a large count. Both are
    reachable from a malicious server. -/
theorem misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_no_panic {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (hde : ∀ b : io.ParseBuf, io.ParseBuf.parse de b () ⦃ _ => True ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o) (h64 : Target64) (buf : io.ParseBuf)
    (hov : ∀ c, o = some c → c.val * leNat (buf.val.take 4) ≤ Usize.max) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize cl de () buf ⦃ _ => True ⦄ := by
  sorry

end mysql_common
