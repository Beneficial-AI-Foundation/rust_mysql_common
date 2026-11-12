import Defs

/-! Statements for `impl SeqRepr for LeU64` (spec file: `Specs/Misc/Raw/Seq.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `LeU64::MAX_LEN`: `u64::MAX as usize` (= `usize::MAX` on the 64-bit target). -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN_spec (h64 : Target64) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN ⦃ m => m.val = 2 ^ 64 - 1 ⦄ := by
  sorry

/-- `LeU64::SIZE` is `None`. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.SIZE_eq :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.SIZE = none := by
  sorry

/-- `LeU64::serialize`: appends the item count (at most `MAX_LEN`) as a 8-byte little-endian integer, then the serializations of the first that many items: a longer sequence is silently truncated. -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize_spec {T : Type} (ser : proto.MySerialize T) (enc : T → List U8)
    (hser : ∀ (x : T) (b : alloc.vec.Vec U8), b.length + (enc x).length ≤ Usize.max →
      ser.serialize x b ⦃ b' => b'.val = b.val ++ enc x ⦄)
    (seq : Slice T) (buf : alloc.vec.Vec U8)
    (h : buf.length + 8 + (seq.val.flatMap enc).length ≤ Usize.max) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize ser seq buf ⦃ buf' =>
      buf'.val = buf.val ++ leBytes 8 (min seq.length (2 ^ 64 - 1)) ++ (seq.val.take (2 ^ 64 - 1)).flatMap enc ⦄ := by
  sorry

/-- `LeU64::deserialize`: reads back a 8-byte count followed by that many serialized items (hypotheses as for `Unknown`). -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_roundtrip {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (xs : List T) (enc : T → List U8)
    (hde : ∀ x ∈ xs, ∀ (tail : List U8) (b : io.ParseBuf), b.val = enc x ++ tail →
      io.ParseBuf.parse de b () ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o)
    (hfix : ∀ c, o = some c → (∀ x ∈ xs, (enc x).length = c.val) ∧ c.val * xs.length ≤ Usize.max)
    (hlen : xs.length ≤ Usize.max) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 8 xs.length ++ xs.flatMap enc ++ tail) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize cl de () buf ⦃ r rest => (okPart r).map cowList = some xs ∧ rest.val = tail ⦄ := by
  sorry

/-- `LeU64::deserialize` does not panic if the item parser does not, provided `SIZE * count`
    does not overflow, where `count` is the length prefix read from the (untrusted) input.
    **Crash path.** The count comes from the wire, up to `u64::MAX`. For a fixed-size item the
    unchecked product `SIZE * count` overflows for a large count (a panic in a debug build, a
    wrap-around in release); and before that, `Vec::with_capacity(count)` (modelled as free) asks
    for `count * size_of::<T>()` bytes: Rust panics (capacity overflow) if that exceeds
    `isize::MAX` and aborts the process if the allocation fails (OOM). Both are reachable from a
    malicious server. (On a 32-bit `usize` the count is truncated by `as usize`; `hov` bounds the
    untruncated count, so no `Target64` is needed.) -/
theorem misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_no_panic {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (hde : ∀ b : io.ParseBuf, io.ParseBuf.parse de b () ⦃ _ => True ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o) (buf : io.ParseBuf)
    (hov : ∀ c, o = some c → c.val * leNat (buf.val.take 8) ≤ Usize.max) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize cl de () buf ⦃ _ => True ⦄ := by
  sorry

end mysql_common
