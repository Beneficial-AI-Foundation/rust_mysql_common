import Defs

/-! Statements for `impl SeqRepr for Unknown` (spec file: `Specs/Misc/Raw/Seq.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `Unknown::MAX_LEN`: `usize::MAX`. -/
theorem misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.MAX_LEN_spec :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.MAX_LEN.val = Usize.max := by
  sorry

/-- `Unknown::SIZE` is `None`. -/
theorem misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.SIZE_eq :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.SIZE = none := by
  sorry

/-- `Unknown::serialize`: appends the items' serializations, nothing else (the count is stored elsewhere). Stated given what the item serializer appends (`enc`). -/
theorem misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.serialize_spec {T : Type} (ser : proto.MySerialize T) (enc : T → List U8)
    (hser : ∀ (x : T) (b : alloc.vec.Vec U8), b.length + (enc x).length ≤ Usize.max →
      ser.serialize x b ⦃ b' => b'.val = b.val ++ enc x ⦄)
    (seq : Slice T) (buf : alloc.vec.Vec U8)
    (h : buf.length + (seq.val.flatMap enc).length ≤ Usize.max) :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.serialize ser seq buf ⦃ buf' => buf'.val = buf.val ++ seq.val.flatMap enc ⦄ := by
  sorry

/-- `Unknown::deserialize(len)`: reads back `len` serialized items. Stated given that the item
    parser reads back each item's serialization `enc x`, and, if items have a fixed `SIZE`, that
    every `enc x` has that size and `SIZE * len` does not overflow (it is computed unchecked). -/
theorem misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize_roundtrip {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (xs : List T) (enc : T → List U8)
    (hde : ∀ x ∈ xs, ∀ (tail : List U8) (b : io.ParseBuf), b.val = enc x ++ tail →
      io.ParseBuf.parse de b () ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o)
    (hfix : ∀ c, o = some c → (∀ x ∈ xs, (enc x).length = c.val) ∧ c.val * xs.length ≤ Usize.max)
    (len : Usize) (hlen : len.val = xs.length) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = xs.flatMap enc ++ tail) :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize cl de len buf ⦃ r rest => (okPart r).map cowList = some xs ∧ rest.val = tail ⦄ := by
  sorry

/-- `Unknown::deserialize(len)` does not panic if the item parser does not, provided
    `SIZE * len` does not overflow for a fixed-size item. **Caveats.** (1) `Vec::with_capacity(len)`
    is modelled as free: real Rust panics (capacity overflow) when `len * size_of::<T>()` exceeds
    `isize::MAX`, and aborts the process when the allocation fails (OOM). (2) The product `SIZE * len` is a plain `usize` multiplication: it panics on overflow
    in a debug build (as in the Lean model) and wraps in a release build. -/
theorem misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize_no_panic {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (hde : ∀ b : io.ParseBuf, io.ParseBuf.parse de b () ⦃ _ => True ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o)
    (len : Usize) (hov : ∀ c, o = some c → c.val * len.val ≤ Usize.max) (buf : io.ParseBuf) :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize cl de len buf ⦃ _ => True ⦄ := by
  sorry

end mysql_common
