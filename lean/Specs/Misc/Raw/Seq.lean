import Proofs.Misc.Raw.Seq.Seq
import Proofs.Misc.Raw.Seq.Unknown
import Proofs.Misc.Raw.Seq.LeU64
import Proofs.Misc.Raw.Seq.LeU32
import Proofs.Misc.Raw.Seq.RawSeq

/-!
# `src/misc/raw/seq.rs`
    Sequences of serialized values (`Seq<T, U>`, with the count stored as `U`: `Unknown`, `LeU32`,
    `LeU64`) and raw byte sequences (`RawSeq<T, U>`).

    **Configuration.** As in `Specs/Io.lean`.

    **Definitions used.** `Defs/Bytes.lean` (`cowList`, `okPart`, `leBytes`, `leNat`, `Target64`).

    **Reading the statements.** The item type is generic: the `SeqRepr` statements take what the item
    serializer appends (`enc`) and that the item parser reads it back as hypotheses, and conclude the
    round trip for the sequence (the hypotheses only concern the items of the sequence, so lossy item
    types such as `RawInt<LeU24>` qualify for sequences of in-range items); a separate statement gives absence of panics from absence of panics
    of the item parser.

    **Not covered.** `Seq::empty`, `is_empty`, `len`, `push`, `into_owned`, `Default` (not in the
    translation's `start_from`); `Debug`.

    **Behaviour to note.** Deserializing a sequence trusts the count it reads: see the crash path on
    `deserialize_no_panic` for `LeU64`/`LeU32` (allocation of `count` items; unchecked `SIZE * count`).
    `LeU32::serialize`/`LeU64::serialize` silently truncate longer sequences.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-! ### `struct Seq and its impls` -/

/-- `Deref for Seq`: the items. -/
recall misc.raw.seq.Seq.Insts.CoreOpsDerefDerefSlice.deref_spec {T U : Type} (cl : core.clone.Clone T)
    (self : misc.raw.seq.Seq T U) :
    misc.raw.seq.Seq.Insts.CoreOpsDerefDerefSlice.deref cl self ⦃ s => s.val = cowList self.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.Seq.Insts.CoreOpsDerefDerefSlice.deref_spec`

/-- `Seq::new(s)`: wraps `s.into()`. -/
recall misc.raw.seq.Seq.new_eq {T T3 : Type} (U : Type) (cl : core.clone.Clone T)
    (into : core.convert.Into T3 (alloc.borrow.Cow (Slice T) (alloc.vec.Vec T))) (s : T3) (c : alloc.borrow.Cow (Slice T) (alloc.vec.Vec T)) (h : into.into s = ok c) :
    misc.raw.seq.Seq.new U cl into s = ok (c, ())

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.Seq.new_eq`

/-- `MySerialize for Seq<T, U>`: `U::serialize` of the items; whatever that guarantees carries over. -/
recall misc.raw.seq.Seq.Insts.Mysql_commonProtoMySerialize.serialize_spec {T U Ctx : Type} (cl : core.clone.Clone T) (ser : proto.MySerialize T)
    (repr : misc.raw.seq.SeqRepr U Ctx) (self : misc.raw.seq.Seq T U) (buf : alloc.vec.Vec U8)
    (P : alloc.vec.Vec U8 → Prop)
    (h : ∀ s : Slice T, s.val = cowList self.1 → repr.serialize ser s buf ⦃ P ⦄) :
    misc.raw.seq.Seq.Insts.Mysql_commonProtoMySerialize.serialize cl ser repr self buf ⦃ P ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.Seq.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- `MyDeserialize for Seq<T, U>`: `SIZE` is `None`. -/
recall misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq {T U Ctx : Type} (cl : core.clone.Clone T) (de : proto.MyDeserialize T Unit)
    (repr : misc.raw.seq.SeqRepr U Ctx) :
    misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.SIZE cl de repr = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.SIZE_eq`

/-- `MyDeserialize for Seq<T, U>`: `U::deserialize`, wrapped; whatever it guarantees carries over. -/
recall misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec {T U Ctx : Type} (cl : core.clone.Clone T) (de : proto.MyDeserialize T Unit)
    (repr : misc.raw.seq.SeqRepr U Ctx) (ctx : Ctx) (buf : io.ParseBuf)
    (Q : Option (List T) → io.ParseBuf → Prop)
    (h : repr.deserialize cl de ctx buf ⦃ r rest => Q ((okPart r).map cowList) rest ⦄) :
    misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.deserialize cl de repr ctx buf ⦃ r rest => Q ((okPart r).map (fun s => cowList s.1)) rest ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.Seq.Insts.Mysql_commonProtoMyDeserialize.deserialize_spec`

/-! ### `impl SeqRepr for Unknown` -/

/-- `Unknown::MAX_LEN`: `usize::MAX`. -/
recall misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.MAX_LEN_spec :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.MAX_LEN.val = Usize.max

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.MAX_LEN_spec`

/-- `Unknown::SIZE` is `None`. -/
recall misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.SIZE_eq :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.SIZE_eq`

/-- `Unknown::serialize`: appends the items' serializations, nothing else (the count is stored elsewhere). Stated given what the item serializer appends (`enc`). -/
recall misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.serialize_spec {T : Type} (ser : proto.MySerialize T) (enc : T → List U8)
    (hser : ∀ (x : T) (b : alloc.vec.Vec U8), b.length + (enc x).length ≤ Usize.max →
      ser.serialize x b ⦃ b' => b'.val = b.val ++ enc x ⦄)
    (seq : Slice T) (buf : alloc.vec.Vec U8)
    (h : buf.length + (seq.val.flatMap enc).length ≤ Usize.max) :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.serialize ser seq buf ⦃ buf' => buf'.val = buf.val ++ seq.val.flatMap enc ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.serialize_spec`

/-- `Unknown::deserialize(len)`: reads back `len` serialized items. Stated given that the item
    parser reads back each item's serialization `enc x`, and, if items have a fixed `SIZE`, that
    every `enc x` has that size and `SIZE * len` does not overflow (it is computed unchecked). -/
recall misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize_roundtrip {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (xs : List T) (enc : T → List U8)
    (hde : ∀ x ∈ xs, ∀ (tail : List U8) (b : io.ParseBuf), b.val = enc x ++ tail →
      io.ParseBuf.parse de b () ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o)
    (hfix : ∀ c, o = some c → (∀ x ∈ xs, (enc x).length = c.val) ∧ c.val * xs.length ≤ Usize.max)
    (len : Usize) (hlen : len.val = xs.length) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = xs.flatMap enc ++ tail) :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize cl de len buf ⦃ r rest => (okPart r).map cowList = some xs ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize_roundtrip`

/-- `Unknown::deserialize(len)` does not panic if the item parser does not, provided
    `SIZE * len` does not overflow for a fixed-size item. **Caveats.** (1) `Vec::with_capacity(len)`
    is modelled as free: real Rust panics (capacity overflow) when `len * size_of::<T>()` exceeds
    `isize::MAX`, and aborts the process when the allocation fails (OOM). (2) The product `SIZE * len` is a plain `usize` multiplication: it panics on overflow
    in a debug build (as in the Lean model) and wraps in a release build. -/
recall misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize_no_panic {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (hde : ∀ b : io.ParseBuf, io.ParseBuf.parse de b () ⦃ _ => True ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o)
    (len : Usize) (hov : ∀ c, o = some c → c.val * len.val ≤ Usize.max) (buf : io.ParseBuf) :
    misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize cl de len buf ⦃ _ => True ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.Unknown.Insts.Mysql_commonMiscRawSeqSeqReprUsize.deserialize_no_panic`

/-! ### `impl SeqRepr for LeU64` -/

/-- `LeU64::MAX_LEN`: `u64::MAX as usize` (= `usize::MAX` on the 64-bit target). -/
recall misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN_spec (h64 : Target64) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN ⦃ m => m.val = 2 ^ 64 - 1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN_spec`

/-- `LeU64::SIZE` is `None`. -/
recall misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.SIZE_eq :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.SIZE_eq`

/-- `LeU64::serialize`: appends the item count (at most `MAX_LEN`) as a 8-byte little-endian integer, then the serializations of the first that many items: a longer sequence is silently truncated. -/
recall misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize_spec {T : Type} (ser : proto.MySerialize T) (enc : T → List U8)
    (hser : ∀ (x : T) (b : alloc.vec.Vec U8), b.length + (enc x).length ≤ Usize.max →
      ser.serialize x b ⦃ b' => b'.val = b.val ++ enc x ⦄)
    (seq : Slice T) (buf : alloc.vec.Vec U8)
    (h : buf.length + 8 + (seq.val.flatMap enc).length ≤ Usize.max) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize ser seq buf ⦃ buf' =>
      buf'.val = buf.val ++ leBytes 8 (min seq.length (2 ^ 64 - 1)) ++ (seq.val.take (2 ^ 64 - 1)).flatMap enc ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize_spec`

/-- `LeU64::deserialize`: reads back a 8-byte count followed by that many serialized items (hypotheses as for `Unknown`). -/
recall misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_roundtrip {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (xs : List T) (enc : T → List U8)
    (hde : ∀ x ∈ xs, ∀ (tail : List U8) (b : io.ParseBuf), b.val = enc x ++ tail →
      io.ParseBuf.parse de b () ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o)
    (hfix : ∀ c, o = some c → (∀ x ∈ xs, (enc x).length = c.val) ∧ c.val * xs.length ≤ Usize.max)
    (hlen : xs.length ≤ Usize.max) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 8 xs.length ++ xs.flatMap enc ++ tail) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize cl de () buf ⦃ r rest => (okPart r).map cowList = some xs ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_roundtrip`

/-- `LeU64::deserialize` does not panic if the item parser does not, provided `SIZE * count`
    does not overflow, where `count` is the length prefix read from the (untrusted) input.
    **Crash path.** The count comes from the wire, up to `u64::MAX`. For a fixed-size item the
    unchecked product `SIZE * count` overflows for a large count (a panic in a debug build, a
    wrap-around in release); and before that, `Vec::with_capacity(count)` (modelled as free) asks
    for `count * size_of::<T>()` bytes: Rust panics (capacity overflow) if that exceeds
    `isize::MAX` and aborts the process if the allocation fails (OOM). Both are reachable from a
    malicious server. (On a 32-bit `usize` the count is truncated by `as usize`; `hov` bounds the
    untruncated count, so no `Target64` is needed.) -/
recall misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_no_panic {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (hde : ∀ b : io.ParseBuf, io.ParseBuf.parse de b () ⦃ _ => True ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o) (buf : io.ParseBuf)
    (hov : ∀ c, o = some c → c.val * leNat (buf.val.take 8) ≤ Usize.max) :
    misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize cl de () buf ⦃ _ => True ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU64.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_no_panic`

/-! ### `impl SeqRepr for LeU32` -/

/-- `LeU32::MAX_LEN`: `u32::MAX`. -/
recall misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN_spec :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN ⦃ m => m.val = 2 ^ 32 - 1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.MAX_LEN_spec`

/-- `LeU32::SIZE` is `None`. -/
recall misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.SIZE_eq :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.SIZE = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.SIZE_eq`

/-- `LeU32::serialize`: appends the item count (at most `MAX_LEN`) as a 4-byte little-endian integer, then the serializations of the first that many items: a longer sequence is silently truncated. -/
recall misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize_spec {T : Type} (ser : proto.MySerialize T) (enc : T → List U8)
    (hser : ∀ (x : T) (b : alloc.vec.Vec U8), b.length + (enc x).length ≤ Usize.max →
      ser.serialize x b ⦃ b' => b'.val = b.val ++ enc x ⦄)
    (seq : Slice T) (buf : alloc.vec.Vec U8)
    (h : buf.length + 4 + (seq.val.flatMap enc).length ≤ Usize.max) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize ser seq buf ⦃ buf' =>
      buf'.val = buf.val ++ leBytes 4 (min seq.length (2 ^ 32 - 1)) ++ (seq.val.take (2 ^ 32 - 1)).flatMap enc ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.serialize_spec`

/-- `LeU32::deserialize`: reads back a 4-byte count followed by that many serialized items (hypotheses as for `Unknown`). -/
recall misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_roundtrip {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (xs : List T) (enc : T → List U8)
    (hde : ∀ x ∈ xs, ∀ (tail : List U8) (b : io.ParseBuf), b.val = enc x ++ tail →
      io.ParseBuf.parse de b () ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o)
    (hfix : ∀ c, o = some c → (∀ x ∈ xs, (enc x).length = c.val) ∧ c.val * xs.length ≤ Usize.max)
    (hlen : xs.length ≤ (2 ^ 32 - 1)) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = leBytes 4 xs.length ++ xs.flatMap enc ++ tail) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize cl de () buf ⦃ r rest => (okPart r).map cowList = some xs ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_roundtrip`

/-- `LeU32::deserialize` does not panic if the item parser does not, provided `SIZE * count`
    does not overflow, where `count` is the length prefix read from the (untrusted) input.
    **Crash path.** The count comes from the wire, up to `u32::MAX`. For a fixed-size item the
    unchecked product `SIZE * count` overflows for a large count (a panic in a debug build, a
    wrap-around in release); and before that, `Vec::with_capacity(count)` (modelled as free) asks
    for `count * size_of::<T>()` bytes: Rust panics (capacity overflow) if that exceeds
    `isize::MAX` and aborts the process if the allocation fails (OOM). Both are reachable from a
    malicious server. (On a 32-bit `usize` the count is truncated by `as usize`; `hov` bounds the
    untruncated count, so no `Target64` is needed.) -/
recall misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_no_panic {T : Type} (cl : core.clone.Clone T)
    (de : proto.MyDeserialize T Unit) (hde : ∀ b : io.ParseBuf, io.ParseBuf.parse de b () ⦃ _ => True ⦄)
    (o : Option Usize) (hsz : de.SIZE = ok o) (buf : io.ParseBuf)
    (hov : ∀ c, o = some c → c.val * leNat (buf.val.take 4) ≤ Usize.max) :
    misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize cl de () buf ⦃ _ => True ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.int.LeU32.Insts.Mysql_commonMiscRawSeqSeqReprTuple.deserialize_no_panic`

/-! ### `struct RawSeq and its impls` -/

/-- `RawSeq::new(t)`: wraps `t.into()`. -/
recall misc.raw.seq.RawSeq.new_eq {T T3 P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P)
    (into : core.convert.Into T3 (alloc.borrow.Cow (Slice P) (alloc.vec.Vec P))) (t : T3)
    (c : alloc.borrow.Cow (Slice P) (alloc.vec.Vec P)) (h : into.into t = ok c) :
    misc.raw.seq.RawSeq.new U inst into t = ok (c, ())

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.RawSeq.new_eq`

/-- `len`: the number of items. -/
recall misc.raw.seq.RawSeq.len_spec {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw.seq.RawSeq T U P) :
    misc.raw.seq.RawSeq.len inst self ⦃ n => n.val = (cowList self.1).length ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.RawSeq.len_spec`

/-- `is_empty`: whether there are no items. -/
recall misc.raw.seq.RawSeq.is_empty_spec {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw.seq.RawSeq T U P) :
    misc.raw.seq.RawSeq.is_empty inst self ⦃ b => (b ↔ cowList self.1 = []) ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.RawSeq.is_empty_spec`

/-- `into_owned`: the same items, owned. Assumes the primitive's `Clone` is the identity
    (`hcl`): a borrowed sequence is copied element by element with `Clone::clone`, which Rust does
    not force to agree with `Copy` (it does for every primitive integer type the crate uses).
    Added after proof found the unconditional statement false for an arbitrary `Clone` instance. -/
recall misc.raw.seq.RawSeq.into_owned_spec {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (hcl : ∀ x, inst.coremarkerCopyInst.cloneInst.clone x = ok x)
    (self : misc.raw.seq.RawSeq T U P) :
    misc.raw.seq.RawSeq.into_owned inst self ⦃ r =>
      cowList r.1 = cowList self.1 ∧ ∃ v, r.1 = alloc.borrow.Cow.Owned v ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.RawSeq.into_owned_spec`

/-- `get(index)`: the item at `index` as a `RawConst`, `None` out of range. -/
recall misc.raw.seq.RawSeq.get_spec {T U P E : Type} (inst : misc.raw.int.IntRepr T P)
    (cp : core.marker.Copy T) (tf : core.convert.TryFrom U P E)
    (self : misc.raw.seq.RawSeq T U P) (index : Usize) :
    misc.raw.seq.RawSeq.get inst cp tf self index ⦃ o => o.map (·.1) = (cowList self.1)[index.val]? ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.RawSeq.get_spec`

/-- `MyDeserialize for RawSeq<T, U>` (`T::Primitive = u8`): `SIZE` is `None`. -/
recall misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq {T : Type} (U : Type) (inst : misc.raw.int.IntRepr T U8) :
    misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE U inst = none

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq`

/-- `MyDeserialize for RawSeq<T, U>`: total; the given number `len` of bytes, an error with the buffer unchanged if there are fewer. -/
recall misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec {T : Type} (U : Type) (inst : misc.raw.int.IntRepr T U8)
    (len : Usize) (buf : io.ParseBuf) :
    misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize U inst len buf ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map (fun s => cowList s.1) = some (buf.val.take len.val) ∧
        rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec`

/-- `MySerialize for RawSeq<T, U>`: appends the bytes (no length). -/
recall misc.raw.seq.RawSeq0TUU8.Insts.Mysql_commonProtoMySerialize.serialize_spec {T U : Type} (inst : misc.raw.int.IntRepr T U8)
    (self : misc.raw.seq.RawSeq T U U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + (cowList self.1).length ≤ Usize.max) :
    misc.raw.seq.RawSeq0TUU8.Insts.Mysql_commonProtoMySerialize.serialize inst self buf ⦃ buf' => buf'.val = buf.val ++ cowList self.1 ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.RawSeq0TUU8.Insts.Mysql_commonProtoMySerialize.serialize_spec`

/-- Round trip: `deserialize(s.len())` reads back what `serialize` writes. -/
recall misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.roundtrip {T : Type} (U : Type) (inst : misc.raw.int.IntRepr T U8)
    (s tail : List U8) (len : Usize) (hlen : len.val = s.length) (buf : io.ParseBuf)
    (h : buf.val = s ++ tail) :
    misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize U inst len buf ⦃ r rest =>
      (okPart r).map (fun s => cowList s.1) = some s ∧ rest.val = tail ⦄

-- TODO(axioms): `/-- [...] -/ #guard_msgs (whitespace := lax, substring := true) in #print axioms misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.roundtrip`
end mysql_common
