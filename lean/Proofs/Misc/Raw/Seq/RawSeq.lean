import Defs

/-! Statements for `struct RawSeq and its impls` (spec file: `Specs/Misc/Raw/Seq.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `RawSeq::new(t)`: wraps `t.into()`. -/
theorem misc.raw.seq.RawSeq.new_eq {T T3 P : Type} (U : Type) (inst : misc.raw.int.IntRepr T P)
    (into : core.convert.Into T3 (alloc.borrow.Cow (Slice P) (alloc.vec.Vec P))) (t : T3)
    (c : alloc.borrow.Cow (Slice P) (alloc.vec.Vec P)) (h : into.into t = ok c) :
    misc.raw.seq.RawSeq.new U inst into t = ok (c, ()) := by
  sorry

/-- `len`: the number of items. -/
theorem misc.raw.seq.RawSeq.len_spec {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw.seq.RawSeq T U P) :
    misc.raw.seq.RawSeq.len inst self ⦃ n => n.val = (cowList self.1).length ⦄ := by
  sorry

/-- `is_empty`: whether there are no items. -/
theorem misc.raw.seq.RawSeq.is_empty_spec {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw.seq.RawSeq T U P) :
    misc.raw.seq.RawSeq.is_empty inst self ⦃ b => (b ↔ cowList self.1 = []) ⦄ := by
  sorry

/-- `into_owned`: the same items, owned. -/
theorem misc.raw.seq.RawSeq.into_owned_spec {T U P : Type} (inst : misc.raw.int.IntRepr T P)
    (self : misc.raw.seq.RawSeq T U P) :
    misc.raw.seq.RawSeq.into_owned inst self ⦃ r =>
      cowList r.1 = cowList self.1 ∧ ∃ v, r.1 = alloc.borrow.Cow.Owned v ⦄ := by
  sorry

/-- `get(index)`: the item at `index` as a `RawConst`, `None` out of range. -/
theorem misc.raw.seq.RawSeq.get_spec {T U P E : Type} (inst : misc.raw.int.IntRepr T P)
    (cp : core.marker.Copy T) (tf : core.convert.TryFrom U P E)
    (self : misc.raw.seq.RawSeq T U P) (index : Usize) :
    misc.raw.seq.RawSeq.get inst cp tf self index ⦃ o => o.map (·.1) = (cowList self.1)[index.val]? ⦄ := by
  sorry

/-- `MyDeserialize for RawSeq<T, U>` (`T::Primitive = u8`): `SIZE` is `None`. -/
theorem misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE_eq {T : Type} (U : Type) (inst : misc.raw.int.IntRepr T U8) :
    misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.SIZE U inst = none := by
  sorry

/-- `MyDeserialize for RawSeq<T, U>`: total; the given number `len` of bytes, an error with the buffer unchanged if there are fewer. -/
theorem misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize_spec {T : Type} (U : Type) (inst : misc.raw.int.IntRepr T U8)
    (len : Usize) (buf : io.ParseBuf) :
    misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize U inst len buf ⦃ r rest =>
      if len.val ≤ buf.length then
        (okPart r).map (fun s => cowList s.1) = some (buf.val.take len.val) ∧
        rest.val = buf.val.drop len.val
      else okPart r = none ∧ rest = buf ⦄ := by
  sorry

/-- `MySerialize for RawSeq<T, U>`: appends the bytes (no length). -/
theorem misc.raw.seq.RawSeq0TUU8.Insts.Mysql_commonProtoMySerialize.serialize_spec {T U : Type} (inst : misc.raw.int.IntRepr T U8)
    (self : misc.raw.seq.RawSeq T U U8) (buf : alloc.vec.Vec U8)
    (h : buf.length + (cowList self.1).length ≤ Usize.max) :
    misc.raw.seq.RawSeq0TUU8.Insts.Mysql_commonProtoMySerialize.serialize inst self buf ⦃ buf' => buf'.val = buf.val ++ cowList self.1 ⦄ := by
  sorry

/-- Round trip: `deserialize(s.len())` reads back what `serialize` writes. -/
theorem misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.roundtrip {T : Type} (U : Type) (inst : misc.raw.int.IntRepr T U8)
    (s tail : List U8) (len : Usize) (hlen : len.val = s.length) (buf : io.ParseBuf)
    (h : buf.val = s ++ tail) :
    misc.raw.seq.RawSeqDeTUU8.Insts.Mysql_commonProtoMyDeserializeDeUsize.deserialize U inst len buf ⦃ r rest =>
      (okPart r).map (fun s => cowList s.1) = some s ∧ rest.val = tail ⦄ := by
  sorry

end mysql_common
