import Defs

/-! Statements for `impl IntRepr for VarLen` (spec file: `Specs/Misc/Raw/Int.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `VarLen::SIZE` is `None`. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE_eq :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.SIZE = none := by
  sorry

/-- `VarLen::deserialize`: total; the JSONB varlen reader `jsonbVarLenRead` (at most 5 bytes,
    errors on more, on values above `u32::MAX`, and on end of input; the bytes read are consumed). -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_spec (buf : io.ParseBuf) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest =>
      ((okPart r).map (·.val), rest.val) = jsonbVarLenRead buf.val ⦄ := by
  sorry

/-- `buf.parse::<RawInt<VarLen>>(())`: total; `jsonbVarLenRead` (`SIZE` is `None`, so this is `deserialize`). -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.parse_rawint_spec (buf : io.ParseBuf) :
    io.ParseBuf.parse (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32) buf () ⦃ r rest =>
      ((okPart r).map (·.1.val), rest.val) = jsonbVarLenRead buf.val ⦄ := by
  sorry

/-- `VarLen::deserialize` reads back the JSONB encoding `jsonbVarLen x` of every `u32`. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize_roundtrip (x : U32) (tail : List U8) (buf : io.ParseBuf)
    (h : buf.val = jsonbVarLen x.val ++ tail) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.deserialize buf ⦃ r rest => okPart r = some x ∧ rest.val = tail ⦄ := by
  sorry

/-- **Bug.** `VarLen::serialize` does not write the JSONB encoding. Its loop has its two
    branches swapped (it stops, setting the continuation bit, as soon as more bits remain): for
    `x ≥ 128` it appends the single byte `(x mod 128) | 0x80` and drops the higher bits. Since
    that byte has its continuation bit set, `deserialize` goes on into whatever bytes follow it
    and can silently return a wrong value; at the end of the input it fails. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_large (x : U32) (buf : alloc.vec.Vec U8) (hx : 128 ≤ x.val)
    (h : buf.length + 1 ≤ Usize.max) :
    misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ buf' => buf'.val = buf.val ++ [byte (x.val % 128 + 128)] ⦄ := by
  sorry

/-- **Bug.** For `x < 128`, `VarLen::serialize` never returns: after writing `x` its loop keeps
    appending `0` bytes forever (in Rust: until allocation fails and the process aborts; in the
    Lean model: until the `Vec` reaches `usize::MAX` and the next `push` fails). It is stated as
    "does not return normally" rather than as an equation because the failure only comes after
    `usize::MAX` iterations of the loop. -/
theorem misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize_small_fails (x : U32) (buf : alloc.vec.Vec U8) (hx : x.val < 128) :
    ¬ misc.raw.int.VarLen.Insts.Mysql_commonMiscRawIntIntReprU32.serialize x buf ⦃ _ => True ⦄ := by
  sorry

end mysql_common
