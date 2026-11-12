import Proofs.Util.IntAndMisc

/-! Statements for `impl MySerialize for [u8]` (spec file: `Specs/Misc/Raw.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs WP

namespace mysql_common

/-- appends the bytes. -/
theorem SliceU8.Insts.Mysql_commonProtoMySerialize.serialize_spec (self : Slice U8)
    (buf : alloc.vec.Vec U8) (h : buf.length + self.length ≤ Usize.max) :
    SliceU8.Insts.Mysql_commonProtoMySerialize.serialize self buf
      ⦃ buf' => buf'.val = buf.val ++ self.val ⦄ := by
  unfold SliceU8.Insts.Mysql_commonProtoMySerialize.serialize
  exact IntAndMisc.put_slice_spec buf self h

end mysql_common
