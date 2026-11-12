import Defs

/-! Statements for `enum ChunkInfo and its impls` (spec file: `Specs/Proto/Codec.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `seq_id`: the sequence id of either variant. -/
theorem proto.codec.ChunkInfo.seq_id_eq (ci : proto.codec.ChunkInfo) :
    proto.codec.ChunkInfo.seq_id ci = ok (chunkInfoSeq ci) := by
  sorry

end mysql_common
