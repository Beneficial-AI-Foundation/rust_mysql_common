import Defs
import Proofs.Util.ParseBuf

/-! Helper lemmas for the compressed-codec proofs (group CompCodec: `Proofs/Proto/Codec/Comp*.lean`,
`Compress*.lean`, `PacketCodec*.lean`, `Proofs/Defs/LemmasComp.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.CompCodec

open proto.codec.buf_model

/-! ## Step lemmas for `VecBuf` -/

@[step]
theorem vb_advance_spec (src : VecBuf) (cnt : Usize) (h : cnt.val ≤ src.val.length) :
    VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf.advance src cnt ⦃ r => r.val = src.val.drop cnt.val ⦄ := by
  unfold VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf.advance
  step*
  subst_vars; assumption

@[step]
theorem vb_put_slice_spec (dst : VecBuf) (s : Slice U8) (h : dst.val.length + s.val.length ≤ Usize.max) :
    VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut.put_slice dst s ⦃ r => r.val = dst.val ++ s.val ⦄ := by
  unfold VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut.put_slice alloc.vec.Vec.extend_from_slice
  simp only [dite_eq_left h]
  have := List.clone_spec (clone := core.clone.CloneU8.clone) (l := s.val) (by intros; rfl)
  obtain ⟨l, hl, hp⟩ := PBUtil.spec_eq_ok this
  simp [hl, hp.1]

@[step]
theorem vb_deref_spec (v : VecBuf) : VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref v ⦃ s => s.val = v.val ⦄ := by
  simp [VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, alloc.vec.Vec.deref]

@[step]
theorem vb_reserve_spec (v : VecBuf) (n : Usize) :
    VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve.reserve v n ⦃ r => r = v ⦄ := by
  simp [VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve.reserve]

@[step]
theorem vb_clear_spec (v : VecBuf) :
    VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear.clear v ⦃ r => r.val = [] ⦄ := by
  simp [VecBuf.Insts.Mysql_commonProtoCodecBuf_modelClear.clear]

end mysql_common.CompCodec
