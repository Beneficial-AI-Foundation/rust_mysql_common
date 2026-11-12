import Defs
import Proofs.Util.RawBytesSeq
import Proofs.Io.ParseBuf

/-! Statements for `enum Either and its impls` (spec file: `Specs/Misc/Raw.lean`). Proofs: TODO. -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `unwrap_left` on `Left(x)` is `x`. -/
theorem misc.raw.Either.unwrap_left_left {T U : Type} (x : T) :
    misc.raw.Either.unwrap_left (misc.raw.Either.Left x : misc.raw.Either T U) = ok x := by
  rfl

/-- `unwrap_left` on `Right(_)` panics (by design). -/
theorem misc.raw.Either.unwrap_left_right {T U : Type} (y : U) :
    misc.raw.Either.unwrap_left (misc.raw.Either.Right y : misc.raw.Either T U) = fail .panic := by
  rfl

/-- `unwrap_right` on `Right(y)` is `y`. -/
theorem misc.raw.Either.unwrap_right_right {T U : Type} (y : U) :
    misc.raw.Either.unwrap_right (misc.raw.Either.Right y : misc.raw.Either T U) = ok y := by
  rfl

/-- `unwrap_right` on `Left(_)` panics (by design). -/
theorem misc.raw.Either.unwrap_right_left {T U : Type} (x : T) :
    misc.raw.Either.unwrap_right (misc.raw.Either.Left x : misc.raw.Either T U) = fail .panic := by
  rfl

/-- `MyDeserialize for Either`: `SIZE` is `None`. -/
theorem misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.SIZE_eq {T U C1 C2 : Type} (i1 : proto.MyDeserialize T C1) (i2 : proto.MyDeserialize U C2) :
    misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.SIZE i1 i2 = none := by
  unfold misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.SIZE; rfl

/-- `MyDeserialize for Either`: with context `Left(ctx)`, `T::deserialize(ctx)` wrapped in `Left`. -/
theorem misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.deserialize_left {T U C1 C2 : Type} (i1 : proto.MyDeserialize T C1)
    (i2 : proto.MyDeserialize U C2) (ctx : C1) (buf : io.ParseBuf)
    (Q : Option T → io.ParseBuf → Prop) (h : i1.deserialize ctx buf ⦃ r rest => Q (okPart r) rest ⦄) :
    misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.deserialize i1 i2 (.Left ctx) buf ⦃ r rest =>
      ∃ o, Q o rest ∧ okPart r = o.map misc.raw.Either.Left ⦄ := by
  unfold misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.deserialize
  step with h as ⟨ r, rest, hr ⟩
  cases r with
  | Ok x => simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨some x, by simpa [okPart] using hr, by simp [okPart]⟩
  | Err e => simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨none, by simpa [okPart] using hr, by simp [okPart]⟩

/-- `MyDeserialize for Either`: with context `Right(ctx)`, `U::deserialize(ctx)` wrapped in `Right`. -/
theorem misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.deserialize_right {T U C1 C2 : Type} (i1 : proto.MyDeserialize T C1)
    (i2 : proto.MyDeserialize U C2) (ctx : C2) (buf : io.ParseBuf)
    (Q : Option U → io.ParseBuf → Prop) (h : i2.deserialize ctx buf ⦃ r rest => Q (okPart r) rest ⦄) :
    misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.deserialize i1 i2 (.Right ctx) buf ⦃ r rest =>
      ∃ o, Q o rest ∧ okPart r = o.map misc.raw.Either.Right ⦄ := by
  unfold misc.raw.Either.Insts.Mysql_commonProtoMyDeserializeDeEither.deserialize
  step with h as ⟨ r, rest, hr ⟩
  cases r with
  | Ok x => simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨some x, by simpa [okPart] using hr, by simp [okPart]⟩
  | Err e => simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨none, by simpa [okPart] using hr, by simp [okPart]⟩

/-- `MySerialize for Either`: `Left(x)` serializes as `x`. -/
theorem misc.raw.Either.Insts.Mysql_commonProtoMySerialize.serialize_left {T U : Type} (i1 : proto.MySerialize T) (i2 : proto.MySerialize U)
    (x : T) (buf : alloc.vec.Vec U8) :
    misc.raw.Either.Insts.Mysql_commonProtoMySerialize.serialize i1 i2 (.Left x) buf = i1.serialize x buf := by
  rfl

/-- `MySerialize for Either`: `Right(y)` serializes as `y`. -/
theorem misc.raw.Either.Insts.Mysql_commonProtoMySerialize.serialize_right {T U : Type} (i1 : proto.MySerialize T) (i2 : proto.MySerialize U)
    (y : U) (buf : alloc.vec.Vec U8) :
    misc.raw.Either.Insts.Mysql_commonProtoMySerialize.serialize i1 i2 (.Right y) buf = i2.serialize y buf := by
  rfl

end mysql_common
