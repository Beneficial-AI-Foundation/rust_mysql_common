import Proofs.Util.BinlogEvGtid
open Aeneas Aeneas.Std Result mysql_common Defs
namespace mysql_common
example (buf : io.ParseBuf) (h : 8 ≤ buf.length) :
    io.ParseBuf.parse_unchecked (misc.raw.int.RawInt.Insts.Mysql_commonProtoMyDeserializeDeTuple
      misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64) buf () ⦃ r rest =>
      ∃ x, r = .Ok x ∧ x.1.val = leNat (buf.val.take 8) ∧ rest.val = buf.val.drop 8 ⦄ := by
  rw [io.ParseBuf.parse_unchecked_eq]
  have hd := misc.raw.int.RawInt.deserialize_spec misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64 buf (fun (o : Option U64) (rest : io.ParseBuf) => o.map (·.val) = some (leNat (buf.val.take 8)) ∧ rest.val = buf.val.drop 8) (misc.raw.int.LeU64.Insts.Mysql_commonMiscRawIntIntReprU64.deserialize_spec buf h)
  apply WP.spec_mono hd
  rintro ⟨r, rest⟩ ⟨h1, h2⟩
  cases r with
  | Ok x => exact ⟨x, rfl, by simpa [okPart] using h1, h2⟩
  | Err e => simp [okPart] at h1
