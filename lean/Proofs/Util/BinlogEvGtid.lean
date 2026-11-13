import Defs
import Proofs.Io.ParseBuf
import Proofs.Util.ParseBuf
import Proofs.Util.IntAndMisc
import Proofs.Binlog.Events.FormatDescriptionEvent.FormatDescriptionEvent

/-! Helper lemmas for the binlog-event proofs of group `BinlogEvGtid` (GTID, previous-GTIDs,
rotate, intvar, rand, XID, incident, rows-query and transaction-payload events). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.BinlogEvGtid


@[step]
theorem get_event_type_header_length_step (e : binlog.events.format_description_event.FormatDescriptionEvent) (t : binlog.consts.EventType) :
    binlog.events.format_description_event.FormatDescriptionEvent.get_event_type_header_length e t ⦃ n => n.val = postHeaderLen (fdeLens e) t ⦄ :=
  binlog.events.format_description_event.FormatDescriptionEvent.get_event_type_header_length_spec e t

@[step]
theorem checked_skip_step (buf : io.ParseBuf) (cnt : Usize) :
    io.ParseBuf.checked_skip buf cnt ⦃ b rest =>
      if cnt.val ≤ buf.length then b = true ∧ rest.val = buf.val.drop cnt.val
      else b = false ∧ rest = buf ⦄ :=
  io.ParseBuf.checked_skip_spec buf cnt

theorem cast_u8_usize (x : U8) : (UScalar.cast .Usize x).val = x.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits])

theorem cast_u16_usize (x : U16) : (UScalar.cast .Usize x).val = x.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits])

theorem cast_u32_usize (x : U32) : (UScalar.cast .Usize x).val = x.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits])

theorem take_leBytes_append (k n : Nat) (t : List U8) : (leBytes k n ++ t).take k = leBytes k n := by
  simp [List.take_append, PBUtil.length_leBytes]

theorem drop_leBytes_append (k n : Nat) (t : List U8) : (leBytes k n ++ t).drop k = t := by
  simp [List.drop_append, PBUtil.length_leBytes]

theorem leNat_leBytes_of_lt (k n : Nat) (h : n < 2 ^ (8 * k)) : leNat (leBytes k n) = n := by
  rw [PBUtil.leNat_leBytes, Nat.mod_eq_of_lt h]

theorem leNat_leBytes_u8 (x : U8) : leNat (leBytes 1 x.val) = x.val :=
  leNat_leBytes_of_lt _ _ (by have := x.hBounds; simpa using this)
theorem leNat_leBytes_u16 (x : U16) : leNat (leBytes 2 x.val) = x.val :=
  leNat_leBytes_of_lt _ _ (by have := x.hBounds; simpa using this)
theorem leNat_leBytes_u32 (x : U32) : leNat (leBytes 4 x.val) = x.val :=
  leNat_leBytes_of_lt _ _ (by have := x.hBounds; simpa using this)
theorem leNat_leBytes_u64 (x : U64) : leNat (leBytes 8 x.val) = x.val :=
  leNat_leBytes_of_lt _ _ (by have := x.hBounds; simpa using this)

theorem okPart_map_eq_some {T V : Type} {f : T → V} {r : core.result.Result T core.io.error.Error} {v : V}
    (h : (okPart r).map f = some v) : ∃ x, r = .Ok x ∧ f x = v := by
  cases r <;> simp_all [okPart]

end mysql_common.BinlogEvGtid
