import Defs
import Proofs.Util.CompCodec
import Proofs.Proto.Codec.CompressWith
import Proofs.Proto.Codec.CompDecoder
import Proofs.Proto.Codec.PlainPacketCodec
import Proofs.Defs.LemmasCF
import Proofs.Defs.LemmasComp

/-! Statements for `struct CompPacketCodec and its impls` (spec file: `Specs/Proto/Codec.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

/-! Helper lemmas: the plain packet reader on a growing input, and the compressed reader on a
stream of compressed packets (`run_main`). -/

namespace mysql_common.CompCodec

open WP

theorem plainDecodeAux_none (f : Nat) : ∀ (seq : U8) (st : ChunkState) (src dst : List U8) (max : Nat)
    (comp : Option U8),
    (plainDecodeAux f seq st src dst max none).1 ≠ .Err .PacketsOutOfSync →
    plainDecodeAux f seq st src dst max comp = plainDecodeAux f seq st src dst max none := by
  induction f with
  | zero => intros; rfl
  | succ f ih =>
    intro seq st src dst max comp h
    simp only [plainDecodeAux] at h ⊢
    rcases hc : chunkStep st src dst max with ⟨r, st', src', dst'⟩
    rw [hc] at h
    rcases r with ((_ | info) | e)
    · rfl
    · simp only at h ⊢
      by_cases hs : seq = chunkInfoSeq info
      · have h1 : ¬ (seq ≠ chunkInfoSeq info ∧ comp ≠ some (chunkInfoSeq info)) := fun h => h.1 hs
        have h2 : ¬ (seq ≠ chunkInfoSeq info ∧ (none : Option U8) ≠ some (chunkInfoSeq info)) := fun h => h.1 hs
        simp only [h1, h2, ↓reduceIte] at h ⊢
        cases info with
        | Last _ => rfl
        | Middle s0 =>
          simp only at h ⊢
          split_ifs at h ⊢
          · rfl
          · exact ih _ _ _ _ _ _ h
      · have h2 : (seq ≠ chunkInfoSeq info ∧ (none : Option U8) ≠ some (chunkInfoSeq info)) := ⟨hs, by simp⟩
        simp [h2] at h
    · rfl

theorem chunkStep_some_append (st : ChunkState) (src dst : List U8) (max : Nat) (info : proto.codec.ChunkInfo)
    (st' : ChunkState) (src' dst' : List U8) (h : chunkStep st src dst max = (.Ok (some info), st', src', dst'))
    (more : List U8) :
    chunkStep st (src ++ more) dst max = (.Ok (some info), st', src' ++ more, dst') ∧ src'.length < src.length := by
  cases st with
  | idle =>
    simp only [chunkStep] at h ⊢
    by_cases h1 : src.length < 4
    · simp [h1] at h
    · have e1 : ¬ (src ++ more).length < 4 := by simp; omega
      have e2 : (src ++ more).take 3 = src.take 3 := List.take_append_of_le_length (by omega)
      have e3 : (src ++ more).getD 3 (byte 0) = src.getD 3 (byte 0) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show 3 < src.length by omega)]
      simp only [h1, ↓reduceIte] at h
      simp only [e1, e2, e3, ↓reduceIte]
      by_cases h2 : leNat (src.take 3) = 0
      · simp only [h2, ↓reduceIte, Prod.mk.injEq] at h ⊢
        obtain ⟨hr, rfl, rfl, rfl⟩ := h
        simp only [hr, List.drop_append_of_le_length (show 4 ≤ src.length by omega), true_and]
        simp; omega
      · by_cases h3 : max < dst.length + leNat (src.take 3)
        · simp [h2, h3] at h
        · by_cases h4 : 4 + leNat (src.take 3) ≤ src.length
          · have e4 : 4 + leNat (src.take 3) ≤ (src ++ more).length := by simp; omega
            simp only [h2, h3, h4, e4, ↓reduceIte, Prod.mk.injEq] at h ⊢
            obtain ⟨hr, rfl, rfl, rfl⟩ := h
            simp only [true_and]
            rw [List.drop_append_of_le_length (show 4 ≤ src.length by omega),
              List.drop_append_of_le_length h4, List.take_append_of_le_length (l₁ := List.drop 4 src) (l₂ := more) (by simp; omega)]
            exact ⟨⟨hr, rfl, rfl⟩, by simp; omega⟩
          · simp [h2, h3, h4] at h
  | chunk seq len =>
    simp only [chunkStep] at h ⊢
    by_cases h1 : 4 + len ≤ src.length
    · have e4 : 4 + len ≤ (src ++ more).length := by simp; omega
      simp only [h1, e4, ↓reduceIte, Prod.mk.injEq] at h ⊢
      obtain ⟨hr, rfl, rfl, rfl⟩ := h
      simp only [true_and]
      rw [List.drop_append_of_le_length (show 4 ≤ src.length by omega),
        List.drop_append_of_le_length h1, List.take_append_of_le_length (l₁ := List.drop 4 src) (l₂ := more) (by simp; omega)]
      exact ⟨⟨hr, rfl, rfl⟩, by simp; omega⟩
    · simp [h1] at h

theorem chunkStep_none_append (st : ChunkState) (src dst : List U8) (max : Nat)
    (st' : ChunkState) (src' dst' : List U8) (h : chunkStep st src dst max = (.Ok none, st', src', dst'))
    (more : List U8) :
    src' = src ∧ dst' = dst ∧ chunkStep st' (src ++ more) dst max = chunkStep st (src ++ more) dst max := by
  cases st with
  | idle =>
    simp only [chunkStep] at h
    by_cases h1 : src.length < 4
    · simp only [h1, ↓reduceIte, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
    · simp only [h1, ↓reduceIte] at h
      by_cases h2 : leNat (src.take 3) = 0
      · simp [h2] at h
      · by_cases h3 : max < dst.length + leNat (src.take 3)
        · simp [h2, h3] at h
        · by_cases h4 : 4 + leNat (src.take 3) ≤ src.length
          · simp [h2, h3, h4] at h
          · simp only [h2, h3, h4, ↓reduceIte, Prod.mk.injEq] at h
            obtain ⟨-, rfl, rfl, rfl⟩ := h
            refine ⟨rfl, rfl, ?_⟩
            have e1 : ¬ (src ++ more).length < 4 := by simp; omega
            have e2 : (src ++ more).take 3 = src.take 3 := List.take_append_of_le_length (by omega)
            have e3 : (src ++ more).getD 3 (byte 0) = src.getD 3 (byte 0) := by
              simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show 3 < src.length by omega)]
            simp only [chunkStep, e1, e2, e3, h2, h3, ↓reduceIte]
  | chunk seq len =>
    simp only [chunkStep] at h
    by_cases h1 : 4 + len ≤ src.length
    · simp [h1] at h
    · simp only [h1, ↓reduceIte, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl⟩

theorem plainDecode_nil (seq : U8) (st : ChunkState) (dst : List U8) (max : Nat) (comp : Option U8) :
    plainDecode seq st [] dst max comp = (.Ok false, seq, st, [], dst) := by
  unfold plainDecode
  cases st <;> simp [plainDecodeAux, chunkStep]

theorem plainDecode_step_middle (seq : U8) (st : ChunkState) (X dst : List U8) (max : Nat) (comp : Option U8)
    (s0 : U8) (st' : ChunkState) (Y dst' : List U8)
    (hc : chunkStep st X dst max = (.Ok (some (.Middle s0)), st', Y, dst'))
    (hm : ¬ (seq ≠ s0 ∧ comp ≠ some s0)) (hlt : Y.length < X.length) :
    plainDecode seq st X dst max comp =
      if Y = [] then (.Ok false, byte (s0.val + 1), st', Y, dst')
      else plainDecode (byte (s0.val + 1)) st' Y dst' max comp := by
  conv_lhs => unfold plainDecode; simp only [plainDecodeAux, hc, chunkInfoSeq, hm, ↓reduceIte]
  split_ifs
  · rfl
  · exact plainDecodeAux_fuel _ _ _ _ _ _ _ (by omega)

theorem plainDecodeAux_append (f : Nat) : ∀ (seq : U8) (st : ChunkState) (src dst : List U8) (max : Nat)
    (comp : Option U8) (seq1 : U8) (st1 : ChunkState) (src1 dst1 : List U8),
    plainDecodeAux f seq st src dst max comp = (.Ok false, seq1, st1, src1, dst1) →
    ∀ more, plainDecode seq1 st1 (src1 ++ more) dst1 max comp = plainDecode seq st (src ++ more) dst max comp := by
  induction f with
  | zero =>
    intro seq st src dst max comp seq1 st1 src1 dst1 h more
    simp only [plainDecodeAux, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl, rfl, rfl⟩ := h
    rfl
  | succ f ih =>
    intro seq st src dst max comp seq1 st1 src1 dst1 h more
    simp only [plainDecodeAux] at h
    rcases hc : chunkStep st src dst max with ⟨r, st', src', dst'⟩
    rw [hc] at h
    rcases r with ((_ | info) | e)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨rfl, rfl, he⟩ := chunkStep_none_append st src dst max st' src' dst' hc more
      unfold plainDecode
      simp only [plainDecodeAux, he]
    · simp only at h
      obtain ⟨hcs, hlt⟩ := chunkStep_some_append st src dst max info st' src' dst' hc more
      by_cases hm : seq ≠ chunkInfoSeq info ∧ comp ≠ some (chunkInfoSeq info)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hm)] at h; simp at h
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)] at h
        cases info with
        | Last _ => simp at h
        | Middle s0 =>
          simp only [chunkInfoSeq] at h hm
          rw [plainDecode_step_middle seq st (src ++ more) dst max comp s0 st' (src' ++ more) dst' hcs hm
            (by simp; omega)]
          by_cases he : src' = []
          · simp only [he, ↓reduceIte, Prod.mk.injEq] at h
            obtain ⟨-, rfl, rfl, rfl, rfl⟩ := h
            subst he
            simp only [List.nil_append]
            split_ifs with hmo
            · subst hmo; exact plainDecode_nil _ _ _ _ _
            · rfl
          · simp only [he, ↓reduceIte] at h
            have hne : src' ++ more ≠ [] := by simp [he]
            simp only [hne, ↓reduceIte]
            exact ih _ _ _ _ _ _ _ _ _ _ h more
    · simp at h

theorem chunkStep_sizes (st : ChunkState) (src dst : List U8) (max : Nat) :
    (chunkStep st src dst max).2.2.2.length + (chunkStep st src dst max).2.2.1.length ≤ dst.length + src.length := by
  unfold chunkStep
  cases st <;> simp only <;> split_ifs <;> simp <;> omega

theorem plainDecodeAux_sizes (n : Nat) : ∀ (seq : U8) (st : ChunkState) (src dst : List U8) (max : Nat) (comp : Option U8),
    (plainDecodeAux n seq st src dst max comp).2.2.2.2.length + (plainDecodeAux n seq st src dst max comp).2.2.2.1.length ≤
      dst.length + src.length := by
  induction n with
  | zero => intros; simp [plainDecodeAux]
  | succ n ih =>
    intro seq st src dst max comp
    have hsz := chunkStep_sizes st src dst max
    simp only [plainDecodeAux]
    rcases hc : chunkStep st src dst max with ⟨r, st', src', dst'⟩
    rw [hc] at hsz
    simp only at hsz
    rcases r with ((_ | info) | e)
    · simp; omega
    · cases info with
      | Last _ => simp only; split_ifs <;> simp <;> omega
      | Middle s0 =>
        simp only; split_ifs
        all_goals first
          | (simp; omega)
          | (have := ih (byte ((chunkInfoSeq (.Middle s0)).val + 1)) st' src' dst' max comp; omega)
    · simp; omega

theorem compStep_none_append (inf : List U8 → Nat → core.result.Result (List U8) core.io.error.Error)
    (st : CompState) (src dst : List U8) (max : Nat)
    (st' : CompState) (src' dst' : List U8) (h : compStep inf st src dst max = (.Ok none, st', src', dst'))
    (more : List U8) (d : List U8) :
    src' = src ∧ dst' = dst ∧ compStep inf st' (src ++ more) d max = compStep inf st (src ++ more) d max := by
  cases st with
  | idle =>
    by_cases h1 : src.length < 7
    · simp only [compStep, h1, ↓reduceIte, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
    · rcases hh : compHeaderRead src with ⟨cl, sq, pl⟩
      rw [compStep_idle_hdr _ _ _ _ _ _ _ (by omega) hh] at h
      have hh' : compHeaderRead (src ++ more) = (cl, sq, pl) := by
        rw [← hh]; simp only [compHeaderRead]
        rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
          List.take_append_of_le_length (by simp; omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show 3 < src.length by omega)]
      by_cases h2 : max < Nat.max cl pl
      · simp [h2] at h
      · by_cases h3 : cl = 0
        · by_cases h4 : pl = 0 <;> simp only [h3, h4, ↓reduceIte] at h <;> (try split_ifs at h) <;> simp at h
        · simp only [h2, h3, ↓reduceIte] at h
          rw [compStep_idle_hdr _ _ _ _ _ _ _ (by simp; omega) hh']
          simp only [h2, h3, ↓reduceIte]
          simp only [compStep] at h
          by_cases h5 : 7 + cl ≤ src.length
          · simp only [h5, ↓reduceIte] at h
            revert h; split <;> (try split) <;> simp
          · simp only [h5, ↓reduceIte, Prod.mk.injEq] at h
            obtain ⟨-, rfl, rfl, rfl⟩ := h
            exact ⟨rfl, rfl, rfl⟩
  | packet sq cl pl =>
    simp only [compStep] at h
    by_cases h5 : 7 + cl ≤ src.length
    · simp only [h5, ↓reduceIte] at h
      revert h; split <;> (try split) <;> simp
    · simp only [h5, ↓reduceIte, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl⟩

theorem flatten_take_prefix (l : List (List U8)) (j : Nat) :
    l.flatten = (l.take j).flatten ++ (l.drop j).flatten := by
  rw [← List.flatten_append, List.take_append_drop]

theorem flatten_take_length_le (l : List (List U8)) (j : Nat) : (l.take j).flatten.length ≤ l.flatten.length := by
  have := congrArg List.length (flatten_take_prefix l j)
  simp only [List.length_append] at this; omega

/-- Before the last piece, the pieces read so far are a strict prefix of the frame. -/
theorem stream_prefix (pieces : List (List U8)) (F rest : List U8) (hp : pieces.flatten = F ++ rest)
    (hlast : pieces.dropLast.flatten.length < F.length) (j : Nat) (hj : j < pieces.length) :
    (pieces.take j).flatten = F.take (pieces.take j).flatten.length ∧ (pieces.take j).flatten.length < F.length := by
  have h1 : (pieces.take j).flatten.length ≤ pieces.dropLast.flatten.length := by
    rw [List.dropLast_eq_take]
    have : pieces.take j = (pieces.take (pieces.length - 1)).take j := by
      rw [List.take_take]; congr 1; omega
    rw [this]; exact flatten_take_length_le _ _
  refine ⟨?_, by omega⟩
  have h2 := flatten_take_prefix pieces j
  rw [hp] at h2
  have := congrArg (List.take (pieces.take j).flatten.length) h2
  rw [List.take_left' rfl, List.take_append_of_le_length (by omega)] at this
  exact this.symm

theorem compPackets_drop (seq0 : Nat) (pieces : List (List U8)) (zs : List (Option (List U8)))
    (hl : pieces.length = zs.length) (j : Nat) (hj : j < pieces.length) :
    compPackets (seq0 + j) (pieces.drop j) (zs.drop j) =
      compPacket (seq0 + j) pieces[j] zs[j] ++ compPackets (seq0 + (j + 1)) (pieces.drop (j + 1)) (zs.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons (l := pieces) (i := j) hj, List.drop_eq_getElem_cons (l := zs) (i := j) (by rw [← hl]; exact hj)]
  simp only [compPackets]
  congr 1

open proto.codec.buf_model

theorem compStepFits_of (st : proto.codec.CompDecoder) (hv : (CompState.of st).Valid) (b : List U8)
    (h : b.length + 2 ^ 24 ≤ Usize.max) : compStepFits (CompState.of st) b := by
  have hU : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  cases st with
  | Idle => simpa [CompState.of, compStepFits] using h
  | Packet sq d =>
    cases d <;> simp only [CompState.of, CompState.Valid, compStepFits] at hv ⊢
    · obtain ⟨h1, h2, h3⟩ := hv
      have := h3 _ rfl
      simp; omega
    · obtain ⟨h1, h2, -⟩ := hv; simp; omega

theorem chunkValid_hv (c : proto.codec.PlainPacketCodec) (hv : (ChunkState.of c.chunk_decoder).Valid) :
    ∀ seq needed, c.chunk_decoder = .Chunk seq needed → 4 + needed.val ≤ Usize.max := by
  intro seq needed h
  rw [h] at hv
  have hU : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  simp only [ChunkState.of, ChunkState.Valid] at hv; omega

theorem of_idle (cd : proto.codec.CompDecoder) (h : CompState.of cd = .idle) : cd = .Idle := by
  cases cd with
  | Idle => rfl
  | Packet a b => cases b <;> simp [CompState.of] at h

theorem chunk_of_idle (cd : proto.codec.ChunkDecoder) (h : ChunkState.of cd = .idle) : cd = .Idle := by
  cases cd with
  | Idle => rfl
  | Chunk a b => simp [ChunkState.of] at h

theorem take_succ_flatten (l : List (List U8)) (j : Nat) (hj : j < l.length) :
    (l.take (j + 1)).flatten = (l.take j).flatten ++ l[j] := by
  have : l.take (j + 1) = l.take j ++ [l[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  rw [this, List.flatten_append]; simp

theorem PS_next (ps : U8) (pieces : List (List U8)) (max : Nat) (j : Nat) (hj : j < pieces.length)
    (s : U8) (st : ChunkState) (r d : List U8)
    (h : plainDecode ps .idle ((pieces.take j).flatten) [] max none = (.Ok false, s, st, r, d)) :
    plainDecode s st (r ++ pieces[j]) d max none = plainDecode ps .idle ((pieces.take (j + 1)).flatten) [] max none := by
  rw [take_succ_flatten _ _ hj]
  exact plainDecodeAux_append _ _ _ _ _ _ _ _ _ _ _ h _

theorem compPackets_length_ge (seq : Nat) (cs : List (List U8)) (zs : List (Option (List U8)))
    (hl : cs.length = zs.length) : 7 * cs.length ≤ (compPackets seq cs zs).length := by
  induction cs generalizing seq zs with
  | nil => simp
  | cons c cs ih =>
    cases zs with
    | nil => simp at hl
    | cons z zs' =>
      have := ih (seq + 1) zs' (by simpa using hl)
      have h7 : 7 ≤ (compPacket seq c z).length := by
        cases z <;> simp [compPacket, compHeader, PBUtil.length_leBytes] <;> omega
      simp only [compPackets, List.length_append, List.length_cons]
      omega

theorem run_main (pieces : List (List U8)) (zs : List (Option (List U8)))
    (hF : List.Forall₂ (fun c zo => ∀ z, zo = some z → Deflates c z) pieces zs)
    (ps : U8) (p rest tail : List U8) (hpieces : pieces.flatten = frame ps.val p ++ rest)
    (hlast : pieces.dropLast.flatten.length < (frame ps.val p).length)
    (max : Usize) (hsize : ∀ c ∈ pieces, c ≠ [] ∧ c.length ≤ Nat.min maxPayloadLen max.val)
    (hmax : p.length ≤ max.val) (seq0 : Nat)
    (hbound : pieces.flatten.length + 2 ^ 24 ≤ Usize.max) :
    ∀ m j (c : proto.codec.CompPacketCodec) (src dst : VecBuf), pieces.length - j = m → j ≤ pieces.length →
    c.comp_seq_id = byte (seq0 + j) →
    plainDecode c.plain_codec.seq_id (ChunkState.of c.plain_codec.chunk_decoder) c.in_buf.val dst.val max.val none =
      plainDecode ps .idle ((pieces.take j).flatten) [] max.val none →
    (∀ inf d, compStep inf (CompState.of c.comp_decoder) src.val d max.val =
      compStep inf .idle (compPackets (seq0 + j) (pieces.drop j) (zs.drop j) ++ tail) d max.val) →
    (CompState.of c.comp_decoder).Valid → (ChunkState.of c.plain_codec.chunk_decoder).Valid →
    c.in_buf.val.length + dst.val.length ≤ ((pieces.take j).flatten).length →
    (j = pieces.length → src.val = tail ∧ c.comp_decoder = .Idle) →
    proto.codec.CompPacketCodec.decode VecBuf.Insts.CoreOpsDerefDerefSliceU8 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf VecBuf.Insts.CoreConvertAsRefSliceU8 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut c src dst max ⦃ r c' src' dst' =>
      r = .Ok true ∧ dst'.val = p ∧ src'.val = tail ∧ c'.in_buf.val = rest ∧
      c'.comp_seq_id = byte (seq0 + pieces.length) ∧
      c'.plain_codec.seq_id = byte (ps.val + frameCount p.length) ∧
      c'.comp_decoder = .Idle ∧ c'.plain_codec.chunk_decoder = .Idle ⦄ := by
  have hzl : pieces.length = zs.length := hF.length_eq
  have hK : ∀ j, ((pieces.take j).flatten).length ≤ pieces.flatten.length := flatten_take_length_le pieces
  have hU : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  -- the plain decoder on the pieces read so far
  have hPSlt : ∀ j, j < pieces.length → ∃ s st r d, plainDecode ps .idle ((pieces.take j).flatten) [] max.val none =
      (.Ok false, s, st, r, d) := by
    intro j hj
    obtain ⟨e1, e2⟩ := stream_prefix pieces _ rest hpieces hlast j hj
    rcases hpd : plainDecode ps .idle ((pieces.take j).flatten) [] max.val none with ⟨r0, s, st, r, d⟩
    rw [e1] at hpd
    have := (plainDecode_resume ps p [] _ e2 max.val hmax none r0 s st r d hpd).1
    exact ⟨s, st, r, d, by rw [← this]⟩
  have hPSn : plainDecode ps .idle ((pieces.take pieces.length).flatten) [] max.val none =
      (.Ok true, byte (ps.val + frameCount p.length), .idle, rest, p) := by
    rw [List.take_length, hpieces]
    have := plainDecode_frame ps p rest max.val hmax none
    exact this
  intro m
  induction m with
  | zero =>
    intro j c src dst hm hj hseq hpd hcc hvc hvp hbd hend
    have hjn : j = pieces.length := by omega
    subst hjn
    obtain ⟨hsrc, hcd⟩ := hend rfl
    rw [hPSn] at hpd
    have hne : c.in_buf.val ≠ [] := by intro e; rw [e, plainDecode_nil] at hpd; simp at hpd
    rw [proto.codec.CompPacketCodec.decode]
    have hne' : ¬ (alloc.vec.Vec.deref c.in_buf).length = 0 := by
      simpa [Slice.length, alloc.vec.Vec.deref] using hne
    simp only [VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty,
      Std.bind_ok, hne', decide_false, Bool.false_eq_true, ↓reduceIte, lift]
    have hKn := hK pieces.length
    obtain ⟨⟨r, ppc, vb, dst1⟩, hv, hp, -⟩ := PBUtil.spec_eq_ok (proto.codec.PlainPacketCodec.decode_spec c.plain_codec
      (chunkValid_hv _ hvp) c.in_buf dst max (some (core.num.U8.wrapping_sub c.comp_seq_id 1#u8))
      (by simp only [alloc.vec.Vec.length]; omega))
    rw [hv]
    unfold plainDecode at hp hpd
    rw [plainDecodeAux_none (c.in_buf.val.length + 1) c.plain_codec.seq_id (ChunkState.of c.plain_codec.chunk_decoder)
      c.in_buf.val dst.val max.val _ (by rw [hpd]; simp), hpd] at hp
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, hseq', hcd', hvb, hd1⟩ := hp
    have hcd'' := chunk_of_idle _ hcd'
    simp [core.result.Result.Insts.CoreOpsTry.branch, proto.codec.trusted.vec_capacity,
      proto.codec.COMP_CODEC_SHRINK_THRESHOLD]
    split_ifs with he
    · step*
      all_goals simp_all [alloc.vec.Vec.new, alloc.vec.Vec.deref]
    · simp [hd1, hvb, hseq', hcd'', hsrc, hseq, hcd]
  | succ m ih =>
    intro j c src dst hm hj hseq hpd hcc hvc hvp hbd hend
    have hjn : j < pieces.length := by omega
    obtain ⟨s, st, r, d, hPS⟩ := hPSlt j hjn
    have hKj1 := hK (j + 1)
    have hz : ∀ z, zs[j]'(by rw [← hzl]; exact hjn) = some z → Deflates pieces[j] z :=
      (List.forall₂_iff_get.mp hF).2 j hjn (by rw [← hzl]; exact hjn)
    have hcs := (hsize _ (List.getElem_mem hjn)).2
    have hread : ∀ (i : flate2.mem.Decompress) (b : List U8), compStep (inflateList i) (CompState.of c.comp_decoder) src.val b max.val =
        (.Ok (some (.Last (byte (seq0 + j)))), .idle,
          compPackets (seq0 + (j + 1)) (pieces.drop (j + 1)) (zs.drop (j + 1)) ++ tail, b ++ pieces[j]) := by
      intro i b
      rw [hcc, compPackets_drop seq0 pieces zs hzl j hjn, List.append_assoc]
      exact compStep_compPacket i _ _ _ hz _ b max.val hcs
    have hbseq : (c.comp_seq_id != byte (seq0 + j)) = false := by simp [hseq]
    have hwrap : core.num.U8.wrapping_add c.comp_seq_id 1#u8 = byte (seq0 + (j + 1)) := by
      rw [wrap_one, hseq, byte_succ]
    have hflat := take_succ_flatten pieces j hjn
    rw [proto.codec.CompPacketCodec.decode]
    by_cases hib : c.in_buf.val = []
    · have he : (alloc.vec.Vec.deref c.in_buf).length = 0 := by simp [Slice.length, alloc.vec.Vec.deref, hib]
      simp only [VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty,
        Std.bind_ok, he, decide_true, ↓reduceIte]
      obtain ⟨⟨r1, cd1, src1, vb1, o1⟩, hv, hp⟩ := PBUtil.spec_eq_ok (decode_with_spec c.comp_decoder src c.in_buf max
        c.inflater (compStepFits_of _ hvc _ (by rw [hib]; simp; omega)))
      rw [hv]
      simp only [WP.uncurry'_pair] at hp
      rw [hread, hib] at hp
      simp only [Prod.mk.injEq, List.nil_append] at hp
      obtain ⟨rfl, hcd1, hs1, hvb1⟩ := hp
      rw [hib, plainDecode_nil, hPS] at hpd
      simp only [Prod.mk.injEq] at hpd
      obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hpd
      simp [core.result.Result.Insts.CoreOpsTry.branch, proto.codec.ChunkInfo.seq_id, hseq, lift]
      refine ih (j + 1) _ src1 dst (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · show core.num.U8.wrapping_add (byte (seq0 + j)) 1#u8 = _
        rw [wrap_one, byte_succ]
      · simp only [hvb1]
        exact PS_next ps pieces max.val j hjn _ _ _ _ hPS
      · intro inf d; rw [hcd1, hs1]
      · rw [hcd1]; trivial
      · exact hvp
      · simp only [hvb1, hflat, List.length_append]; omega
      · intro hjj; rw [hjj] at hs1
        refine ⟨by rw [hs1]; simp [compPackets], of_idle _ hcd1⟩
    · have hne' : ¬ (alloc.vec.Vec.deref c.in_buf).length = 0 := by
        simpa [Slice.length, alloc.vec.Vec.deref] using hib
      simp only [VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty,
        Std.bind_ok, hne', decide_false, Bool.false_eq_true, ↓reduceIte, lift]
      have hKj := hK j
      obtain ⟨⟨r0, ppc, vb, dst1⟩, hv, hp, hvalid⟩ := PBUtil.spec_eq_ok (proto.codec.PlainPacketCodec.decode_spec
        c.plain_codec (chunkValid_hv _ hvp) c.in_buf dst max (some (core.num.U8.wrapping_sub c.comp_seq_id 1#u8))
        (by simp only [alloc.vec.Vec.length]; omega))
      rw [hv]
      have hpd2 := hpd.trans hPS
      have hsz := plainDecodeAux_sizes ((pieces.take j).flatten.length + 1) ps .idle ((pieces.take j).flatten) [] max.val none
      have hPS' := hPS
      unfold plainDecode at hp hpd2 hPS'
      rw [hPS'] at hsz
      simp only [List.length_nil, zero_add] at hsz
      rw [plainDecodeAux_none (c.in_buf.val.length + 1) c.plain_codec.seq_id (ChunkState.of c.plain_codec.chunk_decoder)
        c.in_buf.val dst.val max.val _ (by rw [hpd2]; simp), hpd2] at hp
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl, rfl, hvb, hd1⟩ := hp
      subst hvb hd1
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      obtain ⟨⟨r1, cd1, src1, vb1, o1⟩, hv2, hp2⟩ := PBUtil.spec_eq_ok (decode_with_spec c.comp_decoder src vb max
        c.inflater (compStepFits_of _ hvc _ (by omega)))
      rw [hv2]
      simp only [WP.uncurry'_pair] at hp2
      rw [hread] at hp2
      simp only [Prod.mk.injEq] at hp2
      obtain ⟨rfl, hcd1, hs1, hvb1⟩ := hp2
      simp [proto.codec.ChunkInfo.seq_id, hseq]
      refine ih (j + 1) _ src1 dst1 (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · show core.num.U8.wrapping_add (byte (seq0 + j)) 1#u8 = _
        rw [wrap_one, byte_succ]
      · simp only [hvb1]
        exact PS_next ps pieces max.val j hjn _ _ _ _ hPS
      · intro inf d; rw [hcd1, hs1]
      · rw [hcd1]; trivial
      · exact hvalid hvp
      · simp only [hvb1, hflat, List.length_append]; omega
      · intro hjj; rw [hjj] at hs1
        refine ⟨by rw [hs1]; simp [compPackets], of_idle _ hcd1⟩

end mysql_common.CompCodec

namespace mysql_common

open proto.codec.buf_model in
private theorem decode_idle_hdr_err (src dst : VecBuf) (max : Usize) (inf : Option flate2.mem.Decompress)
    (hl7 : 7 ≤ src.val.length)
    (herr : max.val < Nat.max (compHeaderRead src.val).1 (compHeaderRead src.val).2.2 ∨
      ((compHeaderRead src.val).1 = 0 ∧ (compHeaderRead src.val).2.2 ≠ 0)) :
    proto.codec.CompDecoder.decode_with VecBuf.Insts.CoreOpsDerefDerefSliceU8 VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut
      .Idle src dst max inf ⦃ _ cd src' dst' inf' => inf' = inf ∧ cd = .Idle ∧ src' = src ∧ dst' = dst ⦄ := by
  rw [proto.codec.CompDecoder.decode_with]
  simp only [proto.codec.CompData.new_eq]
  step*
  all_goals
    have hl := hl7
    obtain ⟨a, b, c, d, e, f, g, rr, hsrc⟩ : ∃ a b c d e f g rr, src.val = a :: b :: c :: d :: e :: f :: g :: rr := by
      match hh : src.val with
      | a :: b :: c :: d :: e :: f :: g :: rr => exact ⟨a, b, c, d, e, f, g, rr, rfl⟩
      | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] => simp [hh] at hl
    have hcl : compressed_len.val = leNat [a, b, c] := by
      rw [compressed_len_post, UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by cases System.Platform.numBits_eq <;> simp [*])]
      have : i4.val = i4.bv.toNat := rfl
      rw [this, i4_post, PBUtil.fromLEBytes_cast_toNat]
      simp only [Array.make_val]
      have := PBUtil.leNat_append_zeros [a, b, c] 1
      simp_all
    have hpl : uncompressed_len.val = leNat [e, f, g] := by
      rw [uncompressed_len_post, UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by cases System.Platform.numBits_eq <;> simp [*])]
      have : i8.val = i8.bv.toNat := rfl
      rw [this, i8_post, PBUtil.fromLEBytes_cast_toNat]
      simp only [Array.make_val]
      have := PBUtil.leNat_append_zeros [e, f, g] 1
      simp_all
    have hseq : seq_id = d := by simp_all
    have hb1 : leNat [a, b, c] < 2 ^ 24 := by have := PBUtil.leNat_lt [a, b, c]; simpa using this
    have hb2 : leNat [e, f, g] < 2 ^ 24 := by have := PBUtil.leNat_lt [e, f, g]; simpa using this
    have hhdr : compHeaderRead src.val = (leNat [a, b, c], d, leNat [e, f, g]) := by
      simp [compHeaderRead, hsrc]
    rw [hcl, hpl] at cf_post
  all_goals
    rw [hhdr] at herr
    simp only at herr
    clear i1_post i2_post i3_post i5_post i6_post i7_post i4_post i8_post compressed_len_post
      uncompressed_len_post seq_id_post
    generalize leNat [a, b, c] = cl at *
    generalize leNat [e, f, g] = pl at *
    split_ifs at cf_post <;> simp_all

/-- `reset_seq_id`: both the compressed and the plain sequence ids become 0. -/
theorem proto.codec.CompPacketCodec.reset_seq_id_eq (self : proto.codec.CompPacketCodec) :
    proto.codec.CompPacketCodec.reset_seq_id self =
      ok { self with comp_seq_id := 0#u8, plain_codec := { self.plain_codec with seq_id := 0#u8 } } := by
  simp [proto.codec.CompPacketCodec.reset_seq_id, proto.codec.PlainPacketCodec.reset_seq_id]

/-- `sync_seq_id`: if no decompressed input is pending (`in_buf` empty, i.e. on a compressed-packet boundary), the plain sequence id becomes the compressed one; otherwise nothing changes. -/
theorem proto.codec.CompPacketCodec.sync_seq_id_eq (self : proto.codec.CompPacketCodec) :
    proto.codec.CompPacketCodec.sync_seq_id self =
      ok (if self.in_buf.val = [] then
            { self with plain_codec := { self.plain_codec with seq_id := self.comp_seq_id } }
          else self) := by
  unfold proto.codec.CompPacketCodec.sync_seq_id
  simp [proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty, alloc.vec.Vec.deref]
  split_ifs <;> rfl

/-- `decode(src, dst, max_allowed_packet)`: total. It never panics, and states the decoder can produce stay valid. It decodes compressed packets from `src` into the internal buffer `in_buf`, and plain packets from `in_buf` into `dst` (see the round-trip, streaming and error statements below).
    The hypotheses: the pending states are valid (`CompState.Valid`, `ChunkState.Valid`; the decoder only produces valid states, but the enum fields are public), and a size bound that rules out `usize` overflow. That bound is stronger than necessary: each compressed packet of at least 7 input bytes can add up to `2^24` bytes to `in_buf`. -/
theorem proto.codec.CompPacketCodec.decode_total (self : proto.codec.CompPacketCodec)
    (hc : (CompState.of self.comp_decoder).Valid) (hp : (ChunkState.of self.plain_codec.chunk_decoder).Valid)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (h : 2 ^ 25 * (self.in_buf.val.length + src.val.length + dst.val.length + 1) ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ _ c' _ _ =>
      (CompState.of c'.comp_decoder).Valid ∧ (ChunkState.of c'.plain_codec.chunk_decoder).Valid ⦄ := by
  sorry

/-- Pipelined plain packets. Take a decoder whose chunk reader is idle and whose decompressed buffer `in_buf` starts with the chunks of a payload `p` (`frame`, from the plain sequence id), followed by anything (`rest`, e.g. the next packet). It returns `Ok(true)` with exactly `p` in `dst`, leaving `rest` in `in_buf`. It reads nothing from `src`. The compressed reader and sequence id, `out_buf`, both flate2 streams and the level are unchanged, and the plain sequence id is advanced by the number of chunks. -/
theorem proto.codec.CompPacketCodec.decode_buffered (self : proto.codec.CompPacketCodec)
    (hidle : self.plain_codec.chunk_decoder = .Idle) (p rest : List U8)
    (hin : self.in_buf.val = frame self.plain_codec.seq_id.val p ++ rest)
    (src dst : proto.codec.buf_model.VecBuf) (hdst : dst.val = []) (max : Usize) (hmax : p.length ≤ max.val)
    (h : self.in_buf.val.length + 2 ^ 24 ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Ok true ∧ dst'.val = p ∧ c'.in_buf.val = rest ∧ src' = src ∧
      c'.comp_seq_id = self.comp_seq_id ∧ c'.comp_decoder = self.comp_decoder ∧
      c'.plain_codec.seq_id = byte (self.plain_codec.seq_id.val + frameCount p.length) ∧
      c'.plain_codec.chunk_decoder = .Idle ∧ c'.out_buf = self.out_buf ∧ c'.deflater = self.deflater ∧
      c'.inflater = self.inflater ∧ c'.level = self.level ⦄ := by
  rw [proto.codec.CompPacketCodec.decode]
  have hne : ¬ (alloc.vec.Vec.deref self.in_buf).length = 0 := by
    have : (frame self.plain_codec.seq_id.val p).length > 0 := by
      rw [frame_length]; simp [frameCount]
    simp [Slice.length, alloc.vec.Vec.deref, hin]; intro e
    rw [e] at this; simp at this
  simp only [proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty,
    Std.bind_ok, hne, decide_false, Bool.false_eq_true, ↓reduceIte, lift]
  have hdl : alloc.vec.Vec.length dst = 0 := by simp [alloc.vec.Vec.length, hdst]
  obtain ⟨⟨r, ppc, vb, dst1⟩, hv, hp⟩ := PBUtil.spec_eq_ok
    (proto.codec.PlainPacketCodec.decode_frame self.plain_codec hidle p rest self.in_buf dst hin hdst max hmax
      (some (core.num.U8.wrapping_sub self.comp_seq_id 1#u8)) (by have := h; simp [alloc.vec.Vec.length] at *; omega))
  rw [hv]
  simp only [WP.uncurry'_pair] at hp
  obtain ⟨rfl, hseq, hcd, hvb, hd1⟩ := hp
  simp [core.result.Result.Insts.CoreOpsTry.branch, proto.codec.trusted.vec_capacity,
    proto.codec.COMP_CODEC_SHRINK_THRESHOLD]
  split_ifs with he
  · step*
    all_goals simp_all [alloc.vec.Vec.new, alloc.vec.Vec.deref]
  · simp [hd1, hvb, hseq, hcd]

/-- Headline round trip (decoding). Take a decoder with nothing pending (`in_buf` empty, both readers idle). Feed it any compressed stream (`CompStreamOf`) whose pieces carry the chunks of a payload `p` followed by `rest`, then anything (`tail`). The chunks are `frame`, from the decoder's plain sequence id; the packets' sequence ids start at the decoder's compressed one.
    The pieces may be cut anywhere (non-empty, at most `min(2^24 - 1, max_allowed_packet)` bytes), each stored or deflated by flate2. The payload's chunks must end in the last piece, so `rest` is the start of what comes next.
    The decoder gives back exactly `p` with `Ok(true)`: the whole stream is consumed (`tail` left), and `rest` stays in `in_buf`. The compressed sequence id is advanced by the number of packets, the plain one by the number of chunks, and both readers are idle.
    Deflated pieces are read back by `Trusted.inflate_deflate`, with any inflate stream. A deflated piece is covered only when it is flate2/miniz_oxide's own output; a server's zlib stream is covered only by `decode_total` and the error statements. -/
theorem proto.codec.CompPacketCodec.decode_compStream (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle ∧ self.plain_codec.chunk_decoder = .Idle)
    (p rest tail out : List U8) (pieces : List (List U8))
    (hpieces : pieces.flatten = frame self.plain_codec.seq_id.val p ++ rest)
    (hlast : pieces.dropLast.flatten.length < (frame self.plain_codec.seq_id.val p).length)
    (max : Usize) (hsize : ∀ c ∈ pieces, c ≠ [] ∧ c.length ≤ Nat.min maxPayloadLen max.val)
    (hstream : CompStreamOf self.comp_seq_id.val pieces out)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = out ++ tail) (hdst : dst.val = [])
    (hmax : p.length ≤ max.val)
    (h : 2 ^ 25 * (src.val.length + 1) ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Ok true ∧ dst'.val = p ∧ src'.val = tail ∧ c'.in_buf.val = rest ∧
      c'.comp_seq_id = byte (self.comp_seq_id.val + pieces.length) ∧
      c'.plain_codec.seq_id = byte (self.plain_codec.seq_id.val + frameCount p.length) ∧
      c'.comp_decoder = .Idle ∧ c'.plain_codec.chunk_decoder = .Idle ⦄ := by
  obtain ⟨hib, hcd, hpcd⟩ := hfresh
  obtain ⟨zs, hF, hout⟩ := hstream
  have hzl : pieces.length = zs.length := hF.length_eq
  have hn : pieces ≠ [] := by
    intro e; rw [e] at hpieces
    have := congrArg List.length hpieces; simp [frame_length, frameCount] at this
  have hnl : 0 < pieces.length := List.length_pos_iff.mpr hn
  have hflat : pieces.flatten.length ≤ pieces.length * 2 ^ 24 := by
    have hall : ∀ c ∈ pieces, c.length ≤ 2 ^ 24 := fun c hc => by
      have := (hsize c hc).2
      have : Nat.min maxPayloadLen max.val = min (2 ^ 24 - 1) max.val := rfl
      omega
    clear hpieces hlast hsize hF hout hzl hn hnl
    induction pieces with
    | nil => simp
    | cons c cs ih =>
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      have := hall c (by simp); have := ih (fun c' h => hall c' (by simp [h])); rw [Nat.succ_mul]; omega
  have hpk : 7 * pieces.length ≤ out.length := by
    rw [hout]; exact CompCodec.compPackets_length_ge _ _ _ hzl
  have hU : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  have hsl : src.val.length = out.length + tail.length := by rw [hsrc]; simp
  have hrm := CompCodec.run_main pieces zs hF self.plain_codec.seq_id p rest tail hpieces hlast max hsize hmax
    self.comp_seq_id.val (by omega) pieces.length 0 self src dst (by simp) (by simp)
    (by apply UScalar.eq_of_val_eq; rw [PBUtil.byte_val]; have := self.comp_seq_id.hBounds; simp at this ⊢)
    (by rw [hib, hdst, hpcd]; rfl)
    (by intro inf d; rw [hcd, hsrc, hout]; rfl)
    (by rw [hcd]; trivial) (by rw [hpcd]; trivial) (by rw [hib, hdst]; simp)
    (by intro h0; omega)
  exact hrm

/-- Streaming. On a strict prefix of such a compressed stream (as in `decode_compStream`), a decoder with nothing pending reports that more input is needed (`Ok(false)`), never an error. Plain chunks completed so far may already be in `dst`. -/
theorem proto.codec.CompPacketCodec.decode_prefix (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle ∧ self.plain_codec.chunk_decoder = .Idle)
    (p rest out : List U8) (pieces : List (List U8))
    (hpieces : pieces.flatten = frame self.plain_codec.seq_id.val p ++ rest)
    (hlast : pieces.dropLast.flatten.length < (frame self.plain_codec.seq_id.val p).length)
    (max : Usize) (hsize : ∀ c ∈ pieces, c ≠ [] ∧ c.length ≤ Nat.min maxPayloadLen max.val)
    (hstream : CompStreamOf self.comp_seq_id.val pieces out)
    (k : Nat) (hk : k < out.length)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = out.take k) (hdst : dst.val = [])
    (hmax : p.length ≤ max.val)
    (h : 2 ^ 25 * (out.length + 1) ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r _ _ _ =>
      r = .Ok false ⦄ := by
  sorry

/-- Resumption. Decode a strict prefix of such a compressed stream (`Ok(false)`). Then call `decode` again with the returned codec and output, on what the first call left of the input followed by the rest of the stream (and anything after). This completes the packet exactly as in `decode_compStream`. -/
theorem proto.codec.CompPacketCodec.decode_resume (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle ∧ self.plain_codec.chunk_decoder = .Idle)
    (p rest tail out : List U8) (pieces : List (List U8))
    (hpieces : pieces.flatten = frame self.plain_codec.seq_id.val p ++ rest)
    (hlast : pieces.dropLast.flatten.length < (frame self.plain_codec.seq_id.val p).length)
    (max : Usize) (hsize : ∀ c ∈ pieces, c ≠ [] ∧ c.length ≤ Nat.min maxPayloadLen max.val)
    (hstream : CompStreamOf self.comp_seq_id.val pieces out)
    (k : Nat) (hk : k < out.length)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = out.take k) (hdst : dst.val = [])
    (hmax : p.length ≤ max.val)
    (h : 2 ^ 25 * (out.length + tail.length + 1) ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r1 c1 src1 dst1 =>
      r1 = .Ok false ∧
      ∀ src2 : proto.codec.buf_model.VecBuf, src2.val = src1.val ++ out.drop k ++ tail →
        (proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut c1 src2 dst1 max ⦃ r c' src' dst' =>
          r = .Ok true ∧ dst'.val = p ∧ src'.val = tail ∧ c'.in_buf.val = rest ∧
          c'.comp_seq_id = byte (self.comp_seq_id.val + pieces.length) ∧
          c'.plain_codec.seq_id = byte (self.plain_codec.seq_id.val + frameCount p.length) ∧
          c'.comp_decoder = .Idle ∧ c'.plain_codec.chunk_decoder = .Idle ⦄) ⦄ := by
  sorry

/-- Out of sync. A decoder with nothing pending, given a compressed packet (as the crate writes them) whose sequence id `s` is not the expected one, fails with `PacketsOutOfSync`; the compressed sequence id is unchanged. **Quirk:** the packet has been consumed, and its plain bytes have been kept in `in_buf`, so a later call would decode them. -/
theorem proto.codec.CompPacketCodec.decode_out_of_sync (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle ∧ self.plain_codec.chunk_decoder = .Idle)
    (s : U8) (hs : s ≠ self.comp_seq_id) (chunk : List U8) (zo : Option (List U8))
    (hz : ∀ z, zo = some z → Deflates chunk z) (tail : List U8)
    (src dst : proto.codec.buf_model.VecBuf) (hsrc : src.val = compPacket s.val chunk zo ++ tail)
    (max : Usize) (hmax : chunk.length ≤ Nat.min maxPayloadLen max.val)
    (h : dst.val.length + 2 ^ 25 ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Err .PacketsOutOfSync ∧ c'.comp_seq_id = self.comp_seq_id ∧ c'.comp_decoder = .Idle ∧
      c'.in_buf.val = chunk ∧ src'.val = tail ∧ dst' = dst ⦄ := by
  obtain ⟨hib, hcd, -⟩ := hfresh
  rw [proto.codec.CompPacketCodec.decode]
  have he : (alloc.vec.Vec.deref self.in_buf).length = 0 := by simp [Slice.length, alloc.vec.Vec.deref, hib]
  simp only [proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty,
    Std.bind_ok, he, decide_true, ↓reduceIte]
  obtain ⟨⟨r, cd, src1, vb, o⟩, hv, hp⟩ := PBUtil.spec_eq_ok (CompCodec.decode_with_spec self.comp_decoder src self.in_buf
    max self.inflater (by rw [hcd]; simp only [CompState.of, compStepFits, hib, List.length_nil]; omega))
  rw [hv]
  simp only [WP.uncurry'_pair] at hp
  rw [hcd, hib] at hp
  simp only [CompState.of] at hp
  rw [hsrc, compStep_compPacket _ s.val chunk zo hz tail [] max.val hmax] at hp
  simp only [Prod.mk.injEq, List.nil_append] at hp
  obtain ⟨rfl, hcd', hs1, hvb⟩ := hp
  have hcd'' : cd = .Idle := by cases cd with
    | Idle => rfl
    | Packet a b => cases b <;> simp at hcd'
  subst hcd''
  have hbs : byte s.val = s := by apply UScalar.eq_of_val_eq; rw [PBUtil.byte_val]; have := s.hBounds; simp at this ⊢
  have hne' : ¬ self.comp_seq_id.val = s.val := fun e => hs (UScalar.eq_of_val_eq e).symm
  simp [core.result.Result.Insts.CoreOpsTry.branch, proto.codec.ChunkInfo.seq_id, hbs, hne', hvb, hs1]

/-- A compressed-packet header with a length above `max_allowed_packet` (either length), seen with nothing pending: `PacketTooLarge`, and nothing changes (the codec, input and output are as before). -/
theorem proto.codec.CompPacketCodec.decode_too_large (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize) (h7 : 7 ≤ src.val.length)
    (hbig : max.val < Nat.max (compHeaderRead src.val).1 (compHeaderRead src.val).2.2) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Err .PacketTooLarge ∧ c' = self ∧ src' = src ∧ dst' = dst ⦄ := by
  obtain ⟨hib, hcd⟩ := hfresh
  rw [proto.codec.CompPacketCodec.decode]
  have he : (alloc.vec.Vec.deref self.in_buf).length = 0 := by simp [Slice.length, alloc.vec.Vec.deref, hib]
  simp only [proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty,
    Std.bind_ok, he, decide_true, ↓reduceIte]
  have hU : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  obtain ⟨⟨r, cd, src1, vb, o⟩, hv, hp⟩ := PBUtil.spec_eq_ok (CompCodec.decode_with_spec self.comp_decoder src self.in_buf
    max self.inflater (by rw [hcd]; simp only [CompState.of, compStepFits, hib, List.length_nil]; omega))
  obtain ⟨⟨r', cd', src1', vb', o'⟩, hv', hp'⟩ := PBUtil.spec_eq_ok (decode_idle_hdr_err src self.in_buf
    max self.inflater h7 (Or.inl hbig))
  rw [hcd] at hv
  rw [hv] at hv'
  simp only [ok.injEq, Prod.mk.injEq] at hv'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hv'
  simp only [WP.uncurry'_pair] at hp hp'
  obtain ⟨rfl, rfl, hs, rfl⟩ := hp'
  subst src1
  rw [hcd, hv]
  rw [hib, hcd] at hp
  simp only [CompState.of] at hp
  rcases hh : compHeaderRead src.val with ⟨cl, sq, pl⟩
  rw [hh] at hbig
  simp only at hbig
  rw [CompCodec.compStep_idle_hdr _ _ _ _ _ _ _ h7 hh] at hp
  simp only [hbig, ↓reduceIte, Prod.mk.injEq] at hp
  obtain ⟨rfl, -, -, -⟩ := hp
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  rw [← hcd]

/-- A compressed-packet header with compressed length 0 but a non-zero uncompressed length, within `max_allowed_packet`, seen with nothing pending: `BadCompressedPacketHeader`, and nothing changes. -/
theorem proto.codec.CompPacketCodec.decode_bad_header (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize) (h7 : 7 ≤ src.val.length)
    (hcl : (compHeaderRead src.val).1 = 0) (hpl : (compHeaderRead src.val).2.2 ≠ 0)
    (hmax : (compHeaderRead src.val).2.2 ≤ max.val) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Err .BadCompressedPacketHeader ∧ c' = self ∧ src' = src ∧ dst' = dst ⦄ := by
  obtain ⟨hib, hcd⟩ := hfresh
  rw [proto.codec.CompPacketCodec.decode]
  have he : (alloc.vec.Vec.deref self.in_buf).length = 0 := by simp [Slice.length, alloc.vec.Vec.deref, hib]
  simp only [proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty,
    Std.bind_ok, he, decide_true, ↓reduceIte]
  have hU : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  obtain ⟨⟨r, cd, src1, vb, o⟩, hv, hp⟩ := PBUtil.spec_eq_ok (CompCodec.decode_with_spec self.comp_decoder src self.in_buf
    max self.inflater (by rw [hcd]; simp only [CompState.of, compStepFits, hib, List.length_nil]; omega))
  obtain ⟨⟨r', cd', src1', vb', o'⟩, hv', hp'⟩ := PBUtil.spec_eq_ok (decode_idle_hdr_err src self.in_buf
    max self.inflater h7 (Or.inr ⟨hcl, hpl⟩))
  rw [hcd] at hv
  rw [hv] at hv'
  simp only [ok.injEq, Prod.mk.injEq] at hv'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hv'
  simp only [WP.uncurry'_pair] at hp hp'
  obtain ⟨rfl, rfl, hs, rfl⟩ := hp'
  subst src1
  rw [hcd, hv]
  rw [hib, hcd] at hp
  simp only [CompState.of] at hp
  rcases hh : compHeaderRead src.val with ⟨cl, sq, pl⟩
  rw [hh] at hcl hpl hmax
  simp only at hcl hpl hmax
  rw [CompCodec.compStep_idle_hdr _ _ _ _ _ _ _ h7 hh] at hp
  have hmx : ¬ max.val < Nat.max 0 pl := by
    have : Nat.max 0 pl = pl := Nat.zero_max pl
    omega
  simp only [hcl] at hp
  simp only [hmx, hpl, ↓reduceIte, Prod.mk.injEq] at hp
  obtain ⟨rfl, -, -, -⟩ := hp
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  rw [← hcd]

/-- Inflate failure. A whole compressed packet (non-zero lengths within `max_allowed_packet`) whose payload the decoder's inflate stream fails to inflate to the declared length, seen with nothing pending, gives `Err(Io(e))` with flate2's error. **Quirk:** the 7 header bytes have been consumed, but the packet reader stays in the pending state of that header. A later call would therefore read the payload's bytes as if a header still preceded them, unless the codec is discarded (as callers do after an error). -/
theorem proto.codec.CompPacketCodec.decode_inflate_error (self : proto.codec.CompPacketCodec)
    (hfresh : self.in_buf.val = [] ∧ self.comp_decoder = .Idle)
    (src dst : proto.codec.buf_model.VecBuf) (max : Usize) (e : core.io.error.Error)
    (h7 : 7 + (compHeaderRead src.val).1 ≤ src.val.length)
    (hcl : (compHeaderRead src.val).1 ≠ 0) (hpl : (compHeaderRead src.val).2.2 ≠ 0)
    (hmax : Nat.max (compHeaderRead src.val).1 (compHeaderRead src.val).2.2 ≤ max.val)
    (hinf : inflateList (self.inflater.getD Trusted.decompressNew)
      ((src.val.drop 7).take (compHeaderRead src.val).1) (compHeaderRead src.val).2.2 = .Err e)
    (h : 2 ^ 25 ≤ Usize.max) :
    proto.codec.CompPacketCodec.decode proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.CoreConvertAsRefSliceU8 proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut self src dst max ⦃ r c' src' dst' =>
      r = .Err (.Io e) ∧ c'.comp_seq_id = self.comp_seq_id ∧ c'.in_buf.val = [] ∧
      CompState.of c'.comp_decoder =
        .packet (compHeaderRead src.val).2.1 (compHeaderRead src.val).1 (some (compHeaderRead src.val).2.2) ∧
      src'.val = src.val.drop 7 ∧ dst' = dst ⦄ := by
  obtain ⟨hib, hcd⟩ := hfresh
  rw [proto.codec.CompPacketCodec.decode]
  have he : (alloc.vec.Vec.deref self.in_buf).length = 0 := by simp [Slice.length, alloc.vec.Vec.deref, hib]
  simp only [proto.codec.buf_model.VecBuf.Insts.CoreOpsDerefDerefSliceU8.deref, core.slice.Slice.is_empty,
    Std.bind_ok, he, decide_true, ↓reduceIte]
  obtain ⟨⟨r, cd, src1, vb, o⟩, hv, hp⟩ := PBUtil.spec_eq_ok (CompCodec.decode_with_spec self.comp_decoder src self.in_buf
    max self.inflater (by rw [hcd]; simp only [CompState.of, compStepFits, hib, List.length_nil]; omega))
  rw [hv]
  simp only [WP.uncurry'_pair] at hp
  rw [hcd, hib] at hp
  simp only [CompState.of] at hp
  have hl7 : 7 ≤ src.val.length := by omega
  rcases hh : compHeaderRead src.val with ⟨cl, sq, pl⟩
  rw [hh] at h7 hcl hpl hmax hinf
  simp only at h7 hcl hpl hmax hinf
  rw [CompCodec.compStep_idle_hdr _ _ _ _ _ _ _ hl7 hh] at hp
  have hmx : ¬ max.val < Nat.max cl pl := by omega
  simp only [hmx, hcl, hpl, ↓reduceIte, compStep, h7, hinf, Prod.mk.injEq] at hp
  obtain ⟨rfl, hcd', hs1, hvb⟩ := hp
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from, hvb, hs1]
  exact hcd'

/-- `encode(packet, dst, max_allowed_packet)`, whenever it does not panic (`max_allowed_packet ≠ 0` or the packet is too large; level at most 10, a kept deflate stream, or no piece long enough to deflate).
    * `PacketTooLarge` if the packet is longer than `max_allowed_packet`; nothing changes.
    * Otherwise the packet's chunks (`frame`, from the plain sequence id) are appended to `out_buf`, and `out_buf` is compressed into `dst` (`CompEncoding`, from the compressed sequence id; see `compress_with_spec`). The packet is consumed.
      - On `Ok`: `out_buf` is emptied, the compressed sequence id is advanced by the number of compressed packets, and the plain sequence id is set to it (synchronised as in the server's `net_serv.cc`).
      - On `Err`: deflating failed (an `Io` error). **Quirk:** the plain sequence id has already advanced but the compressed one has not. The pieces before the failure are already in `dst` as compressed packets, and also still in `out_buf`. So the next `encode` sends them a second time, with the same compressed sequence ids.
    The reading side (`in_buf`, the readers, the inflate stream) and the level are untouched. The deflate stream is not described. -/
theorem proto.codec.CompPacketCodec.encode_spec (self : proto.codec.CompPacketCodec) (packet dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (hmax : max.val ≠ 0 ∨ max.val < packet.val.length)
    (hlvl : self.deflater ≠ none ∨ self.level.level.val ≤ 10 ∨
      Nat.min (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val).length < minCompressLength)
    (h : self.out_buf.val.length + (frame self.plain_codec.seq_id.val packet.val).length ≤ Usize.max ∧
      dst.val.length + 8 * (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.CompPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst max ⦃ r c' packet' dst' =>
      if max.val < packet.val.length then
        r = .Err .PacketTooLarge ∧ c' = self ∧ packet' = packet ∧ dst' = dst
      else
        packet'.val = [] ∧ c'.level = self.level ∧ c'.in_buf = self.in_buf ∧
        c'.comp_decoder = self.comp_decoder ∧ c'.inflater = self.inflater ∧
        c'.plain_codec.chunk_decoder = self.plain_codec.chunk_decoder ∧
        match r with
        | .Ok _ =>
          c'.comp_seq_id = byte (self.comp_seq_id.val +
            (chunksOf (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val)).length) ∧
          c'.plain_codec.seq_id = c'.comp_seq_id ∧ c'.out_buf.val = [] ∧
          ∃ out, CompEncoding (self.deflater.getD (Trusted.compressNew self.level)) self.level.level.val (compChunkSize max.val) self.comp_seq_id.val
              (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val) out ∧
            dst'.val = dst.val ++ out
        | .Err e =>
          (∃ ioe, e = .Io ioe) ∧ c'.comp_seq_id = self.comp_seq_id ∧
          c'.plain_codec.seq_id = byte (self.plain_codec.seq_id.val + frameCount packet.val.length) ∧
          c'.out_buf.val = self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val ∧
          ∃ k out, k < (chunksOf (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val)).length ∧
            self.level.level.val ≠ 0 ∧
            minCompressLength ≤ ((chunksOf (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val)).getD k []).length ∧
            CompPacketsOf (self.deflater.getD (Trusted.compressNew self.level)) self.level.level.val self.comp_seq_id.val
              ((chunksOf (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val)).take k) out ∧
            dst'.val = dst.val ++ out ⦄ := by
  unfold proto.codec.CompPacketCodec.encode
  have hpe := proto.codec.PlainPacketCodec.encode_spec self.plain_codec packet self.out_buf max
    (by by_cases hm : max.val < packet.val.length
        · exact Or.inl hm
        · exact Or.inr (by have := h.1; omega))
  obtain ⟨⟨r1, ppc, packet1, vb⟩, hv, hp⟩ := PBUtil.spec_eq_ok hpe
  rw [hv]
  simp only [WP.uncurry'_pair] at hp
  have e0 : alloc.vec.Vec.length packet = packet.val.length := rfl
  rw [e0] at hp
  by_cases hm : max.val < packet.val.length
  · simp only [hm, ↓reduceIte] at hp ⊢
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  · simp only [hm, ↓reduceIte] at hp ⊢
    obtain ⟨rfl, rfl, hpk, hvb⟩ := hp
    have hmax0 : max.val ≠ 0 := by rcases hmax with h0 | h0 <;> omega
    have hne : vb.val ≠ [] := by
      rw [hvb]; intro e
      have := congrArg List.length e
      simp [frame_length, frameCount] at this
    have hcw := proto.codec.compress_with_spec self.comp_seq_id self.level self.deflater max vb dst hne hmax0
      (by rw [hvb]; exact hlvl) (by rw [hvb]; exact h.2)
    obtain ⟨⟨r2, o, vb1, dst1⟩, hv2, hp2⟩ := PBUtil.spec_eq_ok hcw
    simp only [WP.uncurry'_pair] at hp2
    rw [hvb] at hp2
    cases r2 with
    | Ok val =>
      obtain ⟨hval, hvb1, out, henc, hdst1⟩ := hp2
      simp [core.result.Result.Insts.CoreOpsTry.branch, hv2, proto.codec.trusted.vec_capacity,
        proto.codec.COMP_CODEC_SHRINK_THRESHOLD]
      step*
    | Err e =>
      obtain ⟨⟨ioe, rfl⟩, rfl, k, out, hk, hl0, hbig, hcp, hdst1⟩ := hp2
      simp [core.result.Result.Insts.CoreOpsTry.branch, hv2, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      refine ⟨hpk, hvb, k, hk, hl0, ?_, out, hcp, hdst1⟩
      simpa [List.getD_eq_getElem?_getD] using hbig

/-- **Upstream defect:** a panic instead of an error on a degenerate setting (the server's minimum `max_allowed_packet` is 1024). With `max_allowed_packet = 0`, encoding an empty packet panics. The empty packet passes the size check, its one empty chunk (4 bytes) goes to `out_buf`, and compressing it calls `chunks(0)`. (A non-empty packet gets `PacketTooLarge` instead.) -/
theorem proto.codec.CompPacketCodec.encode_max_zero (self : proto.codec.CompPacketCodec) (packet dst : proto.codec.buf_model.VecBuf)
    (hp : packet.val = []) (h : self.out_buf.val.length + 4 ≤ Usize.max) :
    proto.codec.CompPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst 0#usize = fail .panic := by
  sorry

/-- With no deflate stream yet and a level above 10, `encode` of a packet within `max_allowed_packet` panics when the first piece of `out_buf` (after the packet's chunks are added) has at least `minCompressLength` bytes. This is flate2's `debug_assert!(level <= 10)` in `Compress::new` (`src/ffi/miniz_oxide.rs:153`): debug builds only, no panic in release. -/
theorem proto.codec.CompPacketCodec.encode_level_panic (self : proto.codec.CompPacketCodec) (packet dst : proto.codec.buf_model.VecBuf) (max : Usize)
    (hd : self.deflater = none) (hlvl : 10 < self.level.level.val) (hp : packet.val.length ≤ max.val)
    (hbig : minCompressLength ≤
      Nat.min (compChunkSize max.val) (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val).length)
    (h : self.out_buf.val.length + (frame self.plain_codec.seq_id.val packet.val).length ≤ Usize.max ∧
      dst.val.length + 8 * (self.out_buf.val ++ frame self.plain_codec.seq_id.val packet.val).length ≤ Usize.max) :
    proto.codec.CompPacketCodec.encode proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBuf proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelPacketBufMut proto.codec.buf_model.VecBuf.Insts.Mysql_commonProtoCodecBuf_modelReserve self packet dst max = fail .panic := by
  unfold proto.codec.CompPacketCodec.encode
  have hpe := proto.codec.PlainPacketCodec.encode_spec self.plain_codec packet self.out_buf max
    (Or.inr (by have := h.1; omega))
  obtain ⟨⟨r1, ppc, packet1, vb⟩, hv, hp⟩ := PBUtil.spec_eq_ok hpe
  rw [hv]
  simp only [WP.uncurry'_pair] at hp
  have e0 : alloc.vec.Vec.length packet = packet.val.length := rfl
  rw [e0] at hp
  have hm : ¬ max.val < packet.val.length := by omega
  simp only [hm, ↓reduceIte] at hp
  obtain ⟨rfl, rfl, hpk, hvb⟩ := hp
  have hcs : 512 ≤ compChunkSize max.val := by
    have : minCompressLength = 512 := rfl
    have := le_trans hbig (Nat.min_le_left _ _); omega
  have hmax0 : max.val ≠ 0 := by
    have : compChunkSize max.val = min (2 ^ 24 - 1) max.val := rfl
    omega
  have hne : vb.val ≠ [] := by
    rw [hvb]; intro e
    have := congrArg List.length e
    simp [frame_length, frameCount] at this
  have hpan := proto.codec.compress_with_level_panic self.comp_seq_id self.level max vb dst hne hmax0 hlvl
    (by rw [hvb]; exact hbig)
  simp [core.result.Result.Insts.CoreOpsTry.branch, hd, hpan]

end mysql_common
