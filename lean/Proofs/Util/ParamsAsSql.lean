import Defs
import Proofs.Util.ConvInts
import Proofs.Util.ConvBytesTime

/-! Helper lemmas for the proofs of group ParamsAsSql (`Proofs/Params/*`,
`Proofs/Value/{Escaped,AsSql}.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common.PASUtil

/-! ## Clones -/

theorem list_clone_ok {α : Type} (l : List α) (cl : α → Result α) (h : ∀ x, cl x = ok x) :
    List.clone cl l = ok ⟨l, rfl⟩ := by
  simp only [List.clone]
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.mapM_with_length, ih, h, pure]

theorem vec_u8_clone_eq (v : alloc.vec.Vec U8) : alloc.vec.CloneVec.clone core.clone.CloneU8 v = ok v := by
  simp only [alloc.vec.CloneVec.clone, Slice.clone]
  rw [list_clone_ok _ _ (fun _ => rfl)]
  simp

theorem value_clone_eq (v : value.Value) : value.Value.Insts.CoreCloneClone.clone v = ok v := by
  cases v <;> simp [value.Value.Insts.CoreCloneClone.clone, vec_u8_clone_eq, lift,
    F32.Insts.CoreCloneClone.clone, F64.Insts.CoreCloneClone.clone]

/-! ## Iterators, `From<Vec<_>>` loops -/


theorem next_nil {T : Type} (it : alloc.vec.into_iter.IntoIter T) (h : it.val = []) :
    alloc.vec.into_iter.IteratorIntoIter.next it = ok (none, it) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split <;> simp_all

theorem next_cons {T : Type} (it : alloc.vec.into_iter.IntoIter T) (x : T) (l : List T)
    (h : it.val = x :: l) :
    ∃ it', alloc.vec.into_iter.IteratorIntoIter.next it = ok (some x, it') ∧ it'.val = l := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · simp_all
  · rename_i hd tl heq
    rw [h] at heq; cases heq
    exact ⟨_, rfl, by simp⟩

theorem into_iter_eq {T : Type} (v : alloc.vec.Vec T) :
    ∃ it : alloc.vec.into_iter.IntoIter T, alloc.vec.IntoIteratorVec.into_iter v = ok it ∧ it.val = v.val :=
  ⟨v, rfl, rfl⟩

theorem next_spec {T : Type} (it : alloc.vec.into_iter.IntoIter T) :
    alloc.vec.into_iter.IteratorIntoIter.next it ⦃ o it' =>
      o = it.val.head? ∧ it'.val = it.val.tail ⦄ := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split <;> simp_all [WP.uncurry']

theorem from_vec_loop_spec {T : Type} (inst : core.convert.From value.Value T) (g : T → value.Value) :
    ∀ (l : List T) (iter : alloc.vec.into_iter.IntoIter T) (acc : alloc.vec.Vec value.Value),
    iter.val = l → (∀ t ∈ l, inst.from t = ok (g t)) → acc.length + l.length ≤ Usize.max →
    params.Params.Insts.CoreConvertFromVec.from_loop inst iter acc ⦃ r => r.val = acc.val ++ l.map g ⦄ := by
  intro l
  induction l with
  | nil =>
    intro iter acc hit _ _
    unfold params.Params.Insts.CoreConvertFromVec.from_loop
    rw [loop]
    simp [params.Params.Insts.CoreConvertFromVec.from_loop.body, next_nil iter hit]
  | cons x l ih =>
    intro iter acc hit hg hlen
    unfold params.Params.Insts.CoreConvertFromVec.from_loop
    rw [loop]
    simp only [params.Params.Insts.CoreConvertFromVec.from_loop.body]
    step with next_spec iter as ⟨p, ho, hit'⟩
    obtain ⟨o, it'⟩ := p
    simp only [hit, List.head?_cons, List.tail_cons] at ho hit' ⊢
    subst ho
    step with (show inst.from x ⦃ v => v = g x ⦄ by rw [hg x (by simp)]; simp) as ⟨v, hv⟩
    step as ⟨acc1, hacc1⟩
    have := ih it' acc1 hit' (fun t ht => hg t (by simp [ht])) (by simp_all; omega)
    unfold params.Params.Insts.CoreConvertFromVec.from_loop at this
    apply WP.spec_mono this
    intro r hr
    simp [hr, hacc1, hv]


theorem lookup_eq_none_iff (m : Trusted.ParamsMap) (k : List U8) :
    Trusted.paramsMapLookup m k = none ↔ ∀ e ∈ Trusted.paramsMapEntries m, e.1.val ≠ k := by
  simp [Trusted.paramsMapLookup, List.find?_eq_none]

theorem from_pair_loop_spec {N V : Type}
    (nInst : core.convert.From (alloc.vec.Vec U8) N) (vInst : core.convert.From value.Value V)
    (gn : N → alloc.vec.Vec U8) (gv : V → value.Value) :
    ∀ (l : List (N × V)) (iter : alloc.vec.into_iter.IntoIter (N × V)) (m : Trusted.ParamsMap),
    iter.val = l →
    (∀ e ∈ l, nInst.from e.1 = ok (gn e.1)) →
    (∀ e ∈ l, vInst.from e.2 = ok (gv e.2)) →
    (l.map fun e => (gn e.1).val).Nodup →
    (∀ e ∈ l, ∀ e' ∈ Trusted.paramsMapEntries m, e'.1.val ≠ (gn e.1).val) →
    (Trusted.paramsMapEntries m).length + l.length ≤ Usize.max →
    params.Params.Insts.CoreConvertFromVecPair.from_loop nInst vInst iter m ⦃ r =>
      (Trusted.paramsMapEntries r).Perm
        (l.map (fun e => (gn e.1, gv e.2)) ++ Trusted.paramsMapEntries m) ⦄ := by
  intro l
  induction l with
  | nil =>
    intro iter m hit _ _ _ _ _
    unfold params.Params.Insts.CoreConvertFromVecPair.from_loop
    rw [loop]
    simp only [params.Params.Insts.CoreConvertFromVecPair.from_loop.body]
    step with next_spec iter as ⟨p, ho, hit'⟩
    obtain ⟨o, it'⟩ := p
    simp only [hit, List.head?_nil] at ho ⊢
    subst ho
    simp
  | cons x l ih =>
    intro iter m hit hn hv hnd hfresh hlen
    unfold params.Params.Insts.CoreConvertFromVecPair.from_loop
    rw [loop]
    simp only [params.Params.Insts.CoreConvertFromVecPair.from_loop.body]
    step with next_spec iter as ⟨p, ho, hit'⟩
    obtain ⟨o, it'⟩ := p
    simp only [hit, List.head?_cons, List.tail_cons] at ho hit' ⊢
    subst ho
    obtain ⟨xn, xv⟩ := x
    have hnone : Trusted.paramsMapLookup m (gn xn).val = none :=
      (lookup_eq_none_iff _ _).mpr (hfresh (xn, xv) (by simp))
    step with (show nInst.from xn ⦃ v => v = gn xn ⦄ by rw [hn (xn, xv) (by simp)]; simp) as ⟨nm, hnm⟩
    subst hnm
    step with (show sql_trusted.params_map_contains_key m (alloc.vec.Vec.deref (gn xn)) ⦃ b => b = false ⦄ by
      simp [sql_trusted.params_map_contains_key, alloc.vec.Vec.deref, hnone]) as ⟨b, hb⟩
    subst hb
    step with massert_spec (¬ (false = true)) (by simp) as ⟨hu⟩
    step with (show vInst.from xv ⦃ v => v = gv xv ⦄ by rw [hv (xn, xv) (by simp)]; simp) as ⟨vv, hvv⟩
    subst hvv
    step with (show sql_trusted.params_map_insert m (gn xn) (gv xv) ⦃ _ m1 =>
        m1 = Trusted.paramsMapInsert m (gn xn) (gv xv) ⦄ by
      simp [sql_trusted.params_map_insert]) as ⟨p, hp⟩
    obtain ⟨o1, m1⟩ := p
    simp only at hp ⊢
    subst hp
    apply WP.spec_bind (Pₘ := fun r => r = .cont (it', Trusted.paramsMapInsert m (gn xn) (gv xv)))
      ((WP.spec_ok _).mpr rfl)
    rintro r rfl
    have hE : (Trusted.paramsMapEntries (Trusted.paramsMapInsert m (gn xn) (gv xv))).Perm
        ((gn xn, gv xv) :: Trusted.paramsMapEntries m) :=
      Trusted.paramsMapEntries_insert m (gn xn) (gv xv) hnone (by simp at hlen; omega)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have := ih it' (Trusted.paramsMapInsert m (gn xn) (gv xv)) hit'
      (fun e he => hn e (by simp [he])) (fun e he => hv e (by simp [he])) hnd.2
      (by
        intro e he e' he'
        rcases List.mem_cons.mp (hE.mem_iff.mp he') with h | h
        · subst h; intro heq; exact hnd.1 ⟨e, he, heq.symm⟩
        · exact hfresh e (by simp [he]) e' h)
      (by rw [hE.length_eq]; simp at hlen ⊢; omega)
    unfold params.Params.Insts.CoreConvertFromVecPair.from_loop at this
    refine WP.spec_mono this ?_
    intro r hr
    simp only [List.map_cons]
    exact hr.trans ((List.Perm.append_left _ hE).trans List.perm_middle)


theorem from_pair_loop_dup {N V : Type}
    (nInst : core.convert.From (alloc.vec.Vec U8) N) (vInst : core.convert.From value.Value V)
    (gn : N → alloc.vec.Vec U8) (gv : V → value.Value) :
    ∀ (l : List (N × V)) (iter : alloc.vec.into_iter.IntoIter (N × V)) (m : Trusted.ParamsMap),
    iter.val = l →
    (∀ e ∈ l, nInst.from e.1 = ok (gn e.1)) →
    (∀ e ∈ l, vInst.from e.2 = ok (gv e.2)) →
    ¬ (l.map (fun e => (gn e.1).val) ++ (Trusted.paramsMapEntries m).map (fun e => e.1.val)).Nodup →
    (Trusted.paramsMapEntries m).length + l.length ≤ Usize.max →
    params.Params.Insts.CoreConvertFromVecPair.from_loop nInst vInst iter m = fail .assertionFailure := by
  intro l
  induction l with
  | nil =>
    intro iter m _ _ _ hnd _
    exact absurd (Trusted.paramsMapEntries_keys_nodup m) (by simpa using hnd)
  | cons x l ih =>
    intro iter m hit hn hv hnd hlen
    obtain ⟨xn, xv⟩ := x
    obtain ⟨it', hnx, hit'⟩ := next_cons iter _ _ hit
    unfold params.Params.Insts.CoreConvertFromVecPair.from_loop
    rw [loop]
    simp only
    rw [params.Params.Insts.CoreConvertFromVecPair.from_loop.body]
    simp only [hnx, Std.bind_ok, core.convert.IntoFrom.into]
    simp only [Std.uncurry_apply_pair, hn (xn, xv) (by simp), Std.bind_ok,
      sql_trusted.params_map_contains_key, alloc.vec.Vec.deref, Slice.from_val]
    by_cases hin : (gn xn).val ∈ (Trusted.paramsMapEntries m).map (fun e => e.1.val)
    · have hs : (Trusted.paramsMapLookup m (gn xn).val).isSome = true := by
        cases h : Trusted.paramsMapLookup m (gn xn).val with
        | some _ => rfl
        | none =>
          obtain ⟨e, he, heq⟩ := List.mem_map.mp hin
          exact absurd heq ((lookup_eq_none_iff _ _).mp h e he)
      simp [hs, massert]
    · have hnone : Trusted.paramsMapLookup m (gn xn).val = none := by
        rw [lookup_eq_none_iff]; intro e he heq; exact hin (List.mem_map.mpr ⟨e, he, heq⟩)
      have hE : (Trusted.paramsMapEntries (Trusted.paramsMapInsert m (gn xn) (gv xv))).Perm
          ((gn xn, gv xv) :: Trusted.paramsMapEntries m) :=
        Trusted.paramsMapEntries_insert m (gn xn) (gv xv) hnone (by simp at hlen; omega)
      simp only [hnone, Option.isSome_none, massert, Bool.false_eq_true, not_false_eq_true, ↓reduceIte,
        Std.bind_ok, hv (xn, xv) (by simp), sql_trusted.params_map_insert, Std.uncurry_apply_pair]
      have := ih it' (Trusted.paramsMapInsert m (gn xn) (gv xv)) hit'
        (fun e he => hn e (by simp [he])) (fun e he => hv e (by simp [he]))
        (by
          intro hnd'
          apply hnd
          have hp : (List.map (fun e => (gn e.1).val) l ++ List.map (fun e => e.1.val)
              (Trusted.paramsMapEntries (Trusted.paramsMapInsert m (gn xn) (gv xv)))).Perm
              ((gn xn).val :: (List.map (fun e => (gn e.1).val) l ++
                List.map (fun e => e.1.val) (Trusted.paramsMapEntries m))) :=
            ((List.Perm.append_left _ (hE.map _)).trans List.perm_middle)
          have h2 := hp.nodup_iff.mp hnd'
          simpa using h2)
        (by rw [hE.length_eq]; simp at hlen ⊢; omega)
      unfold params.Params.Insts.CoreConvertFromVecPair.from_loop at this
      simpa using this

/-! ## UTF-8 -/


/-- The UTF-8 bytes of a character. -/
def enc (c : Char) : List U8 := (String.utf8EncodeChar c).map fun b => byte b.toNat

theorem utf8_ofList (cs : List Char) : utf8 (String.ofList cs) = cs.flatMap enc := by
  simp only [utf8, String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.utf8Encode_cons, ByteArray.data_append, Array.toList_append, List.map_append, ih,
      List.utf8Encode_singleton]
    simp [enc]

theorem utf8_eq_flatMap (t : String) : utf8 t = t.toList.flatMap enc := by
  rw [← utf8_ofList, String.ofList_toList]

theorem utf8_append (s t : String) : utf8 (s ++ t) = utf8 s ++ utf8 t := by
  rw [utf8_eq_flatMap, utf8_eq_flatMap, utf8_eq_flatMap, String.toList_append, List.flatMap_append]

theorem enc_ascii (c : Char) (h : c.toNat < 128) : enc c = [byte c.toNat] := by
  rw [enc, String.utf8EncodeChar_eq_singleton (Char.utf8Size_eq_one_iff.mpr (by
    rw [UInt32.le_iff_toNat_le]; exact Nat.le_of_lt_succ h))]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  congr 1
  have : c.val.toNat = c.toNat := rfl
  simp only [UInt32.toNat_toUInt8]
  omega

theorem enc_high (c : Char) (h : 127 < c.toNat) : ∀ b ∈ enc c, 128 ≤ b.val := by
  intro b hb
  simp only [enc, List.mem_map] at hb
  obtain ⟨u, hu, rfl⟩ := hb
  have hlt : u.toNat < 256 := u.toNat_lt
  rw [ConvInts.byte_val _ hlt]
  have hv : 127 < c.val.toNat := h
  simp only [String.utf8EncodeChar] at hu
  split_ifs at hu with h1 h2 h3
  · omega
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> simp only [UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat] <;> omega

theorem isUtf8_append {a b : List U8} (ha : IsUtf8 a) (hb : IsUtf8 b) : IsUtf8 (a ++ b) := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  exact ⟨s ++ t, utf8_append s t⟩

theorem isUtf8_flatMap {α : Type} (g : α → List U8) :
    ∀ (l : List α), (∀ x ∈ l, IsUtf8 (g x)) → IsUtf8 (l.flatMap g)
  | [], _ => ⟨"", rfl⟩
  | x :: l, h => by
    rw [List.flatMap_cons]
    exact isUtf8_append (h x (by simp)) (isUtf8_flatMap g l (fun y hy => h y (by simp [hy])))

theorem isUtf8_single (b : U8) (hb : b.val < 128) : IsUtf8 [b] := by
  refine ⟨String.ofList [Char.ofNat b.val], ?_⟩
  have hc : (Char.ofNat b.val).toNat = b.val := by
    unfold Char.ofNat
    rw [dite_eq_left_of_eq_true (eq_true (by unfold Nat.isValidChar; omega))]
    simp [Char.ofNatAux, Char.toNat]
  rw [utf8_ofList, List.flatMap_cons, List.flatMap_nil, List.append_nil, enc_ascii _ (by omega), hc,
    CBTUtil.byte_val]

theorem isUtf8_ascii (l : List U8) (h : ∀ b ∈ l, b.val < 128) : IsUtf8 l := by
  have : l = l.flatMap (fun b => [b]) := by simp
  rw [this]
  exact isUtf8_flatMap _ l (fun b hb => isUtf8_single b (h b hb))

theorem flatMap_id_of (f : U8 → List U8) (hhi : ∀ b : U8, 128 ≤ b.val → f b = [b]) :
    ∀ (l : List U8), (∀ b ∈ l, 128 ≤ b.val) → l.flatMap f = l
  | [], _ => rfl
  | b :: l, h => by
    rw [List.flatMap_cons, hhi b (h b (by simp)), flatMap_id_of f hhi l (fun x hx => h x (by simp [hx]))]
    rfl

theorem isUtf8_flatMap_bytes (f : U8 → List U8) (hhi : ∀ b : U8, 128 ≤ b.val → f b = [b])
    (hlo : ∀ b : U8, b.val < 128 → IsUtf8 (f b)) (bs : List U8) (h : IsUtf8 bs) :
    IsUtf8 (bs.flatMap f) := by
  obtain ⟨t, rfl⟩ := h
  rw [utf8_eq_flatMap, List.flatMap_assoc]
  apply isUtf8_flatMap
  intro c _
  by_cases hc : c.toNat < 128
  · rw [enc_ascii c hc, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact hlo _ (by rw [ConvInts.byte_val _ (by omega)]; exact hc)
  · rw [flatMap_id_of f hhi _ (enc_high c (by omega))]
    exact ⟨String.ofList [c], by rw [utf8_ofList]; simp⟩

/-! ## `escaped` -/

/-- The escape of one byte in `quoteSql`. -/
def escB (nbe : Bool) (c : U8) : List U8 :=
  if nbe then (if c.val = 39 then [c, c] else [c])
  else if c.val = 0 then [byte 92, byte 48]
  else if c.val = 10 then [byte 92, byte 110]
  else if c.val = 13 then [byte 92, byte 114]
  else if c.val = 26 then [byte 92, byte 90]
  else if c.val = 92 ∨ c.val = 39 ∨ c.val = 34 then [byte 92, c]
  else [c]

theorem quoteSql_eq (nbe : Bool) (s : List U8) :
    quoteSql nbe s = byte 39 :: s.flatMap (escB nbe) ++ [byte 39] := rfl

theorem escB_length (nbe : Bool) (c : U8) : (escB nbe c).length ≤ 2 := by
  unfold escB; split_ifs <;> simp

theorem isUtf8_quoteSql (nbe : Bool) (s : List U8) (h : IsUtf8 s) : IsUtf8 (quoteSql nbe s) := by
  have h39 : IsUtf8 [byte 39] := isUtf8_single _ (by rw [ConvInts.byte_val _ (by omega)]; omega)
  rw [quoteSql_eq, ← List.singleton_append]
  refine isUtf8_append (isUtf8_append h39 ?_) h39
  apply isUtf8_flatMap_bytes _ _ _ s h
  · intro b hb
    unfold escB
    split_ifs <;> first | rfl | omega
  · intro b hb
    apply isUtf8_ascii
    unfold escB
    split_ifs <;> simp [ConvInts.byte_val, hb]

theorem escaped_loop0_spec (input : Slice U8) :
    ∀ (n : Nat) (output : alloc.vec.Vec U8) (i : Usize), input.length - i.val = n → i.val ≤ input.length →
    output.length + ((input.val.drop i.val).flatMap (escB true)).length < Usize.max →
    value.escaped_loop0 input output i ⦃ r => r.val = output.val ++ (input.val.drop i.val).flatMap (escB true) ⦄ := by
  intro n
  induction n with
  | zero =>
    intro output i hn hi hlen
    unfold value.escaped_loop0
    rw [loop]
    simp only
    rw [value.escaped_loop0.body]
    have : ¬ i.val < input.length := by omega
    have hd : input.val.drop i.val = [] := by
      apply List.drop_eq_nil_of_le; simp only [Slice.length] at this; omega
    simp [this, hd]
  | succ n ih =>
    intro output i hn hi hlen
    unfold value.escaped_loop0
    rw [loop]
    simp only
    rw [value.escaped_loop0.body]
    have hlt : i.val < input.length := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp only [Slice.len]; exact hlt))]
    step as ⟨c, hc⟩
    have hdrop : input.val.drop i.val = c :: input.val.drop (i.val + 1) := by
      rw [hc]; exact List.drop_eq_getElem_cons _
    rw [hdrop] at hlen ⊢
    have hesc := escB_length true c
    simp only [List.flatMap_cons, List.length_append] at hlen
    split
    · rename_i h39
      step with alloc.vec.Vec.push_spec output _ (by simp at hlen ⊢; omega) as ⟨o2, ho2⟩
      step with alloc.vec.Vec.push_spec o2 _ (by simp [escB, h39] at hlen; simp [ho2]; omega) as ⟨o3, ho3⟩
      step as ⟨i2, hi2⟩
      have := ih o3 i2 (by omega) (by omega) (by
        have : escB true c = [c, c] := by simp [escB, h39]
        simp [this] at hlen; simp [ho3, ho2, hi2]; omega)
      refine WP.spec_mono this ?_
      intro r hr
      rw [hr, ho3, ho2, hi2]
      simp [escB, h39]
    · rename_i h39
      step with alloc.vec.Vec.push_spec output _ (by simp at hlen ⊢; omega) as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      have h39' : ¬ c.val = 39 := fun h => h39 (by scalar_tac)
      have := ih o2 i2 (by omega) (by omega) (by
        have : escB true c = [c] := by simp [escB, h39']
        simp [this] at hlen; simp [ho2, hi2]; omega)
      refine WP.spec_mono this ?_
      intro r hr
      rw [hr, ho2, hi2]
      simp [escB, h39']

theorem escaped_body1_push (output : alloc.vec.Vec U8) (c : U8)
    (h : output.length + (escB false c).length < Usize.max) :
    (if c = 0#u8
      then
        do
        let output2 ← alloc.vec.Vec.push output 92#u8
        alloc.vec.Vec.push output2 48#u8
      else
        if c = 10#u8
        then
          do
          let output2 ← alloc.vec.Vec.push output 92#u8
          alloc.vec.Vec.push output2 110#u8
        else
          if c = 13#u8
          then
            do
            let output2 ← alloc.vec.Vec.push output 92#u8
            alloc.vec.Vec.push output2 114#u8
          else
            if c = 92#u8
            then
              do
              let output2 ← alloc.vec.Vec.push output 92#u8
              alloc.vec.Vec.push output2 c
            else
              if c = 39#u8
              then
                do
                let output2 ← alloc.vec.Vec.push output 92#u8
                alloc.vec.Vec.push output2 c
              else
                if c = 34#u8
                then
                  do
                  let output2 ← alloc.vec.Vec.push output 92#u8
                  alloc.vec.Vec.push output2 c
                else
                  if c = 26#u8
                  then
                    do
                    let output2 ← alloc.vec.Vec.push output 92#u8
                    alloc.vec.Vec.push output2 90#u8
                  else alloc.vec.Vec.push output c) ⦃ o => o.val = output.val ++ escB false c ⦄ := by
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  case neg =>
    have e1 : c.val ≠ 0 := fun h => h1 (by scalar_tac)
    have e2 : c.val ≠ 10 := fun h => h2 (by scalar_tac)
    have e3 : c.val ≠ 13 := fun h => h3 (by scalar_tac)
    have e4 : c.val ≠ 92 := fun h => h4 (by scalar_tac)
    have e5 : c.val ≠ 39 := fun h => h5 (by scalar_tac)
    have e6 : c.val ≠ 34 := fun h => h6 (by scalar_tac)
    have e7 : c.val ≠ 26 := fun h => h7 (by scalar_tac)
    have he : escB false c = [c] := by simp [escB, e1, e2, e3, e4, e5, e6, e7]
    rw [he] at h ⊢
    step with alloc.vec.Vec.push_spec output _ (by simp at h; omega) as ⟨o2, ho2⟩
    exact ho2
  all_goals
    subst_vars
    simp only [escB] at h ⊢
    simp at h ⊢
    step with alloc.vec.Vec.push_spec output _ (by omega) as ⟨o2, ho2⟩
    step with alloc.vec.Vec.push_spec o2 _ (by simp [ho2]; omega) as ⟨o3, ho3⟩
    simp [ho3, ho2]
    try (refine ⟨?_, ?_⟩ <;> rfl)
    try rfl

theorem escaped_loop1_spec (input : Slice U8) :
    ∀ (n : Nat) (output : alloc.vec.Vec U8) (i : Usize), input.length - i.val = n → i.val ≤ input.length →
    output.length + ((input.val.drop i.val).flatMap (escB false)).length < Usize.max →
    value.escaped_loop1 input output i ⦃ r => r.val = output.val ++ (input.val.drop i.val).flatMap (escB false) ⦄ := by
  intro n
  induction n with
  | zero =>
    intro output i hn hi hlen
    unfold value.escaped_loop1
    rw [loop]
    simp only
    rw [value.escaped_loop1.body]
    have : ¬ i.val < input.length := by omega
    have hd : input.val.drop i.val = [] := by
      apply List.drop_eq_nil_of_le; simp only [Slice.length] at this; omega
    simp [this, hd]
  | succ n ih =>
    intro output i hn hi hlen
    unfold value.escaped_loop1
    rw [loop]
    simp only
    rw [value.escaped_loop1.body]
    have hlt : i.val < input.length := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp only [Slice.len]; exact hlt))]
    step as ⟨c, hc⟩
    have hdrop : input.val.drop i.val = c :: input.val.drop (i.val + 1) := by
      rw [hc]; exact List.drop_eq_getElem_cons _
    rw [hdrop] at hlen ⊢
    simp only [List.flatMap_cons, List.length_append] at hlen
    step with escaped_body1_push output c (by omega) as ⟨o2, ho2⟩
    step as ⟨i2, hi2⟩
    have := ih o2 i2 (by omega) (by omega) (by
      simp only [alloc.vec.Vec.length] at hlen
      simp only [alloc.vec.Vec.length, ho2, hi2, List.length_append]; omega)
    refine WP.spec_mono this ?_
    intro r hr
    rw [hr, ho2, hi2]
    simp

end mysql_common.PASUtil
