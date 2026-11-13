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

/-! ## `as_sql` formatting -/


theorem str_null : sql_trusted.string_from_str (toStr "NULL") = ok "NULL" := by
  unfold sql_trusted.string_from_str
  rw [show String.fromUTF8? (Trusted.bytesOf (toStr "NULL").val) = some "NULL" by decide +kernel]

theorem str_0x : sql_trusted.string_from_str (toStr "0x") = ok "0x" := by
  unfold sql_trusted.string_from_str
  rw [show String.fromUTF8? (Trusted.bytesOf (toStr "0x").val) = some "0x" by decide +kernel]

theorem charOfNat_toNat (n : Nat) (h : n < 128) : (Char.ofNat n).toNat = n := by
  unfold Char.ofNat
  rw [dite_eq_left_of_eq_true (eq_true (by unfold Nat.isValidChar; omega))]
  simp [Char.ofNatAux, Char.toNat]

theorem enc_ofNat (n : Nat) (h : n < 128) : enc (Char.ofNat n) = [byte n] := by
  rw [enc_ascii _ (by rw [charOfNat_toNat n h]; exact h), charOfNat_toNat n h]

theorem toList_pushn (s : String) (c : Char) (n : Nat) :
    (s.pushn c n).toList = s.toList ++ List.replicate n c := by
  rw [String.pushn_eq_repeat_push]
  induction n with
  | zero => simp [Nat.repeat]
  | succ n ih => rw [Nat.repeat, String.toList_push, ih, List.replicate_succ', List.append_assoc]

theorem flatMap_enc_digits (l : List Char) (h : ∀ c ∈ l, c.toNat < 128) :
    l.flatMap enc = l.map (fun c => byte c.toNat) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.flatMap_cons, enc_ascii c (h c (by simp)), ih (fun d hd => h d (by simp [hd]))]
    rfl

theorem utf8_toString_nat (n : Nat) :
    utf8 (toString n) = (Nat.toDigits 10 n).map (fun c => byte c.toNat) := by
  show utf8 (Nat.repr n) = _
  rw [Nat.repr_eq_ofList_toDigits, utf8_ofList, flatMap_enc_digits]
  intro c hc
  have := ConvInts.digit_bounds n c hc
  omega

theorem length_toString_nat (n : Nat) : (toString n).length = (Nat.toDigits 10 n).length := by
  show (Nat.repr n).length = _
  rw [Nat.repr_eq_ofList_toDigits, String.length_ofList]

theorem utf8_padDec (w n : Nat) : utf8 (Trusted.padDec w n) = padDec w n := by
  simp only [Trusted.padDec, padDec]
  rw [utf8_append, utf8_toString_nat, length_toString_nat, utf8_eq_flatMap ("".pushn _ _), toList_pushn]
  simp only [String.toList_empty, List.nil_append, List.length_map]
  congr 1
  induction (w - (Nat.toDigits 10 n).length) with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.flatMap_cons, ih, enc_ascii _ (by decide)]; rfl

theorem utf8_toString_int (n : Int) : utf8 (toString n) = decimalBytes n := by
  rw [← CBTUtil.u8sOf_toUTF8, ConvInts.u8sOf_toString]

theorem enc_hexDigitUpper (n : Nat) (h : n < 16) : enc (Trusted.hexDigitUpper n) = [hexDigit n] := by
  unfold Trusted.hexDigitUpper hexDigit
  split_ifs
  · exact enc_ofNat _ (by omega)
  · exact enc_ofNat _ (by omega)

theorem utf8_hexByteUpper (b : Nat) (hb : b < 256) :
    utf8 (Trusted.hexByteUpper b) = [hexDigit (b / 16), hexDigit (b % 16)] := by
  rw [utf8_eq_flatMap, Trusted.hexByteUpper, String.toList_push, String.toList_singleton]
  simp only [List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [enc_hexDigitUpper _ (by omega), enc_hexDigitUpper _ (by omega)]
  rfl


theorem uscalar_mk_val {ty : UScalarTy} (b : BitVec ty.numBits) : (UScalar.mk b).val = b.toNat := rfl

/-- An unsigned addition that overflows fails with `integerOverflow`. -/
theorem uadd_overflow {ty : UScalarTy} (x y : UScalar ty) (h : 2 ^ ty.numBits ≤ x.val + y.val) :
    x + y = fail .integerOverflow := by
  show UScalar.add x y = _
  simp only [UScalar.add, UScalar.tryMk]
  have := UScalar.tryMkOpt_eq ty (x.val + y.val)
  cases hc : UScalar.tryMkOpt ty (x.val + y.val) with
  | none => rfl
  | some z => rw [hc] at this; exfalso; simp [UScalar.inBounds] at this; omega

/-! ## Map lookups -/


theorem slice_u8_eq_spec (s1 s2 : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s1 s2 ⦃ b => b = true ↔ s1.val = s2.val ⦄ := by
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec _ _ _ ?_)
  · intro b hb; rw [← Slice.eq_iff]; simpa using hb
  · intro x y; simp

theorem lookup_some_iff (m : Trusted.ParamsMap) (k : List U8) (v : value.Value) :
    Trusted.paramsMapLookup m k = some v ↔ ∃ e ∈ Trusted.paramsMapEntries m, e.1.val = k ∧ e.2 = v := by
  unfold Trusted.paramsMapLookup
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, rfl⟩
  · rintro ⟨e, he, hk, rfl⟩
    cases hf : (Trusted.paramsMapEntries m).find? (fun e => e.1.val = k) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simpa using hk) (hf e he)
    | some e' =>
      have he' := List.mem_of_find?_eq_some hf
      have hk' : e'.1.val = k := by simpa using List.find?_some hf
      have := List.inj_on_of_nodup_map (Trusted.paramsMapEntries_keys_nodup m) he' he (hk'.trans hk.symm)
      simp [this]

theorem lookup_ext (m m' : Trusted.ParamsMap) (k : List U8)
    (h : ∀ e, (e ∈ Trusted.paramsMapEntries m ∧ e.1.val = k) ↔ (e ∈ Trusted.paramsMapEntries m' ∧ e.1.val = k)) :
    Trusted.paramsMapLookup m k = Trusted.paramsMapLookup m' k := by
  apply Option.ext
  intro v
  rw [lookup_some_iff, lookup_some_iff]
  constructor
  · rintro ⟨e, he, hk, hv⟩; exact ⟨e, ((h e).mp ⟨he, hk⟩).1, hk, hv⟩
  · rintro ⟨e, he, hk, hv⟩; exact ⟨e, ((h e).mpr ⟨he, hk⟩).1, hk, hv⟩

theorem lookup_remove (m : Trusted.ParamsMap) (k k' : List U8) (hne : k' ≠ k) :
    Trusted.paramsMapLookup (Trusted.paramsMapRemove m k) k' = Trusted.paramsMapLookup m k' := by
  apply lookup_ext
  intro e
  rw [(Trusted.paramsMapEntries_remove m k).mem_iff, List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by rw [h2]; simpa using hne⟩, h2⟩

/-! ## `into_positional` -/

theorem ip_inner_true (ns : Slice (alloc.vec.Vec U8)) (i : Usize) (nm : alloc.vec.Vec U8) (x : Usize) :
    params.Params.into_positional_loop0_loop0 ns i nm true x ⦃ b => b = true ⦄ := by
  unfold params.Params.into_positional_loop0_loop0
  rw [loop]
  simp only
  rw [params.Params.into_positional_loop0_loop0.body]
  split <;> simp

theorem ip_inner_spec (ns : Slice (alloc.vec.Vec U8)) (i : Usize) (nm : alloc.vec.Vec U8) :
    ∀ (n : Nat) (x : Usize), x.val - i.val = n → x.val < ns.length →
    params.Params.into_positional_loop0_loop0 ns i nm false x ⦃ b =>
      b = true ↔ ∃ j, i.val < j ∧ j ≤ x.val ∧ ∃ w, ns.val[j]? = some w ∧ w.val = nm.val ⦄ := by
  intro n
  induction n with
  | zero =>
    intro x hn hx
    unfold params.Params.into_positional_loop0_loop0
    rw [loop]
    simp only
    rw [params.Params.into_positional_loop0_loop0.body]
    have : ¬ x > i := by scalar_tac
    simp only [this, ↓reduceIte, Std.bind_ok, WP.spec_ok, Bool.false_eq_true, false_iff, not_exists,
      not_and]
    intro j h1 h2; omega
  | succ n ih =>
    intro x hn hx
    unfold params.Params.into_positional_loop0_loop0
    rw [loop]
    simp only
    rw [params.Params.into_positional_loop0_loop0.body]
    have hgt : x > i := by scalar_tac
    simp only [hgt, ↓reduceIte, Bool.false_eq_true]
    step as ⟨v, hv⟩
    step with slice_u8_eq_spec (alloc.vec.Vec.deref nm) (alloc.vec.Vec.deref v) as ⟨b, hb⟩
    rw [CBTUtil.vec_deref_val, CBTUtil.vec_deref_val] at hb
    split
    · rename_i hbt
      simp only [Std.bind_ok]
      have := ip_inner_true ns i nm x
      unfold params.Params.into_positional_loop0_loop0 at this
      refine WP.spec_mono this ?_
      intro r hr
      simp only [hr, true_iff]
      exact ⟨x.val, by scalar_tac, le_refl _, v, by simp [hv], (hb.mp hbt).symm⟩
    · rename_i hbf
      step as ⟨x1, hx1⟩
      have := ih x1 (by omega) (by omega)
      unfold params.Params.into_positional_loop0_loop0 at this
      refine WP.spec_mono this ?_
      intro r hr
      rw [hr]
      constructor
      · rintro ⟨j, h1, h2, w, hw1, hw2⟩; exact ⟨j, h1, by omega, w, hw1, hw2⟩
      · rintro ⟨j, h1, h2, w, hw1, hw2⟩
        refine ⟨j, h1, ?_, w, hw1, hw2⟩
        rcases Nat.lt_or_ge j x.val with h | h
        · omega
        · exfalso
          have hj : j = x.val := by omega
          subst hj
          apply hbf
          rw [hb]
          have : ns.val[x.val]? = some v := by simp [hv]
          rw [this] at hw1
          cases hw1
          exact hw2.symm

theorem ip_outer_spec (ns : Slice (alloc.vec.Vec U8)) (m : Trusted.ParamsMap) :
    ∀ (n : Nat) (mp : Trusted.ParamsMap) (pos : alloc.vec.Vec value.Value) (i : Usize),
    ns.length - i.val = n → i.val ≤ ns.length → pos.length = i.val →
    (∀ j (w : alloc.vec.Vec U8), i.val ≤ j → ns.val[j]? = some w →
      Trusted.paramsMapLookup mp w.val = Trusted.paramsMapLookup m w.val) →
    pos.val.map some = (ns.val.take i.val).map (fun n => Trusted.paramsMapLookup m n.val) →
    params.Params.into_positional_loop0 ns mp pos i ⦃ r => match r with
      | .Ok p => ∃ v, p = .Positional v ∧
          v.val.map some = ns.val.map (fun n => Trusted.paramsMapLookup m n.val)
      | .Err e => ((ns.val.drop i.val).find? (fun n => (Trusted.paramsMapLookup m n.val).isNone)).map
          (·.val) = some e.val ⦄ := by
  intro n
  induction n with
  | zero =>
    intro mp pos i hn hi hpos hmp hpv
    unfold params.Params.into_positional_loop0
    rw [loop]
    simp only
    rw [params.Params.into_positional_loop0.body]
    have : ¬ i.val < ns.length := by omega
    have ht : ns.val.take i.val = ns.val := by
      apply List.take_of_length_le; simp only [Slice.length] at this; omega
    split
    · exfalso; scalar_tac
    · simp only [Std.bind_ok, WP.spec_ok]
      exact ⟨pos, rfl, by rw [hpv, ht]⟩
  | succ n ih =>
    intro mp pos i hn hi hpos hmp hpv
    unfold params.Params.into_positional_loop0
    rw [loop]
    simp only
    rw [params.Params.into_positional_loop0.body]
    have hlt : i.val < ns.length := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp only [Slice.len]; exact hlt))]
    step as ⟨nm, hnm⟩
    step as ⟨x, hx⟩
    step with ip_inner_spec ns i nm _ x rfl (by scalar_tac) as ⟨rep, hrep⟩
    have hgi : ns.val[i.val]? = some nm := by simp [hnm]
    have hlk : Trusted.paramsMapLookup mp nm.val = Trusted.paramsMapLookup m nm.val :=
      hmp i.val nm (le_refl _) hgi
    have hdrop : ns.val.drop i.val = nm :: ns.val.drop (i.val + 1) := by
      rw [hnm]; exact List.drop_eq_getElem_cons _
    have htake : ns.val.take (i.val + 1) = ns.val.take i.val ++ [nm] := by
      rw [hnm]; exact List.take_succ_eq_append_getElem _
    have herr : ((ns.val.drop i.val).find? (fun n => (Trusted.paramsMapLookup m n.val).isNone)).map
        (·.val) = some nm.val ∨ Trusted.paramsMapLookup m nm.val ≠ none := by
      cases h : Trusted.paramsMapLookup m nm.val
      · left; rw [hdrop]; simp [h]
      · right; simp
    have hfind : ∀ v, Trusted.paramsMapLookup m nm.val = some v →
        (ns.val.drop i.val).find? (fun n => (Trusted.paramsMapLookup m n.val).isNone) =
        (ns.val.drop (i.val + 1)).find? (fun n => (Trusted.paramsMapLookup m n.val).isNone) := by
      intro v hv; rw [hdrop]; simp [hv]
    split
    · -- repeated
      simp only [sql_trusted.params_map_get, Std.bind_ok, CBTUtil.vec_deref_val, hlk]
      cases hv : Trusted.paramsMapLookup m nm.val with
      | none =>
        simp only [vec_u8_clone_eq, Std.bind_ok, WP.spec_ok]
        rw [hdrop]; simp [hv]
      | some val =>
        simp only [value_clone_eq, Std.bind_ok]
        step with alloc.vec.Vec.push_spec pos val (by scalar_tac) as ⟨pos1, hpos1⟩
        step as ⟨i3, hi3⟩
        have hn3 : ns.length - i3.val = n := by rw [hi3, Nat.sub_add_eq, hn, Nat.add_sub_cancel]
        have hi3' : i3.val ≤ ns.length := by rw [hi3]; exact Nat.succ_le_of_lt hlt
        have := ih mp pos1 i3 hn3 hi3' (by simp [hpos1, hi3]; omega)
          (fun j w hj hw => hmp j w (by omega) hw) (by rw [hi3, htake, hpos1]; simp [hpv, hv])
        unfold params.Params.into_positional_loop0 at this
        refine WP.spec_mono this ?_
        intro r hr
        split at hr
        · exact hr
        · rw [hfind val hv, ← hi3]; exact hr
    · -- not repeated
      rename_i hrf
      have hnot : ∀ j (w : alloc.vec.Vec U8), i.val + 1 ≤ j → ns.val[j]? = some w → w.val ≠ nm.val := by
        intro j w hj hw heq
        apply hrf
        rw [hrep]
        refine ⟨j, by omega, ?_, w, hw, heq⟩
        have : j < ns.val.length := by
          rcases List.getElem?_eq_some_iff.mp hw with ⟨h, _⟩; exact h
        scalar_tac
      step with (show sql_trusted.params_map_remove mp (alloc.vec.Vec.deref nm) ⦃ o mp1 =>
          o = Trusted.paramsMapLookup m nm.val ∧ mp1 = Trusted.paramsMapRemove mp nm.val ⦄ by
        simp [sql_trusted.params_map_remove, CBTUtil.vec_deref_val, hlk]) as ⟨p, hp1, hp2⟩
      obtain ⟨o, mp1⟩ := p
      simp only at hp1 hp2 ⊢
      subst hp1 hp2
      cases hv : Trusted.paramsMapLookup m nm.val with
      | none =>
        simp only [vec_u8_clone_eq, Std.bind_ok]
        rw [hdrop]; simp [hv]
      | some val =>
        step with alloc.vec.Vec.push_spec pos val (by scalar_tac) as ⟨pos1, hpos1⟩
        step as ⟨i3, hi3⟩
        have hn3 : ns.length - i3.val = n := by rw [hi3, Nat.sub_add_eq, hn, Nat.add_sub_cancel]
        have hi3' : i3.val ≤ ns.length := by rw [hi3]; exact Nat.succ_le_of_lt hlt
        have := ih (Trusted.paramsMapRemove mp nm.val) pos1 i3 hn3 hi3'
          (by simp [hpos1, hi3]; omega)
          (fun j w hj hw => by
            rw [lookup_remove _ _ _ (hnot j w (by omega) hw)]; exact hmp j w (by omega) hw)
          (by rw [hi3, htake, hpos1]; simp [hpv, hv])
        unfold params.Params.into_positional_loop0 at this
        refine WP.spec_mono this ?_
        intro r hr
        split at hr
        · exact hr
        · rw [hfind val hv, ← hi3]; exact hr


/-! ## `sort_indexes` (insertion sort) -/

/-- Sorted by value. -/
abbrev SortedV (l : List Usize) : Prop := l.Pairwise (fun a b => a.val ≤ b.val)

theorem swap_adj_spec (s : Slice Usize) (i j : Usize) (A : List Usize) (a x : Usize) (R : List Usize)
    (hs : s.val = A ++ a :: x :: R) (hA : A.length = i.val) (hij : i.val + 1 = j.val) :
    core.slice.Slice.swap s i j ⦃ s' => s'.val = A ++ x :: a :: R ⦄ := by
  have hlen : s.length = A.length + 2 + R.length := by simp [Slice.length, hs]; omega
  unfold core.slice.Slice.swap
  step with Slice.index_usize_spec s i (by omega) as ⟨av, hav⟩
  step with Slice.index_usize_spec s j (by omega) as ⟨bv, hbv⟩
  step with Slice.update_spec s i bv (by omega) as ⟨s1, hs1⟩
  step with Slice.update_spec s1 j av (by rw [hs1]; simp [Slice.length] at hlen ⊢; omega) as ⟨s2, hs2⟩
  have ha : av = a := by rw [hav]; simp [hs, ← hA]
  have hb : bv = x := by rw [hbv]; simp [hs, ← hij, ← hA]
  rw [hs2, hs1, ha, hb]
  simp only [Slice.set_val_eq, hs, ← hA]
  rw [List.set_append_right _ _ (by omega), List.set_append_right _ _ (by omega)]
  simp [← hij, ← hA]

theorem sort_inner_spec : ∀ (n : Nat) (v : Slice Usize) (j : Usize) (A : List Usize) (x : Usize)
    (B C : List Usize), j.val = n → v.val = A ++ x :: (B ++ C) → A.length = j.val →
    SortedV (A ++ B) → (∀ b ∈ B, x.val < b.val) →
    params.sort_indexes_loop0_loop0 v j ⦃ r => ∃ L, r.val = L ++ C ∧ SortedV L ∧
      L.Perm (x :: (A ++ B)) ⦄ := by
  intro n
  induction n with
  | zero =>
    intro v j A x B C hj hv hA hs hB
    have hA0 : A = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hA0
    unfold params.sort_indexes_loop0_loop0
    rw [loop]
    simp only
    rw [params.sort_indexes_loop0_loop0.body]
    have : ¬ j > 0#usize := by scalar_tac
    simp only [this, ↓reduceIte, Std.bind_ok, WP.spec_ok]
    refine ⟨x :: B, by simp [hv], ?_, List.Perm.refl _⟩
    simp only [List.nil_append] at hs
    exact List.pairwise_cons.mpr ⟨fun b hb => Nat.le_of_lt (hB b hb), hs⟩
  | succ n ih =>
    intro v j A x B C hj hv hA hs hB
    obtain ⟨A', a, rfl⟩ : ∃ A' a, A = A' ++ [a] := by
      rcases List.eq_nil_or_concat A with h | ⟨L, b, h⟩
      · subst h; simp at hA; omega
      · exact ⟨L, b, by simpa using h⟩
    unfold params.sort_indexes_loop0_loop0
    rw [loop]
    simp only
    rw [params.sort_indexes_loop0_loop0.body]
    have hgt : j > 0#usize := by scalar_tac
    simp only [hgt, ↓reduceIte]
    simp only [List.length_append, List.length_singleton] at hA
    have hvl : v.length = A'.length + 2 + B.length + C.length := by
      simp [Slice.length, hv]; omega
    step as ⟨i, hi⟩
    step with Slice.index_usize_spec v i (by scalar_tac) as ⟨i1, hi1⟩
    step with Slice.index_usize_spec v j (by scalar_tac) as ⟨i2, hi2⟩
    have hi1' : i1 = a := by rw [hi1]; simp [hv, hi, ← hA]
    have hi2' : i2 = x := by rw [hi2]; simp [hv, ← hA]
    subst hi1' hi2'
    split
    · rename_i hax
      step with swap_adj_spec v i j A' i1 i2 (B ++ C) (by simp [hv]) (by scalar_tac) (by scalar_tac)
        as ⟨v1, hv1⟩
      have := ih v1 i A' i2 (i1 :: B) C (by scalar_tac) (by simp [hv1]) (by scalar_tac)
        (by simpa using hs) (by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · scalar_tac
          · exact hB b hb)
      unfold params.sort_indexes_loop0_loop0 at this
      refine WP.spec_mono this ?_
      rintro r ⟨L, h1, h2, h3⟩
      refine ⟨L, h1, h2, h3.trans ?_⟩
      simp only [List.append_assoc, List.singleton_append]
      exact List.Perm.refl _
    · rename_i hax
      simp only [Std.bind_ok, WP.spec_ok]
      refine ⟨A' ++ [i1] ++ i2 :: B, by simp [hv], ?_, List.perm_middle⟩
      unfold SortedV at hs ⊢
      rw [List.pairwise_append]
      refine ⟨(List.pairwise_append.mp hs).1, ?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨fun b hb => Nat.le_of_lt (hB b hb),
          (List.pairwise_append.mp hs).2.1⟩
      · intro y hy z hz
        have hpa := (List.pairwise_append.mp (List.pairwise_append.mp hs).1)
        have hle : y.val ≤ i1.val := by
          rcases List.mem_append.mp hy with hy | hy
          · exact hpa.2.2 y hy i1 (by simp)
          · simp at hy; subst hy; exact le_refl _
        rcases List.mem_cons.mp hz with rfl | hz
        · have : ¬ i1 > z := hax
          scalar_tac
        · exact (List.pairwise_append.mp hs).2.2 y hy z hz

theorem sort_outer_spec : ∀ (n : Nat) (v : Slice Usize) (i : Usize), v.length - i.val = n →
    SortedV (v.val.take i.val) →
    params.sort_indexes_loop0 v i ⦃ r => r.val.Perm v.val ∧ SortedV r.val ⦄ := by
  intro n
  induction n with
  | zero =>
    intro v i hn hs
    unfold params.sort_indexes_loop0
    rw [loop]
    simp only
    rw [params.sort_indexes_loop0.body]
    have : ¬ i.val < v.length := by omega
    have ht : v.val.take i.val = v.val := List.take_of_length_le (by simp only [Slice.length] at this; omega)
    split
    · exfalso; scalar_tac
    · simp only [Std.bind_ok, WP.spec_ok]
      exact ⟨List.Perm.refl _, ht ▸ hs⟩
  | succ n ih =>
    intro v i hn hs
    unfold params.sort_indexes_loop0
    rw [loop]
    simp only
    rw [params.sort_indexes_loop0.body]
    have hlt : i.val < v.length := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp only [Slice.len]; exact hlt))]
    have hv : v.val = v.val.take i.val ++ v.val[i.val]'(by simpa using hlt) :: ([] ++ v.val.drop (i.val + 1)) := by
      simp
    step with sort_inner_spec i.val v i (v.val.take i.val) (v.val[i.val]'(by simpa using hlt)) [] _ rfl hv
      (by simp only [Slice.length] at hlt; simp; omega) (by simpa using hs) (by simp) as ⟨v1, L, h1, h2, h3⟩
    step as ⟨i2, hi2⟩
    have hL : L.length = i.val + 1 := by
      rw [h3.length_eq]; simp only [Slice.length] at hlt; simp; omega
    have hperm : v1.val.Perm v.val := by
      have e : v.val = v.val.take i.val ++ v.val[i.val]'(by simpa using hlt) :: v.val.drop (i.val + 1) := by
        simp
      rw [h1]
      refine (List.Perm.append_right _ h3).trans ?_
      rw [List.append_nil, List.cons_append]
      exact List.perm_middle.symm.trans (e ▸ List.Perm.refl _)
    have := ih v1 i2 (by
        rw [hi2]; have := hperm.length_eq; simp only [Slice.length] at hn this ⊢; omega)
      (by rw [hi2, h1, List.take_left' hL]; exact h2)
    unfold params.sort_indexes_loop0 at this
    refine WP.spec_mono this ?_
    rintro r ⟨hr1, hr2⟩
    exact ⟨hr1.trans hperm, hr2⟩

theorem sort_indexes_spec (v : Slice Usize) :
    params.sort_indexes v ⦃ r => r.val.Perm v.val ∧ SortedV r.val ⦄ := by
  unfold params.sort_indexes
  exact sort_outer_spec _ v 1#usize rfl (by
    rcases hv : v.val with _ | ⟨a, l⟩
    · simp
    · simp)

/-! ## `into_values`: the search for the first missing index -/

theorem iv_loop1_spec (S : alloc.vec.Vec Usize) : ∀ (n : Nat) (m : Usize), S.length - m.val = n →
    m.val ≤ S.length →
    (∀ k < m.val, (S.val[k]?).map (·.val) = some k) →
    params.Params.into_values_loop1 S m ⦃ r => r.val ≤ S.length ∧
      (∀ k < r.val, (S.val[k]?).map (·.val) = some k) ∧
      (r.val < S.length → (S.val[r.val]?).map (·.val) ≠ some r.val) ⦄ := by
  intro n
  induction n with
  | zero =>
    intro m hn hm hk
    unfold params.Params.into_values_loop1
    rw [loop]
    rw [params.Params.into_values_loop1.body]
    split
    · exfalso; scalar_tac
    · simp only [Std.bind_ok, WP.spec_ok]
      exact ⟨hm, hk, fun h => by omega⟩
  | succ n ih =>
    intro m hn hm hk
    unfold params.Params.into_values_loop1
    rw [loop]
    rw [params.Params.into_values_loop1.body]
    have hlt : m.val < S.length := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp only [alloc.vec.Vec.len]; exact hlt))]
    step as ⟨i1, hi1⟩
    have hget : S.val[m.val]? = some i1 := by rw [hi1]; simp
    split
    · rename_i heq
      step as ⟨m1, hm1⟩
      have := ih m1 (by rw [hm1]; omega) (by rw [hm1]; omega) (by
        intro k hk'
        rcases Nat.lt_or_ge k m.val with h | h
        · exact hk k h
        · have : k = m.val := by omega
          subst this; rw [hget]; simp [heq])
      unfold params.Params.into_values_loop1 at this
      exact this
    · rename_i hne
      simp only [Std.bind_ok, WP.spec_ok]
      refine ⟨by omega, hk, fun _ => ?_⟩
      rw [hget]; simp only [Option.map_some]
      intro h; exact hne (by simp only [Option.some.injEq] at h; scalar_tac)

/-! ## `into_values`: the inner loop over the statement's names -/

/-- Position `j` of the names is `k`. -/
abbrev PosIs (ns : Slice (alloc.vec.Vec U8)) (k : List U8) (j : Nat) : Prop :=
  (ns.val[j]?).map (·.val) = some k

theorem iv_inner_spec (ns : Slice (alloc.vec.Vec U8)) (nm : alloc.vec.Vec U8) (val : value.Value) :
    ∀ (n : Nat) (values : alloc.vec.Vec value.Value) (indexes : alloc.vec.Vec Usize)
      (first : Option Usize) (i : Usize),
    ns.length - i.val = n → i.val ≤ ns.length → values.length = ns.length →
    (∀ f, first = some f → f.val < i.val) →
    indexes.length + ((List.range' i.val (ns.length - i.val)).filter (fun j => PosIs ns nm.val j)).length
      ≤ Usize.max →
    params.Params.into_values_loop0_loop0 ns values indexes nm val first i ⦃ values' indexes' first' =>
      indexes'.val.map (·.val) = indexes.val.map (·.val) ++
        (List.range' i.val (ns.length - i.val)).filter (fun j => PosIs ns nm.val j) ∧
      first'.map (·.val) = (first.map (·.val)).or
        ((List.range' i.val (ns.length - i.val)).find? (fun j => PosIs ns nm.val j)) ∧
      values'.length = ns.length ∧
      ∀ j, values'.val[j]? = if i.val ≤ j ∧ PosIs ns nm.val j ∧ first'.map (·.val) ≠ some j
        then (if j < ns.length then some val else none) else values.val[j]? ⦄ := by
  intro n
  induction n with
  | zero =>
    intro values indexes first i hn hi hvl hf hlen
    unfold params.Params.into_values_loop0_loop0
    rw [loop]
    simp only
    rw [params.Params.into_values_loop0_loop0.body.eq_def]
    have he : ns.length - i.val = 0 := hn
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp only [Slice.len]; scalar_tac))]
    simp only [Std.bind_ok, WP.spec_ok, he, List.range'_zero, List.filter_nil, List.append_nil,
      List.find?_nil, Option.or_none]
    refine ⟨rfl, rfl, hvl, fun j => ?_⟩
    · split
      · rename_i hc
        exfalso
        obtain ⟨h1, h2, _⟩ := hc
        have : j < ns.val.length := by
          unfold PosIs at h2
          cases h : ns.val[j]? with
          | none => simp [h] at h2
          | some _ => exact (List.getElem?_eq_some_iff.mp h).1
        simp only [Slice.length] at he; omega
      · rfl
  | succ n ih =>
    intro values indexes first i hn hi hvl hf hlen
    have hlt : i.val < ns.length := by omega
    have hr : List.range' i.val (ns.length - i.val) = i.val :: List.range' (i.val + 1) (ns.length - (i.val + 1)) := by
      rw [show ns.length - i.val = (ns.length - (i.val + 1)) + 1 by omega, List.range'_succ]
    unfold params.Params.into_values_loop0_loop0
    rw [loop]
    simp only
    rw [params.Params.into_values_loop0_loop0.body.eq_def]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp only [Slice.len]; exact hlt))]
    step as ⟨v, hv⟩
    step with slice_u8_eq_spec (alloc.vec.Vec.deref v) (alloc.vec.Vec.deref nm) as ⟨b, hb⟩
    rw [CBTUtil.vec_deref_val, CBTUtil.vec_deref_val] at hb
    have hgi : ns.val[i.val]? = some v := by rw [hv]; simp
    have hpos : PosIs ns nm.val i.val ↔ b = true := by
      unfold PosIs; rw [hgi, hb]; simp
    rw [hr] at hlen ⊢
    split
    · rename_i hbt
      have hP : PosIs ns nm.val i.val := hpos.mpr hbt
      rw [List.filter_cons_of_pos (by simpa using hP), List.length_cons] at hlen
      step with alloc.vec.Vec.push_spec indexes i (by simp at hlen ⊢; omega) as ⟨ix2, hix2⟩
      rw [List.filter_cons_of_pos (by simpa using hP), List.find?_cons_of_pos (by simpa using hP)]
      cases first with
      | none =>
        simp only [Std.bind_ok]
        step as ⟨i2, hi2⟩
        have hn2 : ns.length - i2.val = n := by rw [hi2, Nat.sub_add_eq, hn, Nat.add_sub_cancel]
        have := ih values ix2 (some i) i2 hn2 (by rw [hi2]; exact Nat.succ_le_of_lt hlt) hvl
          (fun f hf' => by cases hf'; rw [hi2]; omega)
          (by rw [hi2]; simp [hix2] at hlen ⊢; omega)
        unfold params.Params.into_values_loop0_loop0 at this
        refine WP.spec_mono this ?_
        rintro ⟨values', indexes', first'⟩ ⟨h1, h2, h3, h4⟩
        simp only [Option.map_some, Option.some_or] at h2
        refine ⟨by rw [h1, hix2, hi2]; simp, by rw [h2]; simp, h3, ?_⟩
        intro j
        rw [h4 j, hi2, h2]
        by_cases hj : j = i.val
        · subst hj; simp
        · by_cases hij : i.val ≤ j
          · simp [show i.val + 1 ≤ j by omega, hij, Ne.symm hj]
          · simp [show ¬ i.val + 1 ≤ j by omega, hij]
      | some f =>
        simp only [value_clone_eq, Std.bind_ok]
        step with alloc.vec.Vec.index_mut_usize_spec values i (by omega) as ⟨p, hp1, hp2⟩
        obtain ⟨p1, back⟩ := p
        simp only at hp2 ⊢
        subst hp2
        step as ⟨i2, hi2⟩
        have hn2 : ns.length - i2.val = n := by rw [hi2, Nat.sub_add_eq, hn, Nat.add_sub_cancel]
        have hfi : f.val < i.val := hf f rfl
        have := ih (values.set i val) ix2 (some f) i2 hn2 (by rw [hi2]; exact Nat.succ_le_of_lt hlt)
          (by simp [hvl]) (fun f' hf' => by cases hf'; rw [hi2]; omega)
          (by rw [hi2]; simp [hix2] at hlen ⊢; omega)
        unfold params.Params.into_values_loop0_loop0 at this
        refine WP.spec_mono this ?_
        rintro ⟨values', indexes', first'⟩ ⟨h1, h2, h3, h4⟩
        simp only [Option.map_some, Option.some_or] at h2
        refine ⟨by rw [h1, hix2, hi2]; simp, by rw [h2]; simp, h3, ?_⟩
        intro j
        rw [h4 j, hi2, h2]
        by_cases hj : j = i.val
        · subst hj
          have hvi : i.val < values.val.length := by simp only [alloc.vec.Vec.length] at hvl; omega
          have hnmi : (ns.val[i.val]'(by simpa using hlt)).val = nm.val := by
            have := hP; unfold PosIs at this; rw [hgi] at this; simpa [hv] using this
          simp [alloc.vec.Vec.set_val_eq, hlt, show f.val ≠ i.val by omega, hvi, hnmi]
        · by_cases hij : i.val ≤ j
          · simp [show i.val + 1 ≤ j by omega, hij, alloc.vec.Vec.set_val_eq, Ne.symm hj]
          · simp [show ¬ i.val + 1 ≤ j by omega, hij, alloc.vec.Vec.set_val_eq, Ne.symm hj]
    · rename_i hbf
      have hP : ¬ PosIs ns nm.val i.val := fun h => hbf (hpos.mp h)
      simp only [hP, decide_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg] at hlen ⊢
      step as ⟨i2, hi2⟩
      have hn2 : ns.length - i2.val = n := by rw [hi2, Nat.sub_add_eq, hn, Nat.add_sub_cancel]
      have := ih values indexes first i2 hn2 (by rw [hi2]; exact Nat.succ_le_of_lt hlt) hvl
        (fun f hf' => by have := hf f hf'; rw [hi2]; omega) (by rw [hi2]; exact hlen)
      unfold params.Params.into_values_loop0_loop0 at this
      refine WP.spec_mono this ?_
      rintro ⟨values', indexes', first'⟩ ⟨h1, h2, h3, h4⟩
      refine ⟨by rw [h1, hi2], by rw [h2, hi2, List.find?_cons_of_neg (by simpa using hP)], h3, ?_⟩
      intro j
      rw [h4 j, hi2]
      by_cases hj : j = i.val
      · subst hj; simp [hP]
      · by_cases hij : i.val ≤ j
        · simp [show i.val + 1 ≤ j by omega, hij]
        · simp [show ¬ i.val + 1 ≤ j by omega, hij]

/-! ## `into_values`: the outer loop over the map's entries -/

/-- The positions of the names equal to `k`. -/
abbrev posOf (ns : Slice (alloc.vec.Vec U8)) (k : List U8) : List Nat :=
  (List.range ns.length).filter (fun j => PosIs ns k j)

/-- The value for name `n` after the entries `P`. -/
abbrev Lv (P : List (alloc.vec.Vec U8 × value.Value)) (n : alloc.vec.Vec U8) : value.Value :=
  ((P.find? (fun e => e.1.val = n.val)).map (·.2)).getD .NULL

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem posIs_lt {ns : Slice (alloc.vec.Vec U8)} {k : List U8} {j : Nat} (h : PosIs ns k j) :
    j < ns.length := by
  unfold PosIs at h
  cases hj : ns.val[j]? with
  | none => simp [hj] at h
  | some _ => exact (List.getElem?_eq_some_iff.mp hj).1

theorem iv_entry_spec {β : Type} (ns : Slice (alloc.vec.Vec U8)) (nm : alloc.vec.Vec U8) (val : value.Value)
    (values : alloc.vec.Vec value.Value) (indexes : alloc.vec.Vec Usize)
    (hvl : values.length = ns.length) (hlen : indexes.length + (posOf ns nm.val).length ≤ Usize.max)
    (K : alloc.vec.Vec value.Value → alloc.vec.Vec Usize → Result β) (Q : β → Prop)
    (hK : ∀ values'' indexes'',
      indexes''.val.map (·.val) = indexes.val.map (·.val) ++ posOf ns nm.val →
      values''.length = ns.length →
      (∀ j, values''.val[j]? = if PosIs ns nm.val j then some val else values.val[j]?) →
      K values'' indexes'' ⦃ Q ⦄) :
    (do
      let (values1, indexes1, first) ←
        params.Params.into_values_loop0_loop0 ns values indexes nm val none 0#usize
      match first with
      | none => K values1 indexes1
      | some first1 => do
        let (_, index_mut_back) ← alloc.vec.Vec.index_mut_usize values1 first1
        K (index_mut_back val) indexes1) ⦃ Q ⦄ := by
  have hr : List.range' 0 (ns.length - 0) = List.range ns.length := by
    simp [List.range_eq_range']
  step with iv_inner_spec ns nm val ns.length values indexes none 0#usize (by simp) (by simp) hvl
    (by simp) (by simpa [List.range_eq_range', posOf, PosIs] using hlen) as ⟨values', indexes', first', h1, h2, h3, h4⟩
  rw [hr] at h1 h2
  simp only [Option.map_none, Option.none_or] at h2
  simp only [Nat.zero_le, true_and] at h4
  cases first' with
  | none =>
    refine hK _ _ h1 h3 (fun j => ?_)
    rw [h4 j]
    by_cases hp : PosIs ns nm.val j
    · exfalso
      have := List.find?_eq_none.mp h2.symm j (List.mem_range.mpr (posIs_lt hp))
      simp at this
      obtain ⟨x, hx, hxv⟩ : ∃ x, ns.val[j]? = some x ∧ x.val = nm.val := by unfold PosIs at hp; simpa using hp
      exact this x hx hxv
    · simp [hp]
  | some f =>
    simp only [Option.map_some] at h2
    have hf := List.find?_some h2.symm
    have hfl : f.val < ns.length := List.mem_range.mp (List.mem_of_find?_eq_some h2.symm)
    step with alloc.vec.Vec.index_mut_usize_spec values' f (by omega) as ⟨x, back, hx, hback⟩
    subst hback
    refine hK _ _ h1 (by simp [h3]) (fun j => ?_)
    have hfp : PosIs ns nm.val f.val := by simpa using hf
    by_cases hj : f.val = j
    · subst hj
      rw [ite_t hfp, alloc.vec.Vec.set_val_eq, List.getElem?_set_self (by simp only [alloc.vec.Vec.length] at h3; omega)]
    · rw [alloc.vec.Vec.set_val_eq, List.getElem?_set_ne hj, h4 j]
      by_cases hp : PosIs ns nm.val j
      · rw [ite_t ⟨hp, by simpa using hj⟩, ite_t hp, ite_t (posIs_lt hp)]
      · rw [ite_f (fun h => hp h.1), ite_f hp]

theorem iv_outer_spec (ns : Slice (alloc.vec.Vec U8)) :
    ∀ (R P : List (alloc.vec.Vec U8 × value.Value))
      (iter : alloc.vec.into_iter.IntoIter (alloc.vec.Vec U8 × value.Value))
      (values : alloc.vec.Vec value.Value) (indexes : alloc.vec.Vec Usize),
    iter.val = R → ((P ++ R).map (·.1.val)).Nodup →
    ((P ++ R).flatMap (fun e => posOf ns e.1.val)).length ≤ Usize.max →
    values.length = ns.length →
    (∀ j : Nat, values.val[j]? = (ns.val[j]?).map (Lv P)) →
    indexes.val.map (·.val) = P.flatMap (fun e => posOf ns e.1.val) →
    params.Params.into_values_loop0 iter ns values indexes ⦃ values' indexes' =>
      values'.length = ns.length ∧ (∀ j : Nat, values'.val[j]? = (ns.val[j]?).map (Lv (P ++ R))) ∧
      indexes'.val.map (·.val) = (P ++ R).flatMap (fun e => posOf ns e.1.val) ⦄ := by
  intro R
  induction R with
  | nil =>
    intro P iter values indexes hit hnd hlen hvl hv hix
    unfold params.Params.into_values_loop0
    rw [loop]
    simp only
    rw [params.Params.into_values_loop0.body.eq_def]
    step with next_spec iter as ⟨p, ho, hit'⟩
    obtain ⟨o, it'⟩ := p
    simp only [hit, List.head?_nil] at ho ⊢
    subst ho
    simp only [Std.uncurry_apply_pair, Std.bind_ok, WP.spec_ok, WP.uncurry'_pair, List.append_nil]
    exact ⟨hvl, hv, hix⟩
  | cons e R ih =>
    intro P iter values indexes hit hnd hlen hvl hv hix
    obtain ⟨k, v⟩ := e
    unfold params.Params.into_values_loop0
    rw [loop]
    simp only
    rw [params.Params.into_values_loop0.body.eq_def]
    step with next_spec iter as ⟨p, ho, hit'⟩
    obtain ⟨o, it'⟩ := p
    simp only [hit, List.head?_cons, List.tail_cons] at ho hit' ⊢
    subst ho
    simp only [Std.uncurry_apply_pair]
    have hkP : ∀ e ∈ P, e.1.val ≠ k.val := by
      intro e he heq
      have := List.nodup_middle.mp (by simpa using hnd)
      simp only [List.nodup_cons, List.mem_map, List.mem_append] at this
      exact this.1 (Or.inl ⟨e, he, heq⟩)
    have hlen1 : indexes.length + (posOf ns k.val).length ≤ Usize.max := by
      have : indexes.length = (P.flatMap (fun e => posOf ns e.1.val)).length := by
        rw [← hix]; simp
      rw [this]
      simp only [List.flatMap_append, List.flatMap_cons, List.length_append] at hlen
      omega
    apply WP.spec_bind (Pₘ := fun r => ∃ values'' indexes'', r = .cont (it', values'', indexes'') ∧
      indexes''.val.map (·.val) = indexes.val.map (·.val) ++ posOf ns k.val ∧
      values''.length = ns.length ∧
      (∀ j, values''.val[j]? = if PosIs ns k.val j then some v else values.val[j]?))
    · exact iv_entry_spec ns k v values indexes hvl hlen1 (fun a b => ok (ControlFlow.cont (it', a, b))) _
        (fun a b h1 h2 h3 => (WP.spec_ok _).mpr ⟨a, b, rfl, h1, h2, h3⟩)
    · rintro r ⟨values'', indexes'', rfl, h1, h2, h3⟩
      simp only
      have := ih (P ++ [(k, v)]) it' values'' indexes'' hit' (by simpa using hnd) (by simpa using hlen) h2
        (fun j => by
          rw [h3 j, hv j]
          by_cases hp : PosIs ns k.val j
          · rw [ite_t hp]
            obtain ⟨w, hw, hwk⟩ : ∃ w, ns.val[j]? = some w ∧ w.val = k.val := by
              unfold PosIs at hp; simpa using hp
            have hnone : P.find? (fun e => e.1.val = k.val) = none := by
              rw [List.find?_eq_none]; intro e he; simpa using hkP e he
            rw [hw]
            simp [Lv, List.find?_append, hnone, hwk]
          · rw [ite_f hp]
            rcases Option.eq_none_or_eq_some (ns.val[j]?) with hw | ⟨w, hw⟩
            · rw [hw]; rfl
            · have hne : ¬ w.val = k.val := fun h => hp (by unfold PosIs; rw [hw]; simp [h])
              rw [hw]
              simp [Lv, List.find?_append, Ne.symm hne])
        (by rw [h1, hix]; simp)
      unfold params.Params.into_values_loop0 at this
      refine WP.spec_mono this ?_
      rintro ⟨a, b⟩ ⟨h1', h2', h3'⟩
      exact ⟨h1', by simpa using h2', by simpa using h3'⟩

/-! ## `into_values`: combinatorics of the found positions -/

theorem first_missing (T : List Nat) (hlt : T.Pairwise (· < ·)) (m : Nat) (hm : m ≤ T.length)
    (hk : ∀ k < m, T[k]? = some k) (hne : m < T.length → T[m]? ≠ some m) :
    (∀ k < m, k ∈ T) ∧ m ∉ T ∧ (m < T.length → ∃ j ∈ T, m < j) ∧ (m = T.length → ∀ j ∈ T, j < m) := by
  have hpw := List.pairwise_iff_getElem.mp hlt
  have hge : ∀ h : m < T.length, m ≤ T[m] := by
    intro h
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · omega
    · have h1 := hk (m - 1) (by omega)
      obtain ⟨h1', h1''⟩ := List.getElem?_eq_some_iff.mp h1
      have := hpw (m - 1) m h1' h (by omega)
      omega
  have hne' : ∀ h : m < T.length, T[m] ≠ m := by
    intro h heq; exact hne h (by rw [List.getElem?_eq_getElem h, heq])
  refine ⟨fun k hkm => List.mem_iff_getElem?.mpr ⟨k, hk k hkm⟩, ?_, ?_, ?_⟩
  · intro hmem
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hmem
    obtain ⟨hp1, hp2⟩ := List.getElem?_eq_some_iff.mp hp
    rcases Nat.lt_trichotomy p m with h | h | h
    · have := hk p h; rw [hp] at this; cases this; omega
    · subst h; exact hne' hp1 hp2
    · have := hpw m p (by omega) hp1 h
      have := hge (by omega)
      omega
  · intro h
    exact ⟨T[m], List.getElem_mem h, by have := hge h; have := hne' h; omega⟩
  · intro h j hj
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hj
    obtain ⟨hp1, hp2⟩ := List.getElem?_eq_some_iff.mp hp
    have := hk p (by omega)
    rw [hp] at this; cases this; omega

theorem lookup_isSome_iff (m : Trusted.ParamsMap) (k : List U8) :
    (Trusted.paramsMapLookup m k).isSome ↔ ∃ e ∈ Trusted.paramsMapEntries m, e.1.val = k := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨e, he, hk, _⟩ := (lookup_some_iff m k v).mp hv
    exact ⟨e, he, hk⟩
  · rintro ⟨e, he, hk⟩
    rw [(lookup_some_iff m k e.2).mpr ⟨e, he, hk, rfl⟩]; rfl

theorem mem_posOf (ns : Slice (alloc.vec.Vec U8)) (k : List U8) (j : Nat) :
    j ∈ posOf ns k ↔ ∃ h : j < ns.length, (ns.val[j]'h).val = k := by
  simp only [posOf, List.mem_filter, List.mem_range, decide_eq_true_eq, PosIs]
  constructor
  · rintro ⟨h, h2⟩
    refine ⟨h, ?_⟩
    rw [List.getElem?_eq_getElem h] at h2; simpa using h2
  · rintro ⟨h, h2⟩
    exact ⟨h, by rw [List.getElem?_eq_getElem h]; simpa using h2⟩

theorem found_facts (ns : Slice (alloc.vec.Vec U8)) (m : Trusted.ParamsMap) :
    ((Trusted.paramsMapEntries m).flatMap (fun e => posOf ns e.1.val)).Nodup ∧
    (∀ j, j ∈ (Trusted.paramsMapEntries m).flatMap (fun e => posOf ns e.1.val) ↔
      ∃ h : j < ns.length, (Trusted.paramsMapLookup m (ns.val[j]'h).val).isSome) ∧
    ((Trusted.paramsMapEntries m).flatMap (fun e => posOf ns e.1.val)).length ≤ ns.length := by
  have hmem : ∀ j, j ∈ (Trusted.paramsMapEntries m).flatMap (fun e => posOf ns e.1.val) ↔
      ∃ h : j < ns.length, (Trusted.paramsMapLookup m (ns.val[j]'h).val).isSome := by
    intro j
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨e, he, hj⟩
      obtain ⟨h, hk⟩ := (mem_posOf ns _ j).mp hj
      exact ⟨h, (lookup_isSome_iff m _).mpr ⟨e, he, hk.symm⟩⟩
    · rintro ⟨h, hs⟩
      obtain ⟨e, he, hk⟩ := (lookup_isSome_iff m _).mp hs
      exact ⟨e, he, (mem_posOf ns _ j).mpr ⟨h, hk.symm⟩⟩
  have hnd : ((Trusted.paramsMapEntries m).flatMap (fun e => posOf ns e.1.val)).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun e _ => (List.nodup_range).filter _, ?_⟩
    have hk := Trusted.paramsMapEntries_keys_nodup m
    rw [List.Nodup, List.pairwise_map] at hk
    refine hk.imp ?_
    intro a b hab
    simp only [Function.onFun]
    rw [List.disjoint_left]
    intro j ha hb
    obtain ⟨h1, h1'⟩ := (mem_posOf ns _ j).mp ha
    obtain ⟨h2, h2'⟩ := (mem_posOf ns _ j).mp hb
    exact hab (h1'.symm.trans h2')
  refine ⟨hnd, hmem, ?_⟩
  have hsub : (Trusted.paramsMapEntries m).flatMap (fun e => posOf ns e.1.val) ⊆ List.range ns.length := by
    intro j hj
    obtain ⟨h, _⟩ := (hmem j).mp hj
    exact List.mem_range.mpr h
  have := (hnd.subperm hsub).length_le
  simpa using this

/-! ## `into_values` of `Params::Named` -/

theorem iv_named_spec (m : Trusted.ParamsMap) (s : Slice (alloc.vec.Vec U8)) (hne : s.val ≠ []) :
    params.Params.into_values (.Named m) (some s) ⦃ r =>
      ((∀ n ∈ s.val, (Trusted.paramsMapLookup m n.val).isSome) → ∃ v, r = .Ok v ∧
        v.val.map some = s.val.map (fun n => Trusted.paramsMapLookup m n.val)) ∧
      ((∃ n ∈ s.val, Trusted.paramsMapLookup m n.val = none) → ∃ e, r = .Err (.Missing e) ∧
        e.val = intoValuesMissing m (s.val.map (·.val)) ∧
        e.val ∈ s.val.map (·.val) ∧ Trusted.paramsMapLookup m e.val = none) ⦄ := by
  obtain ⟨hInd, hmem, hIlen⟩ := found_facts s m
  have hsl : s.length ≠ 0 := by simpa [Slice.length] using hne
  unfold params.Params.into_values
  simp only [core.slice.Slice.is_empty, hsl, decide_false, Std.bind_ok, Bool.false_eq_true, ↓reduceIte]
  step with alloc.vec.from_elem_spec value.Value.Insts.CoreCloneClone value.Value.NULL (Slice.len s)
    (value_clone_eq value.Value.NULL) as ⟨values, hv1, hv2⟩
  step with (show sql_trusted.params_map_into_entries m ⦃ v => v.val = Trusted.paramsMapEntries m ⦄ by
    simp [sql_trusted.params_map_into_entries]) as ⟨ev, hev⟩
  step with (show alloc.vec.IntoIteratorVec.into_iter ev ⦃ it => it.val = ev.val ⦄ from
    (WP.spec_ok _).mpr rfl) as ⟨it, hit⟩
  rw [hev] at hit
  have hlenI := hIlen
  step with iv_outer_spec s (Trusted.paramsMapEntries m) [] it values
    (alloc.vec.Vec.with_capacity Usize (Slice.len s)) hit
    (by simpa using Trusted.paramsMapEntries_keys_nodup m)
    (by simp only [List.nil_append]; have := s.property; simp only [Slice.length] at hIlen; omega)
    (by simp [hv2])
    (fun j => by
      rw [hv1]
      rcases Nat.lt_or_ge j s.length with h | h
      · rw [List.getElem?_replicate_of_lt (by simpa using h), List.getElem?_eq_getElem (by simpa using h)]
        simp [Lv]
      · rw [List.getElem?_eq_none (by simpa using h), List.getElem?_eq_none (by simpa [Slice.length] using h)]
        rfl)
    (by simp [alloc.vec.Vec.with_capacity]) as ⟨values1, indexes1, h1, h2, h3⟩
  simp only [List.nil_append] at h2 h3
  have hIdx : indexes1.length = ((Trusted.paramsMapEntries m).flatMap (fun e => posOf s e.1.val)).length := by
    rw [← h3]; simp
  -- the values, when every name has a value
  have hvals : ∀ (hall : ∀ n ∈ s.val, (Trusted.paramsMapLookup m n.val).isSome),
      values1.val.map some = s.val.map (fun n => Trusted.paramsMapLookup m n.val) := by
    intro hall
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_map, h2 j, List.getElem?_map]
    rcases Option.eq_none_or_eq_some (s.val[j]?) with hj | ⟨w, hj⟩
    · rw [hj]; rfl
    · rw [hj]
      have hw := hall w (List.mem_of_getElem? hj)
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hw
      simp only [Option.map_some, Option.some.injEq]
      change some ((Trusted.paramsMapLookup m w.val).getD value.Value.NULL) = Trusted.paramsMapLookup m w.val
      rw [hx]; rfl
  by_cases hall : ∀ n ∈ s.val, (Trusted.paramsMapLookup m n.val).isSome
  · have hfull : ((Trusted.paramsMapEntries m).flatMap (fun e => posOf s e.1.val)).length = s.length := by
      apply le_antisymm hIlen
      have hsub : List.range s.length ⊆ (Trusted.paramsMapEntries m).flatMap (fun e => posOf s e.1.val) := by
        intro j hj
        have hj' := List.mem_range.mp hj
        exact (hmem j).mpr ⟨hj', hall _ (List.getElem_mem _)⟩
      simpa using (List.nodup_range.subperm hsub).length_le
    have hc : ¬ ((alloc.vec.Vec.len indexes1 != Slice.len s) = true) := by
      simp only [bne_iff_ne, ne_eq, not_not]; scalar_tac
    rw [ite_f hc]
    apply (WP.spec_ok _).mpr
    refine ⟨fun _ => ⟨values1, rfl, hvals hall⟩, ?_⟩
    intro n hn hnone
    have := hall n hn; simp [hnone] at this
  · set I := (Trusted.paramsMapEntries m).flatMap (fun e => posOf s e.1.val) with hIdef
    obtain ⟨n0, hn0, hn0s⟩ : ∃ n ∈ s.val, ¬ (Trusted.paramsMapLookup m n.val).isSome := by
      simpa using hall
    obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.mp hn0
    obtain ⟨hj0l, hj0e⟩ := List.getElem?_eq_some_iff.mp hj0
    have hj0I : j0 ∉ I := by
      intro h; obtain ⟨_, hs⟩ := (hmem j0).mp h; rw [hj0e] at hs; exact hn0s hs
    have hIlt : I.length < s.length := by
      have hsub : I ⊆ (List.range s.length).erase j0 := by
        intro j hj
        obtain ⟨h, _⟩ := (hmem j).mp hj
        exact (List.mem_erase_of_ne (fun (e : j = j0) => hj0I (e ▸ hj))).mpr (List.mem_range.mpr h)
      have := (hInd.subperm hsub).length_le
      rw [List.length_erase_of_mem (List.mem_range.mpr hj0l)] at this
      simp at this; simp [Slice.length]; omega
    have hc : (alloc.vec.Vec.len indexes1 != Slice.len s) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h
      have : indexes1.length = s.length := by scalar_tac
      omega
    rw [ite_t hc]
    simp only [lift, alloc.vec.Vec.deref_mut, Std.bind_ok]
    step with sort_indexes_spec indexes1.slice as ⟨s1, hperm, hsorted⟩
    step with iv_loop1_spec ⟨s1⟩ _ 0#usize rfl (by simp) (by simp) as ⟨miss, hm1, hm2, hm3⟩
    set T := s1.val.map (·.val) with hTdef
    have hTI : T.Perm I := by
      rw [← h3, hTdef]; exact hperm.map _
    have hTnd : T.Nodup := hTI.nodup_iff.mpr hInd
    have hTlt : T.Pairwise (· < ·) := by
      have h1 : T.Pairwise (· ≤ ·) := by rw [hTdef, List.pairwise_map]; exact hsorted
      exact (h1.and hTnd).imp (fun ⟨a, b⟩ => Nat.lt_of_le_of_ne a b)
    have hTlen : T.length = I.length := hTI.length_eq
    have hfound : ∀ j (h : j < s.length), (Trusted.paramsMapLookup m (s.val[j]'h).val).isSome ↔ j ∈ T := by
      intro j h; rw [hTI.mem_iff, hmem j]; exact ⟨fun hs => ⟨h, hs⟩, fun ⟨_, hs⟩ => hs⟩
    have hvl : (alloc.vec.Vec.length ⟨s1⟩ : Nat) = T.length := by simp [hTdef, alloc.vec.Vec.length, alloc.vec.Vec.val]
    have hk : ∀ k < miss.val, T[k]? = some k := by
      intro k hk'; have := hm2 k hk'; simpa [hTdef, alloc.vec.Vec.val] using this
    have hne' : miss.val < T.length → T[miss.val]? ≠ some miss.val := by
      intro h; have := hm3 (by rw [hvl]; exact h); simpa [hTdef, alloc.vec.Vec.val] using this
    obtain ⟨fa, fb, fc, fd⟩ := first_missing T hTlt miss.val (by rw [← hvl]; exact hm1) hk hne'
    have hTs : T.length < s.length := by omega
    set names := s.val.map (·.val) with hnames
    have hnl : names.length = s.length := by simp [hnames, Slice.length]
    have hfind : names.findIdx? (fun k => !(Trusted.paramsMapLookup m k).isSome) = some miss.val := by
      rw [List.findIdx?_eq_some_iff_getElem]
      have hml : miss.val < s.length := by
        rcases Nat.lt_or_ge miss.val T.length with h | h
        · omega
        · have := hm1; rw [hvl] at this; omega
      refine ⟨by omega, ?_, ?_⟩
      · simp only [hnames, List.getElem_map, Bool.not_eq_true', Option.isSome_eq_false_iff,
          Option.isNone_iff_eq_none]
        have := (hfound miss.val hml).not.mpr fb
        simpa using this
      · intro k hk'
        simp only [hnames, List.getElem_map, Bool.not_eq_true', Bool.not_eq_false]
        exact (hfound k (by omega)).mpr (fa k hk')
    have hnotfound : ∀ j (h : j < s.length), j ∉ T → Trusted.paramsMapLookup m (s.val[j]'h).val = none := by
      intro j h hj
      have := (hfound j h).not.mpr hj
      simpa using this
    split
    · rename_i hlt
      have hmT : miss.val < T.length := by rw [← hvl]; scalar_tac
      have hml : miss.val < s.length := by omega
      step with Slice.index_usize_spec s miss (by simpa [Slice.length] using hml) as ⟨w, hw⟩
      simp only [vec_u8_clone_eq, Std.bind_ok, params.ParamsError.Insts.CoreConvertFromMissingNamedParameterError.from,
        WP.spec_ok]
      refine ⟨fun h => absurd h hall, fun _ _ _ => ⟨w, rfl, ?_, ?_, ?_⟩⟩
      · obtain ⟨j, hjT, hjm⟩ := fc hmT
        have hjl : j < s.length := by
          obtain ⟨h, _⟩ := (hmem j).mp (hTI.mem_iff.mp hjT); exact h
        have hany : (names.drop (miss.val + 1)).any (fun k => (Trusted.paramsMapLookup m k).isSome) = true := by
          rw [List.any_eq_true]
          refine ⟨(s.val[j]'(by simpa [Slice.length] using hjl)).val, ?_, (hfound j hjl).mpr hjT⟩
          rw [List.mem_iff_getElem?]
          refine ⟨j - (miss.val + 1), ?_⟩
          rw [List.getElem?_drop, show miss.val + 1 + (j - (miss.val + 1)) = j by omega, hnames,
            List.getElem?_map, List.getElem?_eq_getElem (by simpa [Slice.length] using hjl)]
          rfl
        simp only [intoValuesMissing, hfind, hany, ↓reduceIte]
        rw [hw, hnames, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem (by simpa [Slice.length] using hml)]
        rfl
      · rw [hw]; exact List.mem_map_of_mem (List.getElem_mem _)
      · rw [hw]; exact hnotfound miss.val hml fb
    · rename_i hge
      have hmT : miss.val = T.length := by
        have : ¬ miss.val < T.length := by rw [← hvl]; scalar_tac
        have := hm1; rw [hvl] at this; omega
      have hsl1 : 0 < s.length := by omega
      step as ⟨i6, hi6⟩
      step with Slice.index_usize_spec s i6 (by simp [Slice.length] at hsl1 ⊢; scalar_tac) as ⟨w, hw⟩
      simp only [vec_u8_clone_eq, Std.bind_ok, params.ParamsError.Insts.CoreConvertFromMissingNamedParameterError.from,
        WP.spec_ok]
      have hi6v : i6.val = s.length - 1 := by scalar_tac
      have hlastnf : s.length - 1 ∉ T := fun h => by have := fd hmT _ h; omega
      refine ⟨fun h => absurd h hall, fun _ _ _ => ⟨w, rfl, ?_, ?_, ?_⟩⟩
      · have hany : (names.drop (miss.val + 1)).any (fun k => (Trusted.paramsMapLookup m k).isSome) = false := by
          rw [List.any_eq_false]
          intro x hx hxs
          obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hx
          rw [List.getElem?_drop, hnames, List.getElem?_map] at hp
          rcases Option.eq_none_or_eq_some (s.val[miss.val + 1 + p]?) with h | ⟨y, h⟩
          · rw [h] at hp; cases hp
          · rw [h] at hp
            simp only [Option.map_some, Option.some.injEq] at hp
            obtain ⟨hyl, hye⟩ := List.getElem?_eq_some_iff.mp h
            have hT := (hfound (miss.val + 1 + p) (by simpa [Slice.length] using hyl)).mp (by
              simp only [hye, hp, hxs])
            have := fd hmT _ hT
            omega
        simp only [intoValuesMissing, hfind, hany, Bool.false_eq_true, ↓reduceIte]
        rw [hw, hnames]
        simp only [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.length_map, List.getElem?_map]
        rw [List.getElem?_eq_getElem (by simp [Slice.length] at hsl1 ⊢; omega)]
        simp [hi6v, Slice.length]
      · rw [hw]; exact List.mem_map_of_mem (List.getElem_mem _)
      · rw [hw]
        have := hnotfound (s.length - 1) (by omega) hlastnf
        simpa [hi6v, Slice.length] using this

end mysql_common.PASUtil
