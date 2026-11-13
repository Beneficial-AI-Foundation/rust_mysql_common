import MysqlCommon.Types
open Aeneas Aeneas.Std mysql_common

/-! Consistency check (not a spec): a model of the `HashMap` axioms of `FunsExternal.lean` (dev 4999547): the opaque
`std.collections.hash.map.HashMap K V S A` is interpreted as `List (K × V)`; `entries`
normalises any list to a well-formed one (keys distinct by `.val`, length ≤ Usize.max).

Each theorem below restates one `Trusted.paramsMap*` axiom of `formal/trusted/MysqlCommon/FunsExternal.lean`
for this model, so the axioms have a model and cannot prove `False`. If an axiom changes, restate it
here; if it can no longer be proved for any model, the axiom set is suspect. (Added after a review
proved `False` from an earlier version of the insert axiom.) -/

namespace Model

abbrev HashMap (K V _S _A : Type) : Type := List (K × V)
abbrev ParamsMap := HashMap (alloc.vec.Vec U8) value.Value Unit Unit

def WF (l : List (alloc.vec.Vec U8 × value.Value)) : Prop :=
  (l.map fun e => e.1.val).Nodup ∧ l.length ≤ Usize.max

noncomputable def paramsMapEntries (m : ParamsMap) : List (alloc.vec.Vec U8 × value.Value) :=
  open Classical in if WF m then m else []

theorem wf_entries (m : ParamsMap) : WF (paramsMapEntries m) := by
  unfold paramsMapEntries; split
  · assumption
  · exact ⟨List.nodup_nil, by simp⟩

theorem entries_of_wf (m : ParamsMap) (h : WF m) : paramsMapEntries m = m := by
  simp [paramsMapEntries, h]

-- axiom paramsMapEntries_keys_nodup
theorem paramsMapEntries_keys_nodup (m : ParamsMap) :
    ((paramsMapEntries m).map fun e => e.1.val).Nodup := (wf_entries m).1
-- axiom paramsMapEntries_length
theorem paramsMapEntries_length (m : ParamsMap) : (paramsMapEntries m).length ≤ Usize.max :=
  (wf_entries m).2

def paramsMapEmpty : ParamsMap := []
-- axiom paramsMapEntries_empty
theorem paramsMapEntries_empty : paramsMapEntries paramsMapEmpty = [] := by
  unfold paramsMapEntries paramsMapEmpty; exact ite_self _

-- identical to the def in FunsExternal
noncomputable def paramsMapLookup (m : ParamsMap) (k : List U8) : Option value.Value :=
  ((paramsMapEntries m).find? fun e => e.1.val = k).map (·.2)

-- insert = cons after filtering out the key, saturating at the bound
noncomputable def paramsMapInsert (m : ParamsMap) (k : alloc.vec.Vec U8) (v : value.Value) :
    ParamsMap :=
  let l := (paramsMapEntries m).filter fun e => e.1.val ≠ k.val
  open Classical in if l.length < Usize.max then (k, v) :: l else paramsMapEntries m

-- axiom paramsMapEntries_insert (with the new `hlen`)
theorem paramsMapEntries_insert (m : ParamsMap) (k : alloc.vec.Vec U8) (v : value.Value)
    (h : paramsMapLookup m k.val = none)
    (hlen : (paramsMapEntries m).length < Usize.max) :
    (paramsMapEntries (paramsMapInsert m k v)).Perm ((k, v) :: paramsMapEntries m) := by
  have hnot : ∀ e ∈ paramsMapEntries m, e.1.val ≠ k.val := by
    intro e he heq
    unfold paramsMapLookup at h
    simp only [Option.map_eq_none_iff, List.find?_eq_none] at h
    exact h e he (by simpa using heq)
  have hf : (paramsMapEntries m).filter (fun e => e.1.val ≠ k.val) = paramsMapEntries m :=
    List.filter_eq_self.mpr (by intro e he; simpa using hnot e he)
  have hwf : WF ((k, v) :: paramsMapEntries m) := by
    refine ⟨?_, by simp; omega⟩
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, (wf_entries m).1⟩
    rintro ⟨e, he, heq⟩; exact hnot e he heq
  simp only [paramsMapInsert, hf, hlen, ite_true]
  rw [entries_of_wf _ hwf]

noncomputable def paramsMapRemove (m : ParamsMap) (k : List U8) : ParamsMap :=
  (paramsMapEntries m).filter fun e => e.1.val ≠ k

-- axiom paramsMapEntries_remove
theorem paramsMapEntries_remove (m : ParamsMap) (k : List U8) :
    (paramsMapEntries (paramsMapRemove m k)).Perm
      ((paramsMapEntries m).filter fun e => e.1.val ≠ k) := by
  have hw := wf_entries m
  have hwf : WF ((paramsMapEntries m).filter fun e => e.1.val ≠ k) :=
    ⟨(hw.1.sublist ((List.filter_sublist).map _)),
     le_trans (List.length_filter_le _ _) hw.2⟩
  simp only [paramsMapRemove]; rw [entries_of_wf _ hwf]

/-! Connect attributes (branch worktree-agent-a4d02d3c80c562b1d, `misc::trusted`): the axioms
are bare constants with no properties, so any inhabitants model them. -/
abbrev RB := misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit
abbrev ConnectAttrs := HashMap RB RB Unit Unit
abbrev StringMap := HashMap String String Unit Unit
def connectAttrsNew : ConnectAttrs := []
def connectAttrsInsert : ConnectAttrs → RB → RB → ConnectAttrs := fun m _ _ => m
def connectAttrsEntries : ConnectAttrs → alloc.vec.Vec (Slice U8 × Slice U8) :=
  fun _ => alloc.vec.Vec.new _
def connectAttrsFromStrings : StringMap → ConnectAttrs := fun _ => []
def connectAttrsIntoOwned : ConnectAttrs → ConnectAttrs := id
def connectAttrsToStrings : ConnectAttrs → StringMap := fun _ => []

end Model
#print axioms Model.paramsMapEntries_insert
#print axioms Model.paramsMapEntries_remove
#print axioms Model.paramsMapEntries_keys_nodup
#print axioms Model.paramsMapEntries_empty
#print axioms Model.paramsMapEntries_length
