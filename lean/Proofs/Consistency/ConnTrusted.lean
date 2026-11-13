import MysqlCommon
open Aeneas Aeneas.Std mysql_common

/-! Consistency check (not a spec): models of the property axioms of `misc::trusted` in
`FunsExternal.lean` added for the connection-phase packets (`Trusted.connectAttrsEntries_new`,
`Trusted.versionReCaptures_ascii`, `Trusted.mariadbVersionReCaptures_ascii`), so that, together
with the opaque constants they constrain, they have a model and cannot prove `False`. Each
theorem below restates one axiom for the model; if an axiom changes, restate it here.

* Connect attributes: a map is a list of entries, `new` is empty (as in `ParamsMap.lean`).
* Version regexes: the captures are the ASCII-semantics groups (`Trusted.versionReMatch`,
  `Trusted.mariadbVersionReMatch`) on every input, as slices (every group has at most 3 bytes). -/

namespace ConnModel

abbrev RB := misc.raw.bytes.RawBytes misc.raw.int.LenEnc Unit
abbrev ConnectAttrs := List (Slice U8 × Slice U8)
def connectAttrsNew : ConnectAttrs := []
def connectAttrsEntries (m : ConnectAttrs) : alloc.vec.Vec (Slice U8 × Slice U8) :=
  if h : m.length ≤ Usize.max then alloc.vec.Vec.from m h else alloc.vec.Vec.new _

-- axiom connectAttrsEntries_new
theorem connectAttrsEntries_new : (connectAttrsEntries connectAttrsNew).val = [] := by
  simp [connectAttrsEntries, connectAttrsNew]

/-- A group of at most 3 bytes as a slice. -/
def mk (l : List U8) : Slice U8 := Slice.from (l.take 3) (by simp; scalar_tac)

def capt (o : Option (List U8 × List U8 × List U8)) : Option (Slice U8 × Slice U8 × Slice U8) :=
  o.map (fun t => (mk t.1, mk t.2.1, mk t.2.2))

def versionReCaptures (s : Slice U8) := capt (Trusted.versionReMatch s.val)
def mariadbVersionReCaptures (s : Slice U8) := capt (Trusted.mariadbVersionReMatch s.val)

theorem reTwoGroups_len {bs a b r : List U8} (h : Trusted.reTwoGroups bs = some (a, b, r)) :
    a.length ≤ 2 ∧ b.length ≤ 2 := by
  unfold Trusted.reTwoGroups at h
  dsimp only at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      omega
    · simp at h
  · simp at h

theorem versionReMatch_len {bs a b c : List U8} (h : Trusted.versionReMatch bs = some (a, b, c)) :
    a.length ≤ 3 ∧ b.length ≤ 3 ∧ c.length ≤ 3 := by
  unfold Trusted.versionReMatch at h
  dsimp only at h
  split at h
  · rename_i g1 g2 r hg
    have := reTwoGroups_len hg
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp; omega
    · simp at h
  · simp at h

theorem reMariadbCore_len {bs a b c : List U8} (h : Trusted.reMariadbCore bs = some (a, b, c)) :
    a.length ≤ 3 ∧ b.length ≤ 3 ∧ c.length ≤ 3 := by
  unfold Trusted.reMariadbCore at h
  split at h
  · rename_i g1 g2 r hg
    have := reTwoGroups_len hg
    unfold Trusted.reMariadbTail at h
    dsimp only at h
    split at h
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      omega
    · simp at h
  · simp at h

theorem mariadbVersionReMatch_len {bs a b c : List U8}
    (h : Trusted.mariadbVersionReMatch bs = some (a, b, c)) :
    a.length ≤ 3 ∧ b.length ≤ 3 ∧ c.length ≤ 3 := by
  unfold Trusted.mariadbVersionReMatch at h
  dsimp only at h
  split at h
  · rename_i g hg
    split at hg
    · cases h; exact reMariadbCore_len hg
    · simp at hg
  · exact reMariadbCore_len h

theorem capt_val (o : Option (List U8 × List U8 × List U8))
    (h : ∀ a b c, o = some (a, b, c) → a.length ≤ 3 ∧ b.length ≤ 3 ∧ c.length ≤ 3) :
    Trusted.capturesVal (capt o) = o := by
  rcases o with _ | ⟨a, b, c⟩
  · rfl
  · obtain ⟨ha, hb, hc⟩ := h a b c rfl
    simp [capt, Trusted.capturesVal, mk, List.take_of_length_le ha, List.take_of_length_le hb,
      List.take_of_length_le hc]

-- axiom versionReCaptures_ascii
theorem versionReCaptures_ascii (s : Slice U8) (_h : ∀ b ∈ s.val, b.val < 128) :
    Trusted.capturesVal (versionReCaptures s) = Trusted.versionReMatch s.val :=
  capt_val _ (fun _ _ _ h => versionReMatch_len h)

-- axiom mariadbVersionReCaptures_ascii
theorem mariadbVersionReCaptures_ascii (s : Slice U8) (_h : ∀ b ∈ s.val, b.val < 128) :
    Trusted.capturesVal (mariadbVersionReCaptures s) = Trusted.mariadbVersionReMatch s.val :=
  capt_val _ (fun _ _ _ h => mariadbVersionReMatch_len h)

end ConnModel
#print axioms ConnModel.connectAttrsEntries_new
#print axioms ConnModel.versionReCaptures_ascii
#print axioms ConnModel.mariadbVersionReCaptures_ascii
