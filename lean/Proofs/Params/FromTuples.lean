import Defs

/-! Statements for the tuple impls `From<(A, ..)> for Params` (`into_params_impl!`, arities 1 to
12) (spec file: `Specs/Params.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `From<(A,)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
theorem params.Params.Insts.CoreConvertFromTupleA.from_spec {A : Type}
    (instA : core.convert.Into A value.Value)
    (a : A) (va : value.Value)
    (ha : instA.into a = ok va) :
    params.Params.Insts.CoreConvertFromTupleA.from instA a ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va] ⦄ := by
  sorry

/-- `From<(A, B)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
theorem params.Params.Insts.CoreConvertFromPair.from_spec {A : Type} {B : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value)
    (a : A) (b : B) (va : value.Value) (vb : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) :
    params.Params.Insts.CoreConvertFromPair.from instA instB (a, b) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb] ⦄ := by
  sorry

/-- `From<(A, B, C)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
theorem params.Params.Insts.CoreConvertFromTupleABC.from_spec {A : Type} {B : Type} {C : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value)
    (a : A) (b : B) (c : C) (va : value.Value) (vb : value.Value) (vc : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) :
    params.Params.Insts.CoreConvertFromTupleABC.from instA instB instC (a, b, c) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc] ⦄ := by
  sorry

/-- `From<(A, B, C, D)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
theorem params.Params.Insts.CoreConvertFromTupleABCD.from_spec {A : Type} {B : Type} {C : Type} {D : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value)
    (a : A) (b : B) (c : C) (d : D) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) :
    params.Params.Insts.CoreConvertFromTupleABCD.from instA instB instC instD (a, b, c, d) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd] ⦄ := by
  sorry

/-- `From<(A, B, C, D, E)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
theorem params.Params.Insts.CoreConvertFromTupleABCDE.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) :
    params.Params.Insts.CoreConvertFromTupleABCDE.from instA instB instC instD instE (a, b, c, d, e) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve] ⦄ := by
  sorry

/-- `From<(A, B, C, D, E, F)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
theorem params.Params.Insts.CoreConvertFromTupleABCDEF.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) :
    params.Params.Insts.CoreConvertFromTupleABCDEF.from instA instB instC instD instE instF (a, b, c, d, e, f) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf] ⦄ := by
  sorry

/-- `From<(A, B, C, D, E, F, G)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
theorem params.Params.Insts.CoreConvertFromTupleABCDEFG.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type} {G : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value) (instG : core.convert.Into G value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (g : G) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value) (vg : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) (hg : instG.into g = ok vg) :
    params.Params.Insts.CoreConvertFromTupleABCDEFG.from instA instB instC instD instE instF instG (a, b, c, d, e, f, g) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf, vg] ⦄ := by
  sorry

/-- `From<(A, B, C, D, E, F, G, H)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
theorem params.Params.Insts.CoreConvertFromTupleABCDEFGH.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type} {G : Type} {H : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value) (instG : core.convert.Into G value.Value) (instH : core.convert.Into H value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (g : G) (h : H) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value) (vg : value.Value) (vh : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) (hg : instG.into g = ok vg) (hh : instH.into h = ok vh) :
    params.Params.Insts.CoreConvertFromTupleABCDEFGH.from instA instB instC instD instE instF instG instH (a, b, c, d, e, f, g, h) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf, vg, vh] ⦄ := by
  sorry

/-- `From<(A, B, C, D, E, F, G, H, I)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
theorem params.Params.Insts.CoreConvertFromTupleABCDEFGHI.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type} {G : Type} {H : Type} {I : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value) (instG : core.convert.Into G value.Value) (instH : core.convert.Into H value.Value) (instI : core.convert.Into I value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (g : G) (h : H) (i : I) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value) (vg : value.Value) (vh : value.Value) (vi : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) (hg : instG.into g = ok vg) (hh : instH.into h = ok vh) (hi : instI.into i = ok vi) :
    params.Params.Insts.CoreConvertFromTupleABCDEFGHI.from instA instB instC instD instE instF instG instH instI (a, b, c, d, e, f, g, h, i) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf, vg, vh, vi] ⦄ := by
  sorry

/-- `From<(A, B, C, D, E, F, G, H, I, J)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
theorem params.Params.Insts.CoreConvertFromTupleABCDEFGHIJ.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type} {G : Type} {H : Type} {I : Type} {J : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value) (instG : core.convert.Into G value.Value) (instH : core.convert.Into H value.Value) (instI : core.convert.Into I value.Value) (instJ : core.convert.Into J value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (g : G) (h : H) (i : I) (j : J) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value) (vg : value.Value) (vh : value.Value) (vi : value.Value) (vj : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) (hg : instG.into g = ok vg) (hh : instH.into h = ok vh) (hi : instI.into i = ok vi) (hj : instJ.into j = ok vj) :
    params.Params.Insts.CoreConvertFromTupleABCDEFGHIJ.from instA instB instC instD instE instF instG instH instI instJ (a, b, c, d, e, f, g, h, i, j) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf, vg, vh, vi, vj] ⦄ := by
  sorry

/-- `From<(A, B, C, D, E, F, G, H, I, J, K)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
theorem params.Params.Insts.CoreConvertFromTupleABCDEFGHIJK.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type} {G : Type} {H : Type} {I : Type} {J : Type} {K : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value) (instG : core.convert.Into G value.Value) (instH : core.convert.Into H value.Value) (instI : core.convert.Into I value.Value) (instJ : core.convert.Into J value.Value) (instK : core.convert.Into K value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (g : G) (h : H) (i : I) (j : J) (k : K) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value) (vg : value.Value) (vh : value.Value) (vi : value.Value) (vj : value.Value) (vk : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) (hg : instG.into g = ok vg) (hh : instH.into h = ok vh) (hi : instI.into i = ok vi) (hj : instJ.into j = ok vj) (hk : instK.into k = ok vk) :
    params.Params.Insts.CoreConvertFromTupleABCDEFGHIJK.from instA instB instC instD instE instF instG instH instI instJ instK (a, b, c, d, e, f, g, h, i, j, k) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk] ⦄ := by
  sorry

/-- `From<(A, B, C, D, E, F, G, H, I, J, K, L)> for Params`: `Positional` of the converted elements, in order (when each
    conversion returns). -/
theorem params.Params.Insts.CoreConvertFromTupleABCDEFGHIJKL.from_spec {A : Type} {B : Type} {C : Type} {D : Type} {E : Type} {F : Type} {G : Type} {H : Type} {I : Type} {J : Type} {K : Type} {L : Type}
    (instA : core.convert.Into A value.Value) (instB : core.convert.Into B value.Value) (instC : core.convert.Into C value.Value) (instD : core.convert.Into D value.Value) (instE : core.convert.Into E value.Value) (instF : core.convert.Into F value.Value) (instG : core.convert.Into G value.Value) (instH : core.convert.Into H value.Value) (instI : core.convert.Into I value.Value) (instJ : core.convert.Into J value.Value) (instK : core.convert.Into K value.Value) (instL : core.convert.Into L value.Value)
    (a : A) (b : B) (c : C) (d : D) (e : E) (f : F) (g : G) (h : H) (i : I) (j : J) (k : K) (l : L) (va : value.Value) (vb : value.Value) (vc : value.Value) (vd : value.Value) (ve : value.Value) (vf : value.Value) (vg : value.Value) (vh : value.Value) (vi : value.Value) (vj : value.Value) (vk : value.Value) (vl : value.Value)
    (ha : instA.into a = ok va) (hb : instB.into b = ok vb) (hc : instC.into c = ok vc) (hd : instD.into d = ok vd) (he : instE.into e = ok ve) (hf : instF.into f = ok vf) (hg : instG.into g = ok vg) (hh : instH.into h = ok vh) (hi : instI.into i = ok vi) (hj : instJ.into j = ok vj) (hk : instK.into k = ok vk) (hl : instL.into l = ok vl) :
    params.Params.Insts.CoreConvertFromTupleABCDEFGHIJKL.from instA instB instC instD instE instF instG instH instI instJ instK instL (a, b, c, d, e, f, g, h, i, j, k, l) ⦃ p => ∃ w, p = .Positional w ∧ w.val = [va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk, vl] ⦄ := by
  sorry

end mysql_common
