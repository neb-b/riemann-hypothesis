module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveConvex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Bundle0001

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.acyc_simp : ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, Good q T → FaceClosed (simp q T) ∧ simp q T 0 = univ ∧ Acyc (simp q T) := by
  intro E Y _ _ _ q T hG
  refine ⟨UpperTheory.V.ConeExtensionAcyclic.nerve_faceClosed _ _, ?_, ?_⟩
  · ext t
    simp only [UpperTheory.V.ConeExtensionAcyclic.simp, UpperTheory.V.ConeExtensionAcyclic.nerve, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨x, hx⟩ := hG.pos
    exact ⟨x, hx, fun j => j.elim0⟩
  · exact UpperTheory.V.ConeExtensionAcyclic.nerve_convex _ _ (UpperTheory.V.ConeExtensionAcyclic.dual_convex q T).1 hG.pos
      (fun v => ((UpperTheory.V.ConeExtensionAcyclic.dual_convex q T).2 _).1)
      (fun v => ((UpperTheory.V.ConeExtensionAcyclic.dual_convex q T).2 _).2)
      (UpperTheory.V.ConeExtensionAcyclic.cone_finite hG) (UpperTheory.V.ConeExtensionAcyclic.exists_vert hG)
