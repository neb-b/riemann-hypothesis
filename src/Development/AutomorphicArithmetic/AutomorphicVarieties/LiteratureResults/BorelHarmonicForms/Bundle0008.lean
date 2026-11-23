module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.TformPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneReal
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct ComplexOrder

theorem UpperTheory.V.Lit.Bor.oneReal :
    UpperTheory.V.Lit.Bor.OneReal := by
  intro E _ _ _ a Ξ
  obtain ⟨hL, hS⟩ := xiSchur E a Ξ
  obtain ⟨G, hG, hadj⟩ := admEx E a Ξ
  have h1 : oneL E a = toL (1 : Matrix (Fin a) (Fin a) (Cinf E)) := rfl
  obtain ⟨c, hc⟩ := hS (Ξ.dmat (oneL E a)) fun X => by
    have h := hL 1 (Matrix.of X)
    rw [one_mul, mul_one, sub_self] at h
    have h0 : toL (0 : Matrix (Fin a) (Fin a) (Cinf E)) = 0 := rfl
    rw [h0, map_zero, sub_eq_zero] at h
    exact h
  have h := hadj 1
  rw [star_one, ← h1, hc, conjTranspose_smul, conjTranspose_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at h
  refine ⟨c.re, ?_⟩
  unfold HasOne
  rw [hc]
  ext i j
  have hi := congrFun (congrFun h i) i
  have hp : G i i ≠ 0 := (hG.diag_pos (i := i)).ne'
  simp only [Matrix.smul_apply, smul_eq_mul] at hi
  have hs : star c = c := mul_right_cancel₀ hp hi
  rw [← Complex.conj_eq_iff_re.1 hs]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.PiForm
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.piForm :
    UpperTheory.V.Lit.Bor.PiForm := by
  intro E _ _ _ a ha π Ξ r hone
  obtain ⟨G, hG⟩ := admEx E a Ξ
  obtain ⟨H, hH⟩ := petEx E a ha r
  obtain ⟨hinj, hcmp, -, hlie, hadj⟩ := inclFacts E a π Ξ r
  have hpos := tformPos _ Ξ.d H _ G hH.pos hG.pos
  have hmem : ∀ m, incl π Ξ m ∈ tens Ξ.d (sqSub E a r) := fun m =>
    mem_tens.2 fun i => by
      rw [hcmp]
      exact Submodule.subset_span (cuspSq E a ha π r hone _ (UpperTheory.V.Lit.Bor.cmp i m).2)
  refine ⟨((tform H G) ∘ₛₗ (incl π Ξ)).compl₂ (incl π Ξ), ⟨fun x y => ?_, fun x _ => ?_, fun x _ hx => ?_⟩,
    fun X x y => ?_⟩
  · exact hpos.herm _ _
  · exact hpos.nonneg _ (hmem x)
  · exact hinj ((hpos.definite _ (hmem x) hx).trans (map_zero _).symm)
  · show tform H G (incl π Ξ x) (incl π Ξ _) = tform H G (incl π Ξ _) (incl π Ξ y)
    rw [hlie, hadj]
    exact smForm E a Ξ r H G hH hG X _ (hmem x) _ (hmem y)
end

