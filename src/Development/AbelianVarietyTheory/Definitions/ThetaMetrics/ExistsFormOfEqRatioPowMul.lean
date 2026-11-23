module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjSpace.Model

variable {R : Type} [CommRing R] {N : ℕ}

theorem exists_formOn (i : Fin (N + 1)) (u : Γ(PSpace R N, chart R N i)) :
    ∃ n f, ∃ hf : (f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous n,
      u = formOn (chart R N i) i le_rfl n f hf := by
  obtain ⟨p, rfl⟩ := (chartAlgEquiv R N i).surjective u
  obtain ⟨n, f, hf, h⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R N i) (polyToAway R N i p)
  refine ⟨n, f, by simpa using hf, ?_⟩
  rw [chartAlgEquiv_apply, ← h, awayToSection_mk]
  exact frac_eq rfl

theorem isIso_str_zero : IsIso (PSpace.str R 0) := by
  haveI : IsIso (chartι R 0 0) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    rw [opensRange_chartι, ← iSup_chart R 0]
    exact (iSup_unique (ι := Fin 1) (f := chart R 0)).symm
  haveI : IsEmpty {j : Fin (0 + 1) // j ≠ 0} := ⟨fun j => j.2 (Subsingleton.elim (α := Fin 1) _ _)⟩
  haveI : IsIso (chartι R 0 0 ≫ PSpace.str R 0) := by
    rw [chartι_str]
    exact inferInstanceAs (IsIso (Spec.map
      (isEmptyRingEquiv R {j : Fin (0 + 1) // j ≠ 0}).toCommRingCatIso.inv))
  exact IsIso.of_isIso_comp_left (chartι R 0 0) _

end GlobalTheory.ProjSpace.Model
