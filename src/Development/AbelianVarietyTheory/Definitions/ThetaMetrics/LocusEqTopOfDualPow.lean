module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

noncomputable section

namespace GlobalTheory.AmpleModel

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LBGerm GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}}

variable (K : Type) [Field K] (N : ℕ)

def genericPt : ProjectiveSpectrum (grading K N) where
  asHomogeneousIdeal := ⊥
  isPrime := Ideal.isPrime_bot
  not_irrelevant_le h := by
    have := h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (X_mem K N 0))
    exact X_ne_zero _ this

instance irreducibleSpace : IrreducibleSpace (PSpace K N) := by
  have h : closure {genericPt K N} = (Set.univ : Set (ProjectiveSpectrum (grading K N))) :=
    Set.eq_univ_of_forall fun x => (ProjectiveSpectrum.le_iff_mem_closure _ _ x).1 (show ⊥ ≤ x.asHomogeneousIdeal from bot_le)
  have h2 : IsIrreducible (Set.univ : Set (ProjectiveSpectrum (grading K N))) := h ▸ isIrreducible_singleton.closure
  exact (irreducibleSpace_def _).2 h2

instance isIntegral : IsIntegral (PSpace K N) := by
  have : ∀ i, IsReduced ((chartCover K N).X i) := fun i =>
    inferInstanceAs (IsReduced (Sp (MvPolynomial {j // j ≠ i} K)))
  have : IsReduced (PSpace K N) := IsReduced.of_openCover _ (chartCover K N)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem coord_ne_top : nonzeroLocus (coord K 1 1) ≠ ⊤ := by
  intro h
  rw [nonzeroLocus_coord] at h
  have h1 : (PSpace K 1).basicOpen (ratio K 1 0 1) = chart K 1 0 :=
    basicOpen_ratioOn.trans ((congrArg (_ ⊓ ·) h).trans (inf_top_eq _))
  have h2 : IsUnit (ratio K 1 0 1) := (PSpace K 1).toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx =>
    ((PSpace K 1).mem_basicOpen _ x hx).1 (h1.ge hx)
  rw [← chartAlgEquiv_X K 1 0 ⟨1, by decide⟩] at h2
  have h3 := (h2.map (chartAlgEquiv K 1 0).symm).map constantCoeff
  rw [AlgEquiv.symm_apply_apply, constantCoeff_X] at h3
  exact not_isUnit_zero h3

end GlobalTheory.AmpleModel
