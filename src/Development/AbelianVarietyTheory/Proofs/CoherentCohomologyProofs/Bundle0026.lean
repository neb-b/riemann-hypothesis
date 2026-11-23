module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem exists_gen_theta_of_isAbelianScheme :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∀ M : LB B.left, M.IsLB → ∃ t : LB.Gen (Theta B M), t.IsGen := by
  intro K _ _ B _ hB M hM
  have := hB.comm
  exact GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety GlobalTheory.globalFns_holds K B hB (_root_.GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K B hB) M hM

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSymmetricVeryAmple
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.SymVeryAmple

theorem exists_iso_pull_of_triv {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (f : X ⟶ X)
    (h : Triv (LB.LinComb H (K := Fin 2) ![f, 𝟙 X] ![1, -1])) : ∃ w : LB.Iso H (H.pull f), w.IsGen := by
  have e := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hH _ _)).2 h
  rw [CechPic.cls_linComb hH, Fin.sum_univ_two] at e
  refine (CechPic.cls_eq_iff hH (LB.isLB_pull hH f)).1 ?_
  rw [CechPic.cls_pull hH]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, CechPic.pull_id, one_smul, neg_smul] at e
  exact (add_neg_eq_zero.1 e).symm

theorem exists_symmetric_veryAmple : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∃ (H : LB B.left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy B.hom H s ∧ ∃ w : LB.Iso H (H.pull (GrpObj.inv : B ⟶ B).left), w.IsGen := by
  intro K _ _ B _ hB
  have := hB.comm
  obtain ⟨H, m, s, hH, hs, ht⟩ := exists_symmetric_veryAmpleBy K B hB (_root_.GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K B hB)
  exact ⟨H, m, s, hH, hs, exists_iso_pull_of_triv hH _ ht⟩

end GlobalTheory.SymVeryAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteCechLineBundleHomologyStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cechLineBundle_homology : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∀ p, Module.Finite R ((cechLB f M (fun i => nonzeroLocus (s i))).homology p) := by
  first | exact @GlobalTheory.AbLaw.finite_cechLB_homology | exact GlobalTheory.AbLaw.finite_cechLB_homology | (intros; apply GlobalTheory.AbLaw.finite_cechLB_homology <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SerreVanishingH1TwistStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.serre_vanishing_h1_twist : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → FirstCohomologyVanishes (tw M H t) := by
  first | exact @GlobalTheory.AbLaw.exists_h1Zero_tw_of_veryAmpleBy | exact GlobalTheory.AbLaw.exists_h1Zero_tw_of_veryAmpleBy | (intros; apply GlobalTheory.AbLaw.exists_h1Zero_tw_of_veryAmpleBy <;> assumption)
end

