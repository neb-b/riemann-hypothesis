module

public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusA

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.AddAcyclic
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual


set_option maxHeartbeats 1000000 in
theorem addAcyclic_pf : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ M : LB A.left, ∀ hM : M.IsLB, (∀ (Y : Over (Sp k)) (a a' : Y ⟶ A), GlobalTheory.CechPic.pull (a * a').left (cls M hM) = GlobalTheory.CechPic.pull a.left (cls M hM) + GlobalTheory.CechPic.pull a'.left (cls M hM)) → ¬ Triv M → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB A.hom M D).Acyclic := by
  intro k _ _ A _ hA M hM hadd hn κ _ _ D hD hc
  have : IsCommMonObj A := hA.comm
  have hp : IsProjBy A.hom := _root_.GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme k A hA
  refine _root_.GlobalTheory.PrimVan.acyclic_cechLB_of_primitive k A hA hp M hM ?_ hn κ D hD hc
  have hlam : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  refine (GlobalTheory.CechPic.cls_eq_zero_iff hlam).1 ?_
  refine (GlobalTheory.CechPic.cls_cube_two hM (fst A A) (snd A A) hlam).trans ?_
  have h1 := hadd (A ⊗ A) (fst A A) (snd A A)
  have h0 := hadd (A ⊗ A) 1 1
  rw [_root_.mul_one] at h0
  have h0' : GlobalTheory.CechPic.pull (1 : A ⊗ A ⟶ A).left (cls M hM) = 0 := by
    exact add_left_cancel (h0.symm.trans (add_zero _).symm)
  simp only [GlobalTheory.CechPic.lam, h1, h0']
  abel

end CompanionTheory.PfDual
end

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusB
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace CompanionTheory.PfDual


open GlobalTheory.TrivSubscheme in
theorem exists_closed_locTriv_noeth : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → IsLocallyNoetherian Y.left → ∀ F : LB (A ⊗ Y).left, F.IsLB → ∃ (H : Over S) (j : H ⟶ Y), IsClosedImmersion j.left ∧ ∀ (T' : Over S) (x : T' ⟶ Y), (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧ Triv ((F.pull (A ◁ x).left).pull ((snd A T').left ⁻¹ᵁ U).ι)) ↔ ∃ y : T' ⟶ H, y ≫ j = x := by
  intro S A Y _ hB hY F hF
  have h₀ : IsPullback (pullback.fst A.hom Y.hom) (snd A Y).left A.hom Y.hom :=
    IsPullback.of_hasPullback A.hom Y.hom
  obtain ⟨I, hI⟩ := GlobalTheory.TrivSubscheme.exists_idealSheaf
    (GlobalTheory.TrivSubscheme.LocTrivOver (snd A Y).left F)
    GlobalTheory.TrivSubscheme.LocTrivOver.comp GlobalTheory.TrivSubscheme.locTrivOver_of_affine
    (fun U => by
      haveI : IsNoetherianRing Γ(Y.left, U) := IsLocallyNoetherian.component_noetherian U
      let t : Spec (CommRingCat.of Γ(Y.left, U)) ⟶ S := U.2.fromSpec ≫ Y.hom
      have h₁ : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom (U.2.fromSpec ≫ Y.hom) :=
        IsPullback.of_hasPullback _ _
      let φ := h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)
      have h₂ : IsPullback φ (pullback.snd A.hom t) (snd A Y).left U.2.fromSpec :=
        IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀
      obtain ⟨I, hI⟩ := exists_ideal_locTriv_noeth Γ(Y.left, U) ((Over.pullback t).obj A)
        (CubeGen.isAb_baseChange hB t) (F.pull φ) (LB.isLB_pull hF φ)
      refine ⟨I, fun S g => ?_⟩
      have h₃ := IsPullback.of_hasPullback (pullback.snd A.hom t) (Spec.map g)
      rw [← hI S g.hom _ _ _ h₃,
        GlobalTheory.TrivSubscheme.locTrivOver_iff (h₃.paste_horiz h₂)]
      refine forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_
      rw [← Category.assoc]
      exact ((GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _).trans
        (GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _)).symm)
  refine ⟨Over.mk (I.subschemeι ≫ Y.hom), Over.homMk I.subschemeι rfl,
    inferInstanceAs (IsClosedImmersion I.subschemeι), fun T' x => ?_⟩
  have h₄ : IsPullback (A ◁ x).left (snd A T').left (snd A Y).left x.left := by
    refine IsPullback.of_right ?_ (Over.whiskerLeft_left_snd x) h₀
    rw [Over.whiskerLeft_left_fst, Over.w x]
    exact IsPullback.of_hasPullback A.hom T'.hom
  simp only [GlobalTheory.TrivSubscheme.triv_pull_iff]
  rw [← GlobalTheory.TrivSubscheme.locTrivOver_iff h₄, hI]
  constructor
  · intro h
    have h' : I.subschemeι.ker ≤ x.left.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι x.left h') ?_, ?_⟩
    · exact (IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w x)
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  · rintro ⟨y, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp y.left I.subschemeι)

end CompanionTheory.PfDual
end
end

