module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitUniformisationPullbackFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitExt

theorem exists_fracHom {R R₁ M : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] [Field M] [IsAlgClosed M]
    (ρ : R →+* R₁) (hρ : Function.Injective ρ) (hfin : ρ.Finite) (g : R →+* M) (hg : Function.Injective g) :
    ∃ e : FractionRing R₁ →+* M, ∀ r, e (algebraMap R₁ (FractionRing R₁) (ρ r)) = g r := by
  letI : Algebra R R₁ := ρ.toAlgebra
  letI : Algebra R M := g.toAlgebra
  have hinj : Function.Injective (algebraMap R (FractionRing R₁)) := by
    rw [IsScalarTower.algebraMap_eq R R₁ (FractionRing R₁)]
    exact (IsFractionRing.injective R₁ (FractionRing R₁)).comp hρ
  haveI : Module.IsTorsionFree R (FractionRing R₁) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hinj
  haveI : Module.IsTorsionFree R M := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hg
  haveI : Algebra.IsIntegral R R₁ := ⟨fun x => hfin.to_isIntegral x⟩
  haveI : Algebra.IsAlgebraic R R₁ := Algebra.IsIntegral.isAlgebraic
  haveI : Algebra.IsAlgebraic R (FractionRing R₁) :=
    (IsFractionRing.isAlgebraic_iff' R R₁ (FractionRing R₁)).1 inferInstance
  refine ⟨(IsAlgClosed.lift : FractionRing R₁ →ₐ[R] M).toRingHom, fun r => ?_⟩
  have h := (IsAlgClosed.lift : FractionRing R₁ →ₐ[R] M).commutes r
  rw [IsScalarTower.algebraMap_apply R R₁ (FractionRing R₁)] at h
  exact h

end GlobalTheory.Mum.TraitExt

namespace GlobalTheory.Mum.TraitExt

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem unifTrait_pull : ∀ (R R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁]
    (ρ : R →+* R₁), Base R → FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D₁ : DegData R₁ (maximalIdeal R₁)),
    Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₁ : Over (Sp R₁))
    [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G₁ G (spMap ρ) β₁ →
    ∀ L : LB G.left, L.IsLB → UnifTrait D G L → UnifTrait D₁ G₁ (L.pull β₁) := by
  intro R R₁ _ _ _ _ _ _ ρ hR hfin D D₁ hρD G _ _ G₁ _ _ β₁ hG hpb L hL hU
  obtain ⟨hρD⟩ := hρD
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, hφi, hφl, hpb', hLB, ⟨hD⟩⟩ := hU
  have hgi : Function.Injective
      ((algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp φ)) :=
    (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφi)
  obtain ⟨e, he⟩ := exists_fracHom ρ hfin.2.1 hfin.2.2 _ hgi
  obtain ⟨W₁, _, _, _, iw, φ₁, -, hW₁, hiwi, -, hiwl, hφ₁i, hφ₁l, hcomm, -, -⟩ :=
    _root_.GlobalTheory.TraitExt.exists_finite_trait_extension R W R₁ hW φ hφi hφl ρ hfin (Kb W) e he
  have hAW : AdmBase W (maximalIdeal W) := by
    haveI := hW.1; exact ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hAW₁ : AdmBase W₁ (maximalIdeal W₁) := by
    haveI := hW₁.1; exact ⟨inferInstance, inferInstance, inferInstance, hW₁.2.1⟩
  have hG' : IsSemiAbelian G' := by
    obtain ⟨eI, heI, -⟩ := grpPullback_iso hpb' (isGrpPullback_pullback G (spMap φ))
    haveI := heI
    exact GlobalTheory.isSemiAbelian_of_grpIso eI (IsSemiAbelian.pullback _ G hG)
  obtain ⟨hL5, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D'', hD'', A'', U'', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL5.polBaseChange h4.unifBaseChange
    h5.psiOnExists hAW hAW₁ iw hiwi (map_maximalIdeal_le iw) hG' U'
  have hpb1 : IsGrpPullback ((Over.pullback (specOf iw)).obj G') G' (spMap iw) (pullback.fst G'.hom (specOf iw)) :=
    isGrpPullback_pullback G' (spMap iw)
  have hsp : spMap iw ≫ spMap φ = spMap φ₁ ≫ spMap ρ := by
    rw [spMap_comp, spMap_comp, hcomm]
  have hpb2 := hpb1.comp hpb'
  have hsq : (pullback.fst G'.hom (specOf iw) ≫ β) ≫ G.hom =
      ((Over.pullback (specOf iw)).obj G').hom ≫ spMap φ₁ ≫ spMap ρ := by
    rw [← hsp, Category.assoc, hpb'.1.w, ← Category.assoc, pullback.condition]
    rfl
  set β'' : ((Over.pullback (specOf iw)).obj G').left ⟶ G₁.left :=
    hpb.1.lift (pullback.fst G'.hom (specOf iw) ≫ β) (((Over.pullback (specOf iw)).obj G').hom ≫ spMap φ₁) hsq
    with hβ''
  have hβ1 : β'' ≫ β₁ = pullback.fst G'.hom (specOf iw) ≫ β := hpb.1.lift_fst _ _ _
  have hβ2 : β'' ≫ G₁.hom = ((Over.pullback (specOf iw)).obj G').hom ≫ spMap φ₁ := hpb.1.lift_snd _ _ _
  have hpb3 : IsGrpPullback ((Over.pullback (specOf iw)).obj G') G₁ (spMap φ₁) β'' :=
    hpb.cancel (hpb2.congr hsp hβ1.symm) hβ2
  obtain ⟨h, -, -⟩ := _root_.GlobalTheory.Mum.isPullDeg_square R R₁ W W₁ _ _ _ _ hR.1 hfin.1 hAW hAW₁ ρ φ iw φ₁ hcomm hφ₁i hfin.2.1 hφi hiwi
    D D₁ D' D'' hρD hD hD''
  have hw1 : LBIso U''.LG.L
      (U'.LG.L.pull ((Iso.refl ((Over.pullback (specOf iw)).obj G')).hom.left ≫ pullback.fst G'.hom (specOf iw))) :=
    ⟨hP.lg.choose, hP.lg.choose_spec.1⟩
  have hw2 : LBIso (U'.LG.L.pull ((Iso.refl ((Over.pullback (specOf iw)).obj G')).hom.left ≫
      pullback.fst G'.hom (specOf iw))) (L.pull (pullback.fst G'.hom (specOf iw) ≫ β)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull hLB _ (by simp)
  have hw3 : LBIso (L.pull (pullback.fst G'.hom (specOf iw) ≫ β)) ((L.pull β₁).pull β'') :=
    GlobalTheory.AlgUniq.lbIso_pull_comp hL β₁ β'' _ hβ1
  have hw : LBIso U''.LG.L ((L.pull β₁).pull β'') :=
    LBIso.trans U''.LG.isLB (pull_isLB U'.LG.isLB _) (pull_isLB (pull_isLB hL _) _) hw1
      (LBIso.trans (pull_isLB U'.LG.isLB _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) hw2 hw3)
  exact ⟨W₁, inferInstance, inferInstance, inferInstance, φ₁, (Over.pullback (specOf iw)).obj G', inferInstance,
    inferInstance, β'', D'', A'', U'', hW₁, hφ₁i, hφ₁l, hpb3, hw, ⟨h⟩⟩

end GlobalTheory.Mum.TraitExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffCompHolomorphicJacobianSq
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.ChartGlue GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ComplexConjugate

namespace GlobalTheory.GoodTop.CorrHolo

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

def coordMat (L : V n →L[ℂ] V n) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c a => L (coordVec a) c

variable {φ : V n → V n} {w : V n}

end GlobalTheory.GoodTop.CorrHolo

namespace GlobalTheory.GoodTop

open CorrHolo

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
private lemma apply_coordVec_eq_sum_coordMat {n : ℕ} (L : _root_.ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n)
    (a : Fin n) : L (_root_.GlobalTheory.GoodMetric.coordVec a) =
      ∑ c, _root_.GlobalTheory.GoodTop.CorrHolo.coordMat L c a • _root_.GlobalTheory.GoodMetric.coordVec c :=
  _root_.GlobalTheory.LineForm.chain_sum_coordVec _

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
private lemma mdel_sum_smul_coordVec {n : ℕ} {r : Type}
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (x : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.mdel G z (∑ c, x c • _root_.GlobalTheory.GoodMetric.coordVec c) =
      ∑ c, x c • _root_.GlobalTheory.HermFrame.mdel G z (_root_.GlobalTheory.GoodMetric.coordVec c) := by
  ext i j
  simp [_root_.GlobalTheory.HermFrame.mdel_apply, Matrix.sum_apply]

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
private lemma mdbar_sum_smul_coordVec {n : ℕ} {r : Type}
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (y : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.mdbar G z (∑ d, y d • _root_.GlobalTheory.GoodMetric.coordVec d) =
      ∑ d, starRingEnd ℂ (y d) • _root_.GlobalTheory.HermFrame.mdbar G z (_root_.GlobalTheory.GoodMetric.coordVec d) := by
  ext i j
  simp [_root_.GlobalTheory.HermFrame.mdbar_apply, Matrix.sum_apply]

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
private lemma mddbar_sum_smul_coordVec {n : ℕ} {r : Type}
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (x y : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.mddbar G z (∑ c, x c • _root_.GlobalTheory.GoodMetric.coordVec c)
        (∑ d, y d • _root_.GlobalTheory.GoodMetric.coordVec d) =
      ∑ c, ∑ d, (x c * starRingEnd ℂ (y d)) •
        _root_.GlobalTheory.HermFrame.mddbar G z (_root_.GlobalTheory.GoodMetric.coordVec c) (_root_.GlobalTheory.GoodMetric.coordVec d) := by
  ext i j
  simp [_root_.GlobalTheory.HermFrame.mddbar_apply, Matrix.sum_apply, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
private lemma curv_sum_smul_coordVec {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (hG : _root_.GlobalTheory.HermFrame.MContDiffAt 2 G z)
    (hu : IsUnit (G z).det) (x y : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.curv G z (∑ c, x c • _root_.GlobalTheory.GoodMetric.coordVec c)
        (∑ d, y d • _root_.GlobalTheory.GoodMetric.coordVec d) =
      ∑ c, ∑ d, (x c * starRingEnd ℂ (y d)) •
        _root_.GlobalTheory.HermFrame.curv G z (_root_.GlobalTheory.GoodMetric.coordVec c) (_root_.GlobalTheory.GoodMetric.coordVec d) := by
  simp only [_root_.GlobalTheory.HermFrame.curv_eq hG hu, mdel_sum_smul_coordVec,
    mdbar_sum_smul_coordVec, mddbar_sum_smul_coordVec,
    Matrix.transpose_sum, Matrix.transpose_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.smul_sum]

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
private lemma conn_sum_smul {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (x : Fin n → ℂ) (v : Fin n → _root_.ReciprocityTheory.L2DbarEstimates.V n) :
    _root_.GlobalTheory.HermFrame.conn G z (∑ c, x c • v c) =
      ∑ c, x c • _root_.GlobalTheory.HermFrame.conn G z (v c) := by
  let f : _root_.ReciprocityTheory.L2DbarEstimates.V n →+ Matrix r r ℂ :=
    { toFun := _root_.GlobalTheory.HermFrame.conn G z
      map_zero' := by simpa using _root_.GlobalTheory.HermFrame.conn_smul_vec G z 0 0
      map_add' := _root_.GlobalTheory.HermFrame.conn_add_vec G z }
  change f (∑ c, x c • v c) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun c _ => _root_.GlobalTheory.HermFrame.conn_smul_vec G z (x c) (v c)


set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
theorem _root_.GlobalTheory.GoodTop.corrC_comp_holo {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ}
    {φ : _root_.ReciprocityTheory.L2DbarEstimates.V n → _root_.ReciprocityTheory.L2DbarEstimates.V n} {w : _root_.ReciprocityTheory.L2DbarEstimates.V n} (hφ : ContDiffAt ℂ 2 φ w)
    (hρ : DifferentiableAt ℝ ρ (φ w))
    (h₀ : _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₀ (φ w)) (u₀ : IsUnit (G₀ (φ w)).det)
    (h₁ : _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₁ (φ w))
    (u₁ : IsUnit (G₁ (φ w)).det) :
    _root_.GlobalTheory.GoodTop.corrC (fun x => ρ (φ x)) (fun x => G₀ (φ x)) (fun x => G₁ (φ x)) w =
      ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ (φ w) := by
  have hφd : DifferentiableAt ℂ φ w := hφ.differentiableAt (by norm_num)
  have h₀' : _root_.GlobalTheory.HermFrame.MContDiffAt 1 G₀ (φ w) := fun a b => (h₀ a b).of_le (by norm_num)
  have h₁' : _root_.GlobalTheory.HermFrame.MContDiffAt 1 G₁ (φ w) := fun a b => (h₁ a b).of_le (by norm_num)
  obtain ⟨J, hJ⟩ : ∃ J, J = _root_.GlobalTheory.GoodTop.CorrHolo.coordMat (fderiv ℂ φ w) := ⟨_, rfl⟩
  have hL : ∀ a, fderiv ℂ φ w (_root_.GlobalTheory.GoodMetric.coordVec a) =
      ∑ c, J c a • _root_.GlobalTheory.GoodMetric.coordVec c := by
    intro a
    rw [hJ]
    exact apply_coordVec_eq_sum_coordMat _ a
  have hcurv : ∀ G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G (φ w) →
      IsUnit (G (φ w)).det → _root_.GlobalTheory.GoodTop.curvAt (fun x => G (φ x)) w =
        fun a b => ∑ c, ∑ d, (J c a * (J.map (starRingEnd ℂ)) d b) •
          _root_.GlobalTheory.GoodTop.curvAt G (φ w) c d := by
    intro G hG hu
    funext a b
    simp only [_root_.GlobalTheory.GoodTop.curvAt, Matrix.map_apply]
    rw [_root_.GlobalTheory.HermFrame.curv_comp_holo hG hu hφ, hL, hL,
      curv_sum_smul_coordVec G _ hG hu]
  have hρc : DifferentiableAt ℝ (fun y => (ρ y : ℂ)) (φ w) :=
    Complex.ofRealCLM.differentiableAt.comp _ hρ
  have hdbar : _root_.GlobalTheory.GoodTop.cutForm (fun x => ρ (φ x)) (fun x => G₀ (φ x))
      (fun x => G₁ (φ x)) w = fun a b => ∑ c, ∑ d, (J c a * (J.map (starRingEnd ℂ)) d b) •
        _root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ (φ w) c d := by
    funext a b
    simp only [_root_.GlobalTheory.GoodTop.cutForm, Matrix.map_apply]
    have hw := _root_.GlobalTheory.dbar_comp_holo (u := fun y => (ρ y : ℂ)) hρc hφd

    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw, _root_.GlobalTheory.HermFrame.conn_comp_holo h₁' hφd,
      _root_.GlobalTheory.HermFrame.conn_comp_holo h₀' hφd, hL, hL, conn_sum_smul,
      conn_sum_smul, map_sum, ← Finset.sum_sub_distrib, Finset.sum_smul]
    simp only [map_smulₛₗ, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [← smul_sub, smul_smul, smul_eq_mul]
    congr 1
    ring
  have hdet : J.det * (J.map (starRingEnd ℂ)).det = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : J.det = (fderiv ℂ φ w).det := by
      have hJm : J = LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (fderiv ℂ φ w : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) := by
        ext c a
        simp [hJ, _root_.GlobalTheory.GoodTop.CorrHolo.coordMat, LinearMap.toMatrix_apply,
          _root_.GlobalTheory.GoodMetric.coordVec]
      rw [hJm, LinearMap.det_toMatrix]
    have h2 : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det :=
      (RingHom.map_det (starRingEnd ℂ) J).symm
    rw [h2, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
  unfold _root_.GlobalTheory.GoodTop.corrC
  rw [hcurv G₁ h₁ u₁, hcurv G₀ h₀ u₀, hdbar, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hdet, ← _root_.GlobalTheory.GoodTop.mixTop_subst]
  congr 1
  funext i a b
  unfold _root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one
  split_ifs <;> rfl

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCoordinateRatioFibreInvariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TwCoordInv

open GlobalTheory.CoordCompare TorusCoord

theorem ratio_translate_invariant : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] [Mono β.left], g₂.pG ≫ β = g.pG → ∀ (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)) (χ₂ : D₂.X) (χ : D.X), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A → r ≫ g₂.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D₂.P.A → val (g.t χ) r z J = val (g₂.t χ₂) r z J') → ∀ (a : 𝟙_ (Over (Sp R)) ⟶ G) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → r ≫ g.q.left = r' ≫ g.q.left → val (g.t χ) (r ≫ h) z J * ((∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' * val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ = val (g.t χ) (r' ≫ h) z J * ((∏ k, gv w (r' ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r' ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r' ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r' z J' * val (gp.s χ) (r' ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ := by
  intro R _ _ I D D₂ e G _ _ g g₂ β _ _ hβ gp w χ₂ χ hker a₀ h hh hf Z r r' z J J' hJ hJ' hq
  obtain ⟨h₁, h₂⟩ := ratio_invariant g g₂ β hβ χ χ₂ hker r r' z J J' hJ hJ' hq
  have hw : r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom := by
    rw [← Over.w g.q, reassoc_of% hq]
  have hprod : ∀ k, r ≫ D₂.Oφ g₂.pG χ₂ k = r' ≫ D₂.Oφ g₂.pG χ₂ k := fun k =>
    Oφ_congr χ₂ g₂.pG r r' h₁ k
  let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (r' ≫ (thickObj R I e G).hom)
  let b : Z' ⟶ thickObj R I e G := Over.homMk r hw
  let b' : Z' ⟶ thickObj R I e G := Over.homMk r' rfl
  obtain ⟨τ, hτ⟩ := exists_torus g b b' (Over.OverMorphism.ext hq)
  let hO : thickObj R I e G ⟶ thickObj R I e G := Over.homMk h hh
  have hfO : (Over.map (thick R I e)).map hO ≫ fstG I e G =
      fstG I e G ≫ ((toUnit G ≫ a₀) * 𝟙 G) := Over.OverMorphism.ext hf
  have hsh : ∀ x : Z' ⟶ thickObj R I e G, (Over.map (thick R I e)).map (x ≫ hO) ≫ fstG I e G =
      (toUnit _ ≫ a₀) * ((Over.map (thick R I e)).map x ≫ fstG I e G) := fun x => by
    rw [Functor.map_comp, Category.assoc, hfO, ← Category.assoc, MonObj.comp_mul, comp_toUnit_assoc,
      Category.comp_id]
  have hkey : b ≫ hO = (τ ≫ g.i) * (b' ≫ hO) := by
    apply FormalPoint.eq_of_map_fstG
    rw [hsh, FormalPoint.map_mul_fstG, hsh, hτ, FormalPoint.map_mul_fstG, mul_left_comm]
  have v₁ := val_torus_mul g χ (Z := Z') hJ τ _ (b ≫ hO) (b' ≫ hO) rfl hkey
  have v₂ := val_torus_mul g χ (Z := Z') hJ τ _ b b' rfl hτ
  let k : Z ⟶ (thickObj R I e G).left := (τ ≫ g.i).left
  have v₁' : val (g.t χ) (r ≫ h) z J = val (g.t χ) k z J * val (g.t χ) (r' ≫ h) z J := v₁
  have v₂' : val (g.t χ) r z J = val (g.t χ) k z J * val (g.t χ) r' z J := v₂
  have hB : val (g₂.t χ₂) r z J' = val (g.t χ) k z J * val (g₂.t χ₂) r' z J' := by
    rw [v₂'] at h₂
    rw [mul_inv_eq_iff_eq_mul.1 h₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hP : (∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z
        (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i))
        (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) =
      ∏ k, gv w (r' ≫ D₂.Oφ g₂.pG χ₂ k) z
        (fun i => J ((r' ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i))
        (J' (r' ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k :=
    Finset.prod_congr rfl fun k _ => by rw [hprod k]
  have hS : val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J =
      val (gp.s χ) (r' ≫ (thickObj R I e G).hom ≫ thick R I e) z J := by
    rw [reassoc_of% hw]
  rw [hP, hS, v₁', hB]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TwCoordInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem texp_of_isSum {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G} {n j : ℤ} (τ : SecE U b n j)
    {Ix : Type} {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β)
    (hs : Small I s) (hF : IsSum I s F) (hτ : TExp U τ s) : TExp U τ (w := id) F := by
  classical
  intro S hS Z x z J J' hJ hJ'
  have h0 : ∀ i ∉ (hs e).toFinset, Van I (s i) e := fun i hi => by
    by_contra h
    exact hi ((hs e).mem_toFinset.2 h)
  have hx : x ≫ (U.gt e).pG.left =
      (x ≫ (U.gt e).q.left) ≫ pullback.fst D.toPre.P.A.hom (thick R I e) := (Category.assoc _ _ _).symm
  rw [hτ _ h0 Z x z J J' hJ hJ']
  have hsum : ∀ δ, sval (F δ) (x ≫ (U.gt e).pG.left) z J =
      ∑ i ∈ (hs e).toFinset.filter (fun i => w i = δ), sval (s i) (x ≫ (U.gt e).pG.left) z J := fun δ => by
    rw [hx]
    convert hF e _ h0 δ Z (x ≫ (U.gt e).q.left) z J hJ
  have hvan : ∀ δ ∉ S, sval (F δ) (x ≫ (U.gt e).pG.left) z J = 0 := fun δ hδ => by
    rw [hx]
    exact hS δ hδ Z (x ≫ (U.gt e).q.left) z J hJ
  have key : ∀ T : Finset D.toPre.X, (hs e).toFinset.image w ⊆ T →
      ∑ i ∈ (hs e).toFinset, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val =
      ∑ δ ∈ T, sval (F δ) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t δ) x z J).val := fun T hT => by
    rw [← Finset.sum_fiberwise_of_maps_to (g := w) (t := T) (fun i hi => hT (Finset.mem_image_of_mem w hi))]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain rfl := (Finset.mem_filter.1 hi).2
    rfl
  rw [key _ (Finset.subset_union_left (s₂ := S))]
  refine (Finset.sum_subset Finset.subset_union_right fun δ _ hδ => ?_).symm
  exact (congrArg (· * _) (hvan δ hδ)).trans (zero_mul _)

theorem texp_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j : ℤ) (τ : SecE U.toUnifPre b n j) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → TExp U.toUnifPre τ s → TExp U.toUnifPre τ (w := id) F :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U _ _ _ _ τ _ _ s F hs hF hτ => texp_of_isSum U.toUnifPre τ s F hs hF hτ

end GlobalTheory.TwFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionMulOfMemberProducts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem texp_mul_of_prod : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β) (p : ∀ q : D.toPre.X × D.toPre.X, SecT D.toPre a n'' j'' (q.1 + q.2)) (τ : SecE U.toUnifPre b n j) (τ' : SecE U.toUnifPre b n' j') (τ'' : SecE U.toUnifPre b n'' j''), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → (∀ q : D.toPre.X × D.toPre.X, IsProdT (f q.1) (g q.2) (p q)) → TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') → TExp U.toUnifPre τ'' (w := fun q : D.toPre.X × D.toPre.X => q.1 + q.2) p := by
  intro R _ _ _ _ D a A G _ _ _ U e b n j n' j' n'' j'' hn hj f g p τ τ' τ'' hf hg hp hτ hτ' hτ''
  classical
  subst hn hj
  intro S hS Z x z J J' hJ hJ'
  have hy : x ≫ (U.gt e).pG.left = (x ≫ (U.gt e).q.left) ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) := by
    simp [GtCoord.pG, DegPre.prBe, Over.comp_left, Over.map_map_left, Over.homMk_left]
  have vanAt : ∀ {n j : ℤ} {β : D.toPre.X} (s : SecT D.toPre a n j β), Van (maximalIdeal R) s e →
      sval s (x ≫ (U.gt e).pG.left) z J = 0 := fun s hs => by rw [hy]; exact hs Z _ z J hJ
  have h1 : evalE U.toUnifPre τ'' x z J J' = evalE U.toUnifPre τ x z J J' * evalE U.toUnifPre τ' x z J J' := by
    simp only [evalE, zpow_add, Units.val_mul]; rw [hτ'' Z x z J' hJ']; ring
  have hL : ∀ χ χ' : D.toPre.X, x ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (U.gt e).pG)).left =
      (x ≫ (U.gt e).pG.left) ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (𝟙 D.toPre.P.A)) :
        D.toPre.P.A ⟶ G3 D.toPre.P.A).left := by
    intro χ χ'
    rw [Category.assoc, ← Over.comp_left]
    congr 2
    simp [comp_lift]
  have hT : ∀ χ χ' : D.toPre.X, (val ((U.gt e).t (χ + χ')) x z J).val *
      (val D.toPre.cub.t ((x ≫ (U.gt e).pG.left) ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (𝟙 D.toPre.P.A)) :
        D.toPre.P.A ⟶ G3 D.toPre.P.A).left) z J).val =
      (val ((U.gt e).t χ) x z J).val * (val ((U.gt e).t χ') x z J).val := by
    intro χ χ'
    have h := (val_mul hJ _ _ x).symm.trans ((val_corr hJ ((U.gt e).t_mul χ χ') x).trans (val_mul hJ _ _ x))
    have h' := (congrArg (val ((U.gt e).t (χ + χ')) x z J * ·) (val_pull hJ _ _ x)).symm.trans h
    rw [← hL χ χ']
    exact (Units.val_mul _ _).symm.trans ((congrArg Units.val h').trans (Units.val_mul _ _))
  have hSf : ∀ i ∉ (hf e).toFinset, Van (maximalIdeal R) (f i) e := fun i hi =>
    by_contra fun hc => hi ((hf e).mem_toFinset.2 hc)
  have hSg : ∀ i ∉ (hg e).toFinset, Van (maximalIdeal R) (g i) e := fun i hi =>
    by_contra fun hc => hi ((hg e).mem_toFinset.2 hc)
  have ef : evalE U.toUnifPre τ x z J J' = ∑ i ∈ (hf e).toFinset,
      sval (f i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t i) x z J).val := hτ _ hSf Z x z J J' hJ hJ'
  have eg : evalE U.toUnifPre τ' x z J J' = ∑ i ∈ (hg e).toFinset,
      sval (g i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t i) x z J).val := hτ' _ hSg Z x z J J' hJ hJ'
  have hP := fun q => hp q Z (x ≫ (U.gt e).pG.left) z J hJ
  have z₁ : ∀ q ∉ S, sval (p q) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (q.1 + q.2)) x z J).val = 0 :=
    fun q hq => by rw [vanAt _ (hS q hq), zero_mul]
  have z₂ : ∀ q ∉ (hf e).toFinset ×ˢ (hg e).toFinset,
      sval (p q) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (q.1 + q.2)) x z J).val = 0 := by
    intro q hq
    rw [Finset.mem_product, not_and_or] at hq
    rw [hP q]
    rcases hq with h | h
    · rw [vanAt _ (hSf _ h), zero_mul, zero_mul, zero_mul]
    · rw [vanAt _ (hSg _ h), mul_zero, zero_mul, zero_mul]
  show _ = ∑ q ∈ S, sval (p q) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (q.1 + q.2)) x z J).val
  rw [h1, ef, eg, Finset.sum_mul_sum, ← Finset.sum_product',
    Finset.sum_subset (Finset.subset_union_right (s₁ := (hf e).toFinset ×ˢ (hg e).toFinset)) (fun q _ hq => z₁ q hq),
    ← Finset.sum_subset (Finset.subset_union_left (s₂ := S)) (fun q _ hq => z₂ q hq)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hP q]
  linear_combination (-(sval (f q.1) (x ≫ (U.gt e).pG.left) z J * sval (g q.2) (x ≫ (U.gt e).pG.left) z J)) * hT q.1 q.2

end GlobalTheory.TwFam
end

