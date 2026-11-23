module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullbackDegree.EpsPullbackFst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1501
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralExtIsAlgClosedResidueField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerfectPairOfGeometricFibres
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairFibres

section Algebra

open Module TensorProduct GlobalTheory.PrincipalPolPairing

variable {R Ω : Type} [CommRing R] [CommRing Ω] [Algebra R Ω]
  {M N M' N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module Ω M'] [AddCommGroup N'] [Module Ω N']
  {f : M →ₛₗ[algebraMap R Ω] M'} {f' : N →ₛₗ[algebraMap R Ω] N'}

theorem subsingleton_coker₂ [Module.Finite R M] [Module.Projective R M] [Module.Finite R N]
    [Module.Projective R N] (hf : Function.Bijective (GlobalTheory.DeRham.liftSemi f))
    (hf' : Function.Bijective (GlobalTheory.DeRham.liftSemi f')) (θ : Dual R M →ₗ[R] N)
    (φ' : Dual Ω M' →ₗ[Ω] Dual Ω (Dual Ω N')) (hφ : Function.Surjective φ')
    (h : ∀ (x : Dual R M) (y : Dual R N) (x' : Dual Ω M') (y' : Dual Ω N'),
      (∀ c, x' (f c) = algebraMap R Ω (x c)) →
      (∀ c, y' (f' c) = algebraMap R Ω (y c)) → φ' x' y' = algebraMap R Ω (y (θ x))) :
    Subsingleton (Ω ⊗[R] (N ⧸ LinearMap.range θ)) := by
  let e := LinearEquiv.ofBijective _ hf'
  haveI : Module.Finite Ω N' := Module.Finite.equiv e
  haveI : Module.Projective Ω N' := Module.Projective.of_equiv e
  let π : N' →ₗ[Ω] Ω ⊗[R] (N ⧸ LinearMap.range θ) :=
    (LinearMap.range θ).mkQ.baseChange Ω ∘ₗ e.symm.toLinearMap
  have hπ : Function.Surjective π :=
    (LinearMap.baseChange_surjective Ω (Submodule.mkQ_surjective _)).comp e.symm.surjective
  let θ' : Dual Ω M' →ₗ[Ω] N' := (Module.evalEquiv Ω N').symm.toLinearMap ∘ₗ φ'
  have hθ' : Function.Surjective θ' := (Module.evalEquiv Ω N').symm.surjective.comp hφ
  have k : π ∘ₗ θ' = 0 := by
    refine ext_corr hf fun x x' hx ↦ ?_
    have e₁ : θ' x' = f' (θ x) := by
      apply (Module.evalEquiv Ω N').injective
      refine ((Module.evalEquiv Ω N').apply_symm_apply _).trans (ext_corr hf' fun y y' hy ↦ ?_)
      rw [h x y x' y' hx hy, ← hy]
      rfl
    have e₂ : f' (θ x) = e (1 ⊗ₜ θ x) := (one_smul Ω (f' _)).symm
    rw [LinearMap.comp_apply, e₁, e₂]
    simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, LinearMap.baseChange_tmul,
      LinearMap.zero_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self θ x), tmul_zero]
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := (hπ.comp hθ') a
  obtain ⟨b, rfl⟩ := (hπ.comp hθ') b
  exact (LinearMap.congr_fun k a).trans (LinearMap.congr_fun k b).symm

end Algebra

open Module

theorem isPerfPair_of_fibres₂ : ∀ (R : Type) [CommRing R] (M N : Type 1) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] (φ : Module.Dual R M →ₗ[R] Module.Dual R N →ₗ[R] R), (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω], ∃ (M' N' : Type 1) (_ : AddCommGroup M') (_ : Module Ω M') (_ : AddCommGroup N') (_ : Module Ω N') (f : M →ₛₗ[algebraMap R Ω] M') (f' : N →ₛₗ[algebraMap R Ω] N') (φ' : Module.Dual Ω M' →ₗ[Ω] Module.Dual Ω N' →ₗ[Ω] Ω), Function.Bijective (liftSemi f) ∧ Function.Bijective (liftSemi f') ∧ φ'.IsPerfPair ∧ ∀ (x : Module.Dual R M) (x' : Module.Dual Ω M') (y : Module.Dual R N) (y' : Module.Dual Ω N'), (∀ c, x' (f c) = algebraMap R Ω (x c)) → (∀ c, y' (f' c) = algebraMap R Ω (y c)) → φ' x' y' = algebraMap R Ω (φ x y)) → φ.IsPerfPair := by
  intro R _ M N _ _ _ _ _ _ _ _ φ h
  let E := Module.evalEquiv R M
  let E' := Module.evalEquiv R N
  have ev (z : Dual R (Dual R M)) (y : Dual R M) : y (E.symm z) = z y :=
    LinearMap.congr_fun (E.apply_symm_apply z) y
  have ev' (z : Dual R (Dual R N)) (y : Dual R N) : y (E'.symm z) = z y :=
    LinearMap.congr_fun (E'.apply_symm_apply z) y
  have s₁ : Function.Surjective (E'.symm.toLinearMap ∘ₗ φ) := by
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    refine GlobalTheory.PrincipalPolPairing.subsingleton_of_fibres (R := R) fun p ↦ ?_
    obtain ⟨M', N', _, _, _, _, f, f', φ', hf, hf', hp, k⟩ := h (AlgebraicClosure p.asIdeal.ResidueField)
    exact subsingleton_coker₂ hf hf' _ φ' hp.bijective_left.2 fun x y x' y' hx hy ↦ by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ev', k x x' y y' hx hy]
  have s₂ : Function.Surjective (E.symm.toLinearMap ∘ₗ φ.flip) := by
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    refine GlobalTheory.PrincipalPolPairing.subsingleton_of_fibres (R := R) fun p ↦ ?_
    obtain ⟨M', N', _, _, _, _, f, f', φ', hf, hf', hp, k⟩ := h (AlgebraicClosure p.asIdeal.ResidueField)
    exact subsingleton_coker₂ hf' hf _ φ'.flip hp.bijective_right.2 fun y x y' x' hy hx ↦ by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ev, LinearMap.flip_apply, LinearMap.flip_apply,
        k x x' y y' hx hy]
  refine LinearMap.IsPerfPair.of_bijective _ ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun z ↦ ?_⟩
  · refine LinearMap.ext fun c ↦ ?_
    obtain ⟨y, rfl⟩ := s₂ c
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ev, LinearMap.flip_apply, hx]
    rfl
  · obtain ⟨x, hx⟩ := s₁ (E'.symm z)
    exact ⟨x, E'.symm.injective hx⟩

end GlobalTheory.PairFibres
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRestrictOfPsiUnitOn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section
namespace GlobalTheory.UnifProperChar
section Inertia

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

end Inertia

section Reduction

open GlobalTheory.Published GlobalTheory.Published.AbVarRed

end Reduction

theorem exists_dvr_centre (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) [I.IsPrime] :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V),
      IsAlgClosed (ResidueField V) ∧ Function.Injective φ ∧ (maximalIdeal V).comap φ = I := by
  obtain ⟨V, _, _, _, φ, hφ, hc⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (φ : R →+* V), Function.Injective φ ∧ (maximalIdeal V).comap φ = I := by
    rcases eq_or_ne I ⊥ with rfl | hI
    · let K := FractionRing R
      let φ : R →+* PowerSeries K := (PowerSeries.C (R := K)).comp (algebraMap R K)
      have hφ : Function.Injective φ := PowerSeries.C_injective.comp (IsFractionRing.injective R K)
      refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance, φ, hφ, ?_⟩
      refine eq_bot_iff.2 fun r hr => ?_
      rw [Ideal.mem_comap, PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton,
        PowerSeries.X_dvd_iff] at hr
      have : algebraMap R K r = 0 := by simpa [φ] using hr
      exact (Ideal.mem_bot).2 (IsFractionRing.injective R K (this.trans (map_zero _).symm))
    · obtain ⟨V, _, _, hV, -, φ, h1, h2⟩ :=
        exists_complete_discreteValuationRing_of_prime_lt ⊥ I (bot_lt_iff_ne_bot.2 hI)
      exact ⟨V, inferInstance, inferInstance, hV, φ, (RingHom.injective_iff_ker_eq_bot φ).2 h1, h2⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨V', _, _, _, _, h1, h2, -, h3⟩ := GlobalTheory.ClosedResidueExt.exists_unramified_ext V hπ
  refine ⟨V', inferInstance, inferInstance, inferInstance, (algebraMap V V').comp φ, h3, h1.comp hφ, ?_⟩
  rw [← Ideal.comap_comap, ← hc]
  congr 1
  exact eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (algebraMap_isIntegral_iff.mpr h2) (maximalIdeal V'))

end GlobalTheory.UnifProperChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatioTwoMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatRatio.Square

variable {R : Type} [CommRing R] [IsDomain R]

theorem famφB_zero_one (Q : DegPre R) : Q.famφB 0 1 = 𝟙 _ := by
  show (padd Q.P.A (𝟙 Q.P.A) (toUnit _ ≫ Q.c 0)).left = 𝟙 _
  rw [GlobalTheory.Mum.degPre_c_zero, padd, comp_one, ← Hom.mul_def, _root_.mul_one]
  rfl

theorem famφB_zero_two (Q : DegPre R) : Q.famφB 0 2 = Q.famφB 0 3 := by
  show (toUnit Q.P.A ≫ Q.c 0).left = (toUnit Q.P.A ≫ η[Q.P.A]).left
  rw [GlobalTheory.Mum.degPre_c_zero, comp_one, Hom.one_def]

theorem formEq (Q : DegPre R) (N : ℕ) :
    FormEq (Sum.elim (Q.famφB 0) (Q.famφB 0)) (Sum.elim (DegPre.famε N) (DegPre.famε N))
      (Q.famφB 0) (DegPre.famε (2 * N)) := by
  intro U _ h
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four]
  have e1 := famφB_zero_one Q
  have e2 := famφB_zero_two Q
  have e0 : Q.famφB 0 0 = 𝟙 _ := rfl
  rw [e1, e2, e0]
  simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  generalize h (𝟙 _) = a
  generalize h (Q.famφB 0 3) = b
  push_cast
  have hs : ∀ k : ℤ, a ^ (k - 1) * a ^ (1 : ℤ) = a ^ k := fun k => by rw [← zpow_add, sub_add_cancel]
  rw [hs, hs, zpow_neg_one, zpow_one, inv_mul_cancel_right, inv_mul_cancel_right, ← zpow_add, two_mul]

theorem isRatio_two_mul (Q : DegPre R) (N : ℕ) (σ σ' : Q.SecB N 0) (U : Q.P.A.left.Opens)
    (f : Γ(Q.P.A.left, U)) (_hN : 1 ≤ N) (h : GlobalTheory.HeatRatio.IsRatio Q σ σ' U f) :
    ∃ ρ ρ' : Q.SecB (2 * N) 0, GlobalTheory.HeatRatio.IsRatio Q ρ ρ' U f := by
  obtain ⟨ρ, hρ⟩ := exists_sec Q.P.isLB (formEq Q N) (H1.SectionArithmetic.mulSec σ σ')
  obtain ⟨ρ', hρ'⟩ := exists_sec Q.P.isLB (formEq Q N) (H1.SectionArithmetic.mulSec σ' σ')
  refine ⟨ρ, ρ', fun z hz J hJ => ?_⟩
  obtain ⟨hu, he⟩ := h z hz J hJ
  rw [hρ _ _ z J hJ, hρ' _ _ z J hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, he]
  exact ⟨hu.mul hu, by ring⟩

end GlobalTheory.HeatRatio.Square

theorem GlobalTheory.HeatRatio.isRatio_square : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (N : ℕ) (σ σ' : Q.SecB N 0) (U : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, U)), 1 ≤ N → GlobalTheory.HeatRatio.IsRatio Q σ σ' U f → ∃ ρ ρ' : Q.SecB (2 * N) 0, GlobalTheory.HeatRatio.IsRatio Q ρ ρ' U f :=
  fun _ _ _ Q N σ σ' U f hN h => GlobalTheory.HeatRatio.Square.isRatio_two_mul Q N σ σ' U f hN h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudFourierTermSubSmul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HeatTermLin

theorem gs_sub_fn {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by simp only [gs_eq r z U h, map_sub]

theorem sval_sub_smul {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s t : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (s - c • t) r z J = sval s r z J - gs r z ⊤ c * sval t r z J := by
  have hm := hJ.mem φ r
  have h1 : sval (s - c • t) r z J = sval s r z J - sval (c • t) r z J :=
    gs_sub_fn r z _ hm _ _
  have h2 : sval (c • t) r z J = gs r z ⊤ c * sval t r z J :=
    (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm c))
  rw [h1, h2]

theorem gs_constFn {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (e : R) :
    gs r z ⊤ (constFn p ⊤ e) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom e) := by
  rw [← gs_pull r p z ⊤ trivial]
  exact gs_res r z (U := p ⁻¹ᵁ ⊤) (V := ⊤) le_top trivial _

theorem isTerm_sub_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ σ' : Q.SecB k α) (τ τ' : SecM Y.q.left Q.P.L k) (e : R), IsTerm Y k α σ τ → IsTerm Y k α σ' τ' → IsTerm Y k α (σ' - constFn Q.P.A.hom ⊤ e • σ) (τ' - constFn Y.H.hom ⊤ e • τ) := by
  intro R _ _ Q Ω _ _ _ oa Y k α σ σ' τ τ' e h h' T x y J hJ
  have a := sval_sub_smul (constFn Y.H.hom ⊤ e) τ' τ x.left y hJ
  have b := sval_sub_smul (constFn Q.P.A.hom ⊤ e) σ' σ (x ≫ Y.q).left y hJ
  rw [gs_constFn, Over.w] at a b
  refine a.trans ?_
  rw [h T x y J hJ, h' T x y J hJ]
  refine Eq.trans ?_ (congrArg (· * _) b).symm
  ring

end GlobalTheory.HeatTermLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtMul

open GlobalTheory.Heat.WtAlg

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem c_add {S : Type} [CommRing S] {φ : R →+* S} (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (hq : x' ≫ Y.q = x ≫ Y.q)
    (hc : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J)
    (χ χ' : Q.X) : c (χ + χ') = c χ * c χ' := by
  have hu : unitOn (c (χ + χ')) = unitOn (c χ) * unitOn (c χ') := unit_ext fun y _ => by
    obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB y (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e₁ := GlobalTheory.TorusModel.cv_add (Y.Φ _ x) hJ χ χ'
    have e₂ := GlobalTheory.TorusModel.cv_add (Y.Φ _ x') hJ χ χ'
    rw [Ray.Φ_b] at e₁ e₂
    rw [hq] at e₂
    dsimp only [GlobalTheory.TorusModel.cv] at e₁ e₂
    rw [hc _ y J hJ, hc _ y J hJ, hc _ y J hJ, _root_.mul_assoc, e₁, _root_.mul_mul_mul_comm] at e₂
    rw [map_mul]
    exact mul_right_cancel e₂
  have := congrArg (fun u : (Γ(Sp S, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom u.val) hu
  simp only [unitOn, Units.coe_map, Units.val_mul, map_mul] at this
  refine Units.ext ((Iso.inv_hom_id_apply _ _).symm.trans (this.trans ?_))
  exact congrArg₂ (· * ·) (Iso.inv_hom_id_apply _ _) (Iso.inv_hom_id_apply _ _)

theorem isWt_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Y.H.left.Opens) (χ χ' : Q.X) (f g : Γ(Y.H.left, V)), IsWt Y χ V f → IsWt Y χ' V g → IsWt Y (χ + χ') V (f * g) := by
  intro R _ _ Q O _ _ _ oa Y V χ χ' f g hf hg S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_mul'' _ _ hV', valR_mul'' _ _ hV, hg S φ x x' c a a' ha ha' hV hV' hq hc,
    hf S φ x x' c a a' ha ha' hV hV' hq hc, c_add x x' c hq hc, Units.val_mul]
  ring

end GlobalTheory.Heat.WtMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionSubConstMul
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatMod

theorem valR_sub_const_mul {R S : Type} [CommRing R] [CommRing S] {X : Scheme.{0}} (p : X ⟶ Sp R) (φ : R →+* S)
    (x : Sp S ⟶ X) (hx : x ≫ p = spMap φ) (W : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (f g : Γ(X, W)) (r : R) :
    valR x W (f - constFn p W r * g) = valR x W f - φ r * valR x W g := by
  have hc : valR x W (constFn p W r) = φ r := GlobalTheory.Points.valR_constFn_of_over p φ x hx W h r
  rw [← hc]
  unfold valR
  simp only [dif_pos h, map_sub, map_mul]

theorem isWt_sub_const_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (α : Q.X) (W : Y.H.left.Opens) (f g : Γ(Y.H.left, W)) (r : R), IsWt Y α W f → IsWt Y α W g → IsWt Y α W (f - constFn Y.H.hom W r * g) := by
  intro R _ _ Q Ω _ _ _ oa Y α W f g r hf hg S _ φ x x' c a a' ha ha' hW hW' hq hc
  have h1 := hf S φ x x' c a a' ha ha' hW hW' hq hc
  have h2 := hg S φ x x' c a a' ha ha' hW hW' hq hc
  have e : a ≫ Y.H.hom = spMap φ := by rw [ha]; exact Over.w x
  have e' : a' ≫ Y.H.hom = spMap φ := by rw [ha']; exact Over.w x'
  rw [valR_sub_const_mul _ φ a e W hW, valR_sub_const_mul _ φ a' e' W hW', h1, h2]
  ring

end GlobalTheory.HeatMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightPullbackPointTranslation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatTransWt

theorem valR_pbT_le {A : Type} [CommRing A] {X Z : Scheme.{0}} (w : Sp A ⟶ Z) (T : Z ⟶ X) {U : X.Opens}
    {U' : Z.Opens} (hU : U' ≤ T ⁻¹ᵁ U) (h : ⊤ ≤ w ⁻¹ᵁ U') (f : Γ(X, U)) :
    valR w U' (pbT T f U') = valR (w ≫ T) U f := by
  have h' : ⊤ ≤ (w ≫ T) ⁻¹ᵁ U := h.trans (w.preimage_mono hU)
  unfold valR
  rw [dite_eq_left h, dite_eq_left h', GlobalTheory.KS.pbT_of_le T hU]
  rw [← Scheme.Hom.appLE_comp_appLE w T U U' ⊤ hU h]
  rfl

theorem isWt_pbT_tr : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (α : Q.X) (U U' : Y.H.left.Opens), U' ≤ GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U → ∀ f : Γ(Y.H.left, U), IsWt Y α U f → IsWt Y α U' (pbT (GlobalTheory.HeatTrans.tr Y.H x) f U') := by
  intro R _ _ Q O _ _ _ oa Y x α U U' hU f hf S _ φ x₁ x₁' c a a' ha ha' hV hV' hq hc
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  let z : Over.mk (spMap φ) ⟶ Y.H := toUnit _ ≫ x
  have hleft : ∀ w : Over.mk (spMap φ) ⟶ Y.H, (w * z).left = w.left ≫ GlobalTheory.HeatTrans.tr Y.H x := fun w => by
    have e : w ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)) = w * z := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (w ≫ toUnit Y.H) (toUnit _)]
    rw [← e]; rfl
  rw [valR_pbT_le a' _ hU hV', valR_pbT_le a _ hU hV]
  subst ha ha'
  rw [← hleft, ← hleft]
  refine hf S φ (x₁ * z) (x₁' * z) c _ _ rfl rfl ?_ ?_ ?_ ?_
  · rw [hleft]; exact hV.trans (x₁.left.preimage_mono hU)
  · rw [hleft]; exact hV'.trans (x₁'.left.preimage_mono hU)
  · rw [MonObj.mul_comp, MonObj.mul_comp, hq]
  · intro χ y J hJ
    have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁ z)).2 χ y J hJ
    have h1' := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁' z)).2 χ y J hJ
    simp only [Y.Φ_b, GlobalTheory.TorusModel.cv] at h1 h1'
    rw [hq] at h1'
    refine mul_right_cancel (h1'.trans ?_)
    rw [hc χ y J hJ, _root_.mul_assoc, ← h1, _root_.mul_assoc]

end GlobalTheory.HeatTransWt
end
end

