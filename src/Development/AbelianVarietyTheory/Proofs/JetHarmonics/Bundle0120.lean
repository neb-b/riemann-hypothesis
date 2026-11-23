module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDerivedActionFiniteDimUnitaryRep
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0053
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0114
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0043
public import Development.AutomorphicArithmetic.OrbitLabellings.FnumEqRhoMulSumOfDemandRatioLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalBiextensionIntegralChartValuedExtensStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalBiextension_integral_chart_valuedExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p), ∃ B : FB X.O (chD Ch.ch) (𝓞 E), B.G.F = (fun i => MvPowerSeries.map X.ι (Ch.FT i)) ∧ (∀ a, B.A.act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)) ∧ B.IsCanonGauge X.C (letI := io.toAlgebra; MvPowerSeries.map X.ιF Ch.ch.h) := by
  first | exact @GlobalTheory.CharDepth.exists_formalBiext_valExt | exact GlobalTheory.CharDepth.exists_formalBiext_valExt | (intros; apply GlobalTheory.CharDepth.exists_formalBiext_valExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHighestWeightIrreducibleUnitaryRepU
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.UnitaryHighestWeight

section OneParam

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem deriv_right (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (v : W) (t : ℝ) :
    HasDerivAt (fun s => U s v) (U t (A v)) t := by
  have h1 : HasDerivAt (fun s => U (s - t) v) (A v) t := by
    have h := hd v
    rw [← sub_self t] at h
    exact HasDerivAt.comp_sub_const t t h
  have h2 := ((U t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  have h3 : HasDerivAt (fun s => U t (U (s - t) v)) (U t (A v)) t := h2
  convert h3 using 1
  funext s
  simp [← hadd]

theorem deriv_left (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (v : W) (t : ℝ) :
    HasDerivAt (fun s => U s v) (A (U t v)) t := by
  have h1 : HasDerivAt (fun s => U (s - t) (U t v)) (A (U t v)) t := by
    have h := hd (U t v)
    rw [← sub_self t] at h
    exact HasDerivAt.comp_sub_const t t h
  convert h1 using 1
  funext s
  simp [← hadd]

theorem eigen (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (h0 : ∀ v, U 0 v = v)
    (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (v : W) (c : ℂ) (hv : A v = c • v) :
    U 1 v = Complex.exp c • v := by
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) • U t v) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    have h2 := h1.fun_smul (deriv_right U A hadd hd v t)
    convert h2 using 1
    rw [hv, map_smul, smul_smul, ← add_smul]
    simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    one_smul, h0] at hc
  conv_rhs => rw [← hc, smul_smul, ← Complex.exp_add]
  simp

theorem stable [FiniteDimensional ℂ W] (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (h0 : ∀ v, U 0 v = v)
    (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (S : Submodule ℂ W) (hS : ∀ v ∈ S, A v ∈ S)
    (v : W) (hv : v ∈ S) (t : ℝ) : U t v ∈ S := by
  set Q : W →L[ℂ] W := ContinuousLinearMap.id ℂ W - S.starProjection with hQ
  have hQ0 : ∀ y ∈ S, Q y = 0 := fun y hy => by
    simp [hQ, (Submodule.starProjection_eq_self_iff (K := S)).2 hy]
  set B : W →L[ℂ] W := Q.comp (LinearMap.toContinuousLinearMap A) with hB
  have hq : ∀ t, HasDerivAt (fun s => Q (U s v)) (B (Q (U t v))) t := by
    intro t
    have h2 : HasDerivAt (fun s => Q (U s v)) (Q (A (U t v))) t :=
      (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (deriv_left U A hadd hd v t)
    convert h2 using 1
    have h3 : Q (A (S.starProjection (U t v))) = 0 :=
      hQ0 _ (hS _ (Submodule.starProjection_apply_mem S _))
    have h4 : Q (U t v) = U t v - S.starProjection (U t v) := by simp [hQ]
    simp only [hB, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
    rw [h4, map_sub, map_sub, h3, sub_zero]
  have hz : (fun s => Q (U s v)) = fun _ => (0 : W) := by
    refine ODE_solution_unique_univ (v := fun _ y => B y) (s := fun _ => Set.univ) (K := ‖B‖₊) (t₀ := 0)
      (fun _ => B.lipschitz.lipschitzOnWith) (fun t => ⟨hq t, trivial⟩)
      (fun t => ⟨by simpa using hasDerivAt_const t (0 : W), trivial⟩) ?_
    simp only [h0]
    exact hQ0 v hv
  have h5 : U t v - S.starProjection (U t v) = 0 := by simpa [hQ] using congrFun hz t
  rw [sub_eq_zero.1 h5]
  exact Submodule.starProjection_apply_mem S _

end OneParam

open PI.UpqRep

theorem Jm_allPos (k : ℕ) : Jm (allPos k) = 1 := by
  simp [Jm, allPos]

theorem mem_K_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) :
    g ∈ Kset (allPos k) ↔ g ∈ UJset (allPos k) := by
  show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Jm (allPos k) = Jm (allPos k) * g) ↔
    gᴴ * Jm (allPos k) * g = Jm (allPos k)
  rw [Jm_allPos, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']
  simp [Matrix.star_eq_conjTranspose]

theorem exp_mem {k : ℕ} {Z : Matrix (Fin k) (Fin k) ℂ} (hZ : Zᴴ = -Z) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Z) ∈ UJset (allPos k) := by
  refine Formalism.REAL.exp_indefinite_unitary_holds k (allPos k) Z ?_ t
  show Zᴴ * Jm (allPos k) + Jm (allPos k) * Z = 0
  rw [Jm_allPos, hZ]
  simp

variable {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)}

theorem group_zero (hπ : IsURepOn (UJset (allPos k)) π) (Z : Matrix (Fin k) (Fin k) ℂ) (v : W) :
    π (NormedSpace.exp (((0 : ℝ) : ℂ) • Z)) v = v := by
  simp [hπ.1.1]

theorem group_add (hπ : IsURepOn (UJset (allPos k)) π) {Z : Matrix (Fin k) (Fin k) ℂ} (hZ : Zᴴ = -Z)
    (s t : ℝ) (v : W) :
    π (NormedSpace.exp (((s + t : ℝ) : ℂ) • Z)) v =
      π (NormedSpace.exp ((s : ℂ) • Z)) (π (NormedSpace.exp ((t : ℂ) • Z)) v) := by
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute _ _
    (((Commute.refl Z).smul_left _).smul_right _), hπ.1.2 _ (exp_mem hZ s) _ (exp_mem hZ t)]
  rfl

theorem diag_skew (θ : Fin k → ℝ) :
    (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)ᴴ = -Matrix.diagonal fun a => (θ a : ℂ) * Complex.I := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
  congr 1
  funext i
  simp

theorem exp_diag (θ : Fin k → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) =
      Matrix.diagonal fun a => Complex.exp (((t * θ a : ℝ) : ℂ) * Complex.I) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext a
  rw [← Complex.exp_eq_exp_ℂ]
  simp [mul_assoc]

theorem sum_diag (E : Fin k → Fin k → Module.End ℂ W) (d : Fin k → ℂ) (v : W) :
    ∑ a, ∑ b, Matrix.diagonal d a b • E a b v = ∑ a, d a • E a a v := by
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.diagonal_apply, ite_smul]

theorem isWtOn_of_isWeight (hπ : IsURepOn (UJset (allPos k)) π) (E : Fin k → Fin k → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (μ : Fin k → ℝ) (v : W) (hv : Formalism.REAL.IsWeight E μ v) : IsWtOn (Kset (allPos k)) π μ v := by
  intro θ _
  have h := eigen (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)))
    (∑ a, ((θ a : ℂ) * Complex.I) • E a a) (group_zero hπ _) (group_add hπ (diag_skew θ))
    (fun w => by
      have := hE _ (diag_skew θ) w
      rw [sum_diag] at this
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using this)
    v (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) (by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hv _, smul_smul, ← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring)
  simp only [exp_diag, one_mul] at h
  exact h

theorem isWeight_of_isWtOn (E : Fin k → Fin k → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (μ : Fin k → ℝ) (v : W) (hv : IsWtOn (Kset (allPos k)) π μ v) : Formalism.REAL.IsWeight E μ v := by
  intro a
  set θ : Fin k → ℝ := Pi.single a 1 with hθ
  have h1 := hE _ (diag_skew θ) v
  rw [sum_diag] at h1
  have h2 : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)) v) =
      fun t : ℝ => Complex.exp ((μ a * Complex.I) * t) • v := by
    funext t
    have hm := exp_mem (diag_skew θ) t
    rw [exp_diag] at hm ⊢
    rw [hv (fun b => t * θ b) ((mem_K_iff _).2 hm)]
    congr 2
    simp [hθ, Pi.single_apply]
    ring
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((μ a * Complex.I) * t) • v) ((μ a * Complex.I) • v) 0 := by
    have h4 : HasDerivAt (fun t : ℝ => (μ a * Complex.I) * (t : ℂ)) (μ a * Complex.I) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (μ a * Complex.I)
    simpa using h4.cexp.smul_const v
  rw [h2] at h1
  have h5 := h1.unique h3
  have h6 : ∑ b, ((θ b : ℂ) * Complex.I) • E b b v = Complex.I • E a a v := by
    rw [Finset.sum_eq_single a]
    · simp [hθ]
    · intro b _ hb
      simp [hθ, Pi.single_eq_of_ne hb]
    · simp
  rw [h6, mul_comm, ← smul_smul] at h5
  exact smul_right_injective W Complex.I_ne_zero h5

theorem stable_of_derived [FiniteDimensional ℂ W] (hπ : IsURepOn (UJset (allPos k)) π)
    (E : Fin k → Fin k → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (S : Submodule ℂ W) (hS : Formalism.REAL.KStable (allPos k) E S) :
    ∀ g ∈ UJset (allPos k), ∀ v ∈ S, π g v ∈ S := by
  intro g hg v hv
  obtain ⟨Y, hY, hg', -⟩ := Formalism.REAL.compact_exponential_surjective k (allPos k) g ((mem_K_iff g).2 hg)
  have hZ : Yᴴ = -Y := by
    have h : Yᴴ * Jm (allPos k) + Jm (allPos k) * Y = 0 := hY.1
    rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul] at h
    exact eq_neg_of_add_eq_zero_left h
  have h := stable (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E a b)
    (group_zero hπ _) (group_add hπ hZ)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using hE _ hZ w) S
    (fun w hw => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hS a b rfl w hw)) v hv 1
  simpa [hg'] using h

theorem exists_isHCTypeU : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π → (∀ S : Submodule ℂ W, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∃ u, PI.UpqRep.IsHCTypeU k u π := by
  intro k W _ _ _ _ π hπ hirr
  obtain ⟨E, hgl, hun, hE⟩ := _root_.GlobalTheory.UnitaryDerived.exists_derived_action k W π hπ
  obtain ⟨x, -, hx, Λ, hΛ⟩ := Formalism.REAL.highestWeightExists_holds W k (allPos k) E ⊤ inferInstance
    (Formalism.REAL.glRel_kRel _ E hgl) (Formalism.REAL.isUnitary_kUnit _ E hun) (fun _ _ _ _ _ => trivial) top_ne_bot
  have hxm : x ∈ Formalism.REAL.kSpan (allPos k) E x := Submodule.mem_sInf.2 fun S hS => hS.1
  have hst : Formalism.REAL.KStable (allPos k) E (Formalism.REAL.kSpan (allPos k) E x) := fun a b hab y hy =>
    Submodule.mem_sInf.2 fun S hS => hS.2 a b hab y (Submodule.mem_sInf.1 hy S hS)
  have htop : Formalism.REAL.kSpan (allPos k) E x = ⊤ := by
    rcases hirr _ (stable_of_derived hπ E hE _ hst) with h | h
    · rw [h] at hxm
      exact absurd hxm hx
    · exact h
  refine ⟨Λ - rhoN (allPos k) + rhoC (allPos k), inferInstance, inferInstance, hπ, ?_⟩
  have hl : lowK (allPos k) (Λ - rhoN (allPos k) + rhoC (allPos k)) = Λ := by
    unfold lowK
    abel
  rw [hl]
  refine ⟨inferInstance, fun _ _ _ _ => trivial, fun S _ hS => hirr S fun g hg => hS g ((mem_K_iff g).2 hg),
    ⟨x, trivial, hx, isWtOn_of_isWeight hπ E hE Λ x hΛ.1⟩, fun μ v _ hv hw => ?_⟩
  exact _root_.GlobalTheory.weight_cdom_of_mem_kSpan k W E Λ μ x v hgl hun hΛ (htop ▸ trivial) hv (isWeight_of_isWtOn E hE μ v hw)

end GlobalTheory.UnitaryHighestWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentRecursionStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_exists_unit_product_moment_le_Hsq_pow : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (l ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a, lenA k r z (Matrix.of x) a ^ 2) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1)) := by
  first | exact @GlobalTheory.MomProd.product_moment | exact GlobalTheory.MomProd.product_moment | (intros; apply GlobalTheory.MomProd.product_moment <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ForcedContentBoundsProgrammeValueGoodPrime
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ContentValue

lemma lpF_nonneg (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) (hl : 2 ≤ l) (hD : ∀ a, 0 ≤ D a) : 0 ≤ lpF l d D := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hS : 0 ≤ ∑ a, D a := Finset.sum_nonneg fun a _ => hD a
  have hq : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hg : 0 ≤ (l : ℝ) / ((l : ℝ) ^ 2 - 1) * ∑ a, D a := by positivity
  unfold lpF
  rw [sub_nonneg]
  refine Real.sSup_le ?_ hg
  rintro t ⟨x, h0, h1, h2, rfl⟩
  have := (GlobalTheory.FlowProgramme.duality l d D hl x ⟨h0, fun a i h => ?_, h2⟩).1
  · have ht : 0 ≤ ∑ s, ∑ i ∈ Finset.range d, x s i :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => h0 s i
    rw [div_mul_eq_mul_div, le_div_iff₀ hq]
    nlinarith [mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ l - 1 by linarith)]
  · by_contra hc
    refine h (h1 a i ?_)
    by_cases ho : Odd i
    · exact Or.inr (not_lt.1 fun hh => hc ⟨ho, hh⟩)
    · exact Or.inl ho

lemma two_le_ordP (N : NumDatum) (l : ℕ) (hc : Inert N l) (hn : ¬ PhiC N l) : 2 ≤ N.ordP l := by
  unfold NumDatum.ordP
  split
  · have := addOrderOf_pos (2 • N.hP l)
    omega
  · rename_i hs
    have h0 : N.hP l ≠ 0 := fun h => hn ⟨Or.resolve_right hc hs, h⟩
    have h1 : addOrderOf (N.hP l) ≠ 1 := fun h => h0 (AddMonoid.addOrderOf_eq_one_iff.1 h)
    have := addOrderOf_pos (N.hP l)
    omega

lemma rho_bound (k w l : ℝ) (hk : 1 ≤ k) (hw : 0 ≤ w) (hl : 2 ≤ l) :
    (k - 1) * w / (l ^ 2 - 1) ≤ 2 * (k * w / l ^ 2) := by
  have h4 : 4 ≤ l ^ 2 := by nlinarith
  rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 : 0 ≤ k * w := by positivity
  nlinarith [mul_nonneg h1 (show 0 ≤ l ^ 2 - 2 by linarith), mul_nonneg hw (show 0 ≤ l ^ 2 by linarith)]

theorem main : ∀ (N : NumDatum) (j l : ℕ), l.Prime → l ∉ N.H.small → l ≠ N.q → l ≠ N.d → l ≠ N.g 0 → l ≠ N.g 1 → (∀ z, 0 ≤ N.w j z) → (∀ z z', N.w j z' ≤ N.sc.X'' N.R.n * N.w j z) →
  0 ≤ N.FjP j l ∧ (Inert N l ∨ N.cls l = PrimeClass.splitK) ∧ ParOK (parOf N j l) ∧
  (PhiC N l → ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) ≤ N.FjP j l + if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) ∧
  (Inert N l → ¬ PhiC N l → ∀ Z : Finset (RPl N.R), RF.IsReps (parOf N j l) Z →
    (∑ z ∈ Z, Fnum l (N.ordP l) fun s => ((N.R.k : ℝ) - 1) * N.w j (N.pos l z s.val)) ≤ N.FjP j l + if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) := by
  classical
  intro N j l hp h2 hq hd hg0 hg1 hw hr
  have hl : 2 ≤ l := hp.two_le
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hk : (1 : ℝ) ≤ N.R.k := by
    have := N.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ N.R.k)
  have hq2 : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hS : 0 ≤ ∑ z, N.w j z := Finset.sum_nonneg fun z _ => hw z
  have hcls : Inert N l ∨ N.cls l = PrimeClass.splitK := by
    unfold Inert NumDatum.cls primeClass
    rw [if_neg h2, if_neg hq, if_neg hd]
    split_ifs <;> simp
  have hnd : N.cls l ≠ PrimeClass.ramD := by
    rcases hcls with (h | h) | h <;> rw [h] <;> simp
  have hF : N.FjP j l = if Inert N l ∧ (l : ℝ) ≤ N.sc.X'' N.R.n then N.FInert j l else 0 := by
    unfold NumDatum.FjP
    rw [if_neg (by tauto), if_neg hnd]
    by_cases h : Inert N l ∧ (l : ℝ) ≤ N.sc.X'' N.R.n
    · rw [if_pos h]; exact if_pos h
    · rw [if_neg h]; exact if_neg h
  have hD : ∀ z, 0 ≤ ((N.R.k : ℝ) - 1) * N.w j z := fun z => mul_nonneg (by linarith) (hw z)
  have hI : 0 ≤ N.FInert j l := by
    unfold NumDatum.FInert
    split_ifs
    · exact Finset.sum_nonneg fun z _ => div_nonneg (hD z) hq2.le
    · exact div_nonneg (Finset.sum_nonneg fun z _ => lpF_nonneg _ _ _ hl fun a => hD _) (Nat.cast_nonneg _)
  have hb := rho_bound N.R.k _ l hk hS hl'
  refine ⟨?_, hcls, ?_, ?_, ?_⟩
  · rw [hF]
    split_ifs
    · exact hI
    · exact le_rfl
  · have h3 := N.R.m_add_three_le_k
    have h4 := N.R.two_le_m
    refine ⟨?_, ?_, h3, ?_, ?_⟩
    · show Fintype.card (RPl N.R) = N.R.f
      have := Formalism.HC.Frame.card_A N.R.toFrame
      simpa [Ranks.f, Ranks.n] using this
    · show 1 ≤ N.R.m
      omega
    · show N.R.r = N.R.k - 1 + N.R.m
      unfold Ranks.r
      omega
    · show 0 ≤ N.Sc + N.eta
      unfold NumDatum.Sc NumDatum.eta
      positivity
  · intro hc
    have hi : Inert N l := Or.inl hc.1
    by_cases hX : (l : ℝ) ≤ N.sc.X'' N.R.n
    · rw [hF, if_pos ⟨hi, hX⟩, if_neg (not_lt.2 hX), add_zero]
      unfold NumDatum.FInert
      rw [if_pos (show N.cls l = PrimeClass.inertClass ∧ N.hP l = 0 from hc), ← Finset.sum_div, ← Finset.mul_sum]
    · rw [hF, if_neg (fun h => hX h.2), if_pos (not_le.1 hX), zero_add]
      exact hb
  · intro hi hc Z hZ
    have hZ' : Formalism.L2.FormalSeriesBounds.IsReps N l Z := hZ
    by_cases hX : (l : ℝ) ≤ N.sc.X'' N.R.n
    · rw [hF, if_pos ⟨hi, hX⟩, if_neg (not_lt.2 hX), add_zero]
      exact (GlobalTheory.LevelsOrbits.fInertReps N j l Z hZ' hi hc).1.ge
    · rw [hF, if_neg (fun h => hX h.2), if_pos (not_le.1 hX), zero_add]
      refine le_trans (le_of_eq ?_) hb
      have ho2 := two_le_ordP N l hi hc
      have hl3 : 3 ≤ l := by
        have := ne_two_of_not_small h2
        omega
      have hbal : ∀ z z', N.w j z' ≤ l * N.w j z := fun z z' =>
        (hr z z').trans (mul_le_mul_of_nonneg_right (not_le.1 hX).le (hw z))
      rw [GlobalTheory.LevelsOrbits.sum_reps N l Z hZ' (N.w j), Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [UpperTheory.fnum_eq_rho_mul_sum_of_demand_ratio_le l (N.ordP l) hl3 ho2 _ (fun a => hD _) (fun a a' => ?_), ← Finset.mul_sum]
      · unfold Formalism.IncomingBounds.rho
        ring
      · have := mul_le_mul_of_nonneg_left (hbal (N.pos l z a.val) (N.pos l z a'.val))
          (show (0 : ℝ) ≤ N.R.k - 1 by linarith)
        linarith

end GlobalTheory.ContentValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasTrivialKernelIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KerPow
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistCompare

section Basis

variable {A : Type} [CommRing A] {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

end Basis

section Hyp

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

end Hyp

section Conclusion

variable {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R)

end Conclusion

theorem cube : Out.CubeSt :=
  GlobalTheory.AbLaw.Cube.cube_of_gen GlobalTheory.laws_without_cohomology.1 (GlobalTheory.AbLaw.exists_gen_theta
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    GlobalTheory.laws_without_cohomology.1 GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy
    (GlobalTheory.AbLaw.polAV_veryAmpleBy GlobalTheory.laws_without_cohomology.2.2.1)
    GlobalTheory.AbLaw.isProjBy_tensor GlobalTheory.TrivLocus.isClosed_trivLocus
    (GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre GlobalTheory.laws_without_cohomology.1 GlobalTheory.AbLaw.Seesaw.seesaw
      (GlobalTheory.SmallExtLift.exists_gen_of_small_extension GlobalTheory.laws_without_cohomology.1
        GlobalTheory.KuennethOne.kuenneth_injective)))

theorem exists_degPre {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))) (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A) :
    ∃ (D : Out.DegPre R) (α : D.X) (e : D.P = P), e ▸ D.c α = c := by
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (cube _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := SelfUnif.exists_sym P
  choose psi hpsi using fun n : ℤ => DVR.exists_gen_of_local (V := FractionRing R) P.L P.isLB (K := PUnit)
    (fun _ => Out.ptK (c ^ n)) (fun _ => -1)
  exact ⟨{ P := P, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := ℤ
           c := fun n => c ^ n, c_add := fun a b => zpow_add c a b, psi := psi, psi_gen := hpsi },
    (1 : ℤ), rfl, zpow_one c⟩

end GlobalTheory.TwistCompare
end
end

