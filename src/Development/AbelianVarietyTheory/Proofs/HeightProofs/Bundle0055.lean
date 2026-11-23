module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegralNormSqReproducingKernelLeFinrank
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

variable {n : ℕ}

theorem integral_star_mul_self {ε : Fin n → Bool} (f : KG ε → ℂ) :
    ∫ k, star (f k) * f k ∂(muK ε) = ((∫ k, ‖f k‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1; funext k
  rw [mul_comm, ← Complex.normSq_eq_norm_sq]
  exact Complex.mul_conj _

def l2InnerCore {ε : Fin n → Bool} (V : Submodule ℂ (KG ε → ℂ)) (hV : ∀ p ∈ V, Continuous p) :
    InnerProductSpace.Core ℂ V where
  inner p q := ∫ k, star (p.1 k) * q.1 k ∂(muK ε)
  conj_inner_symm p q := by
    rw [← integral_conj]
    congr 1; funext k
    simp [mul_comm]
  re_inner_nonneg p := by
    rw [integral_star_mul_self]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    exact integral_nonneg fun k => by positivity
  add_left p q r := by
    have hp := hV _ p.2
    have hq := hV _ q.2
    have hr := hV _ r.2
    rw [← integral_add (integrable_of_continuousK (f := fun k => star (p.1 k) * r.1 k) (by fun_prop))
      (integrable_of_continuousK (f := fun k => star (q.1 k) * r.1 k) (by fun_prop))]
    congr 1; funext k
    simp [add_mul]
  smul_left p q c := by
    rw [← integral_const_mul]
    congr 1; funext k
    simp [mul_assoc]
  definite p h := by
    have hp := hV _ p.2
    have h0 : ∫ k, ‖p.1 k‖ ^ 2 ∂(muK ε) = 0 := by
      have h' : ∫ k, star (p.1 k) * p.1 k ∂(muK ε) = 0 := h
      rw [integral_star_mul_self] at h'
      exact_mod_cast h'
    have hns : Continuous (fun k => ‖p.1 k‖ ^ 2) := by fun_prop
    have h2 : (fun k => ‖p.1 k‖ ^ 2) =ᵐ[muK ε] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg _)
        ((integrable_of_continuousK (Complex.continuous_ofReal.comp hns)).re)).1 h0
    have h3 : (fun k => ‖p.1 k‖ ^ 2) = 0 :=
      (Continuous.ae_eq_iff_eq (muK ε) hns continuous_const).1 h2
    ext k
    simpa using congrFun h3 k

theorem exists_parseval {ε : Fin n → Bool} (V : Submodule ℂ (KG ε → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ p ∈ V, Continuous p) :
    ∃ φ : Fin (Module.finrank ℂ V) → KG ε → ℂ, (∀ j, φ j ∈ V) ∧ (∀ j, ∫ k, ‖φ j k‖ ^ 2 ∂(muK ε) = 1) ∧
      ∀ r ∈ V, ∫ k, ‖r k‖ ^ 2 ∂(muK ε) = ∑ j, ‖∫ k, star (r k) * φ j k ∂(muK ε)‖ ^ 2 := by
  letI c := l2InnerCore V hV
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  have hin : ∀ p q : V, inner ℂ p q = ∫ k, star (p.1 k) * q.1 k ∂(muK ε) := fun _ _ => rfl
  have hn : ∀ p : V, ∫ k, ‖p.1 k‖ ^ 2 ∂(muK ε) = ‖p‖ ^ 2 := by
    intro p
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) p
    rw [hin, integral_star_mul_self] at h
    apply Complex.ofReal_injective
    rw [h, Complex.ofReal_pow]
    rfl
  let b := stdOrthonormalBasis ℂ V
  refine ⟨fun j => (b j).1, fun j => (b j).2, fun j => ?_, fun r hr => ?_⟩
  · rw [hn, b.orthonormal.1 j, one_pow]
  · rw [hn ⟨r, hr⟩, ← b.sum_sq_norm_inner_left]
    rfl

theorem mul_left_mem_low {ε : Fin n → Bool} (a : KG ε) {i : ℕ} {φ : KG ε → ℂ} (h : φ ∈ lowV ε i) :
    (fun k => φ (a * k)) ∈ lowV ε i := by
  cases i with
  | zero =>
    rw [lowV, Submodule.mem_bot] at h ⊢
    subst h
    rfl
  | succ j => exact mul_left_mem a h

def topV (ε : Fin n → Bool) (i : ℕ) : Submodule ℂ (KG ε → ℂ) where
  carrier := {p | p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨add_mem ha hb, fun q hq => ?_⟩
    have h1 := continuous_of_mem ha
    have h2 := continuous_of_mem hb
    have h3 := continuous_of_mem (lowV_le ε i hq)
    simp only [Pi.add_apply, mul_add]
    rw [integral_add (integrable_of_continuousK (f := fun k => star (q k) * a k) (by fun_prop))
      (integrable_of_continuousK (f := fun k => star (q k) * b k) (by fun_prop)), ha' q hq, hb' q hq, add_zero]
  zero_mem' := ⟨zero_mem _, fun q _ => by simp⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨Submodule.smul_mem _ c ha, fun q hq => ?_⟩
    have : (fun k => star (q k) * (c • a) k) = fun k => c * (star (q k) * a k) := by
      funext k; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this, integral_const_mul, ha' q hq, mul_zero]

theorem topV_le (ε : Fin n → Bool) (i : ℕ) : topV ε i ≤ polyV ε i := fun _ h => h.1

theorem mul_left_mem_top {ε : Fin n → Bool} (a : KG ε) {i : ℕ} {φ : KG ε → ℂ} (h : φ ∈ topV ε i) :
    (fun k => φ (a * k)) ∈ topV ε i := by
  refine ⟨mul_left_mem a h.1, fun q hq => ?_⟩
  have h1 := h.2 _ (mul_left_mem_low a⁻¹ hq)
  rw [← integral_mul_left_eq_self (μ := muK ε) _ a] at h1
  simpa only [inv_mul_cancel_left] using h1

theorem star_mem_top {ε : Fin n → Bool} {i : ℕ} {e : KG ε → ℂ} (he : IsKer ε i e) :
    (fun k => star (e k)) ∈ topV ε i := by
  refine ⟨star_mem he.1, fun q hq => ?_⟩
  calc ∫ k, star (q k) * star (e k) ∂(muK ε)
      = ∫ k, (starRingEnd ℂ) (e k * q k) ∂(muK ε) := by
        congr 1; funext k; rw [map_mul, mul_comm]; rfl
    _ = (starRingEnd ℂ) (∫ k, e k * q k ∂(muK ε)) := integral_conj
    _ = 0 := by rw [he.2.1 q hq, map_zero]

theorem integral_norm_sq_ker_le : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), IsKer ε i e →
    ∫ k, ‖e k‖ ^ 2 ∂(muK ε) ≤ (Module.finrank ℂ (polyV ε i) : ℝ) := by
  intro n ε i e he
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : FiniteDimensional ℂ (topV ε i) := Submodule.finiteDimensional_of_le (topV_le ε i)
  obtain ⟨φ, hφ, h1, hP⟩ := exists_parseval (topV ε i) (fun p hp => continuous_of_mem hp.1)
  have key : ∀ a : KG ε, ∫ k, ‖e k‖ ^ 2 ∂(muK ε) = ∑ j, ‖φ j a‖ ^ 2 := by
    intro a
    have h := hP _ (mul_left_mem_top a⁻¹ (star_mem_top he))
    simp only [star_star, norm_star] at h
    rw [integral_mul_left_eq_self (μ := muK ε) (fun k => ‖e k‖ ^ 2) a⁻¹] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 := mul_left_mem_top a (hφ j)
    have h3 := he.2.2 _ h2.1 h2.2
    rw [← integral_mul_left_eq_self (μ := muK ε) _ a]
    simp only [inv_mul_cancel_left, mul_one] at h3 ⊢
    rw [h3]
  have hint : ∀ j, Integrable (fun a => ‖φ j a‖ ^ 2) (muK ε) := by
    intro j
    have hp := continuous_of_mem (hφ j).1
    have hns : Continuous (fun k => ‖φ j k‖ ^ 2) := by fun_prop
    exact (integrable_of_continuousK (Complex.continuous_ofReal.comp hns)).re
  calc ∫ k, ‖e k‖ ^ 2 ∂(muK ε) = ∫ _a, (∫ k, ‖e k‖ ^ 2 ∂(muK ε)) ∂(muK ε) := by simp
    _ = ∫ a, ∑ j, ‖φ j a‖ ^ 2 ∂(muK ε) := by congr 1; funext a; exact key a
    _ = ∑ j, ∫ a, ‖φ j a‖ ^ 2 ∂(muK ε) := integral_finsetSum _ fun j _ => hint j
    _ = (Module.finrank ℂ (topV ε i) : ℝ) := by simp [h1]
    _ ≤ _ := by exact_mod_cast Submodule.finrank_mono (topV_le ε i)

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.L2normLeIntegralKernelMulTranslateDiff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

variable {n : ℕ}

theorem continuous_integral_paramK {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : KG ε → KG ε → E} (hF : Continuous (Function.uncurry F)) :
    Continuous (fun x => ∫ k, F x k ∂(muK ε)) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  have h := continuous_parametric_integral_of_continuous (μ := muK ε) hF (isCompact_univ (X := KG ε))
  simpa only [Measure.restrict_univ] using h

theorem integrable_prod_of_continuousK {ε : Fin n → Bool} {F : KG ε × KG ε → ℂ} (hF : Continuous F) :
    Integrable F ((muK ε).prod (muK ε)) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  exact hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem norm_integral_star_mul_le_sqrtK {ε : Fin n → Bool} {f g : KG ε → ℂ} (hf : Continuous f)
    (hg : Continuous g) :
    ‖∫ x, star (f x) * g x ∂(muK ε)‖ ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(muK ε)) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂(muK ε)) := by
  have hsq : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have re1 : ∀ h : KG ε → ℂ, (∫ x, star (h x) * h x ∂(muK ε)).re = ∫ x, ‖h x‖ ^ 2 ∂(muK ε) := by
    intro h; simp_rw [hsq]; rw [integral_complex_ofReal, Complex.ofReal_re]
  have H := GlobalTheory.norm_integral_star_mul_sq_le (muK ε) f g hf.aestronglyMeasurable hg.aestronglyMeasurable
    (integrable_of_continuousK (by fun_prop)) (integrable_of_continuousK (by fun_prop))
  rw [re1 f, re1 g] at H
  rw [← Real.sqrt_mul (integral_nonneg fun x => by positivity)]
  have := Real.abs_le_sqrt H
  rwa [abs_of_nonneg (norm_nonneg _)] at this


set_option maxHeartbeats 1600000 in
theorem sqrt_integral_normSq_le_integral_kernel_mul_translate :
    ∀ {n : ℕ} (ε : Fin n → Bool) (p : KG ε → ℂ) (κ : KG ε → ℝ), Continuous p → Continuous κ →
      (∀ k, 0 ≤ κ k) → ∫ k, κ k ∂(muK ε) = 1 →
      (∀ k, ∫ x, star (p x) * (κ (x⁻¹ * k) : ℂ) ∂(muK ε) = 0) →
      Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) ≤
        ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) := by
  intro n ε p κ hp hκ hκ0 hκ1 horth
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  have hsq : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have hA0 : 0 ≤ ∫ x, ‖p x‖ ^ 2 ∂(muK ε) := integral_nonneg fun x => by positivity
  have hAc : ∫ x, star (p x) * p x ∂(muK ε) = ((∫ x, ‖p x‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) := by
    simp_rw [hsq]; exact integral_complex_ofReal
  have htr : ∀ x, ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) = ∫ k, (κ (x⁻¹ * k) : ℂ) * p k ∂(muK ε) := by
    intro x
    have := integral_mul_left_eq_self (μ := muK ε) (fun k => (κ (x⁻¹ * k) : ℂ) * p k) x
    simpa only [inv_mul_cancel_left] using this
  have hzero : ∫ x, star (p x) * ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) ∂(muK ε) = 0 := by
    simp_rw [htr]
    have e1 : ∀ x, star (p x) * ∫ k, (κ (x⁻¹ * k) : ℂ) * p k ∂(muK ε) =
        ∫ k, star (p x) * ((κ (x⁻¹ * k) : ℂ) * p k) ∂(muK ε) := fun x => (integral_const_mul _ _).symm
    simp_rw [e1]
    have hint : Integrable (Function.uncurry fun x k => star (p x) * ((κ (x⁻¹ * k) : ℂ) * p k))
        ((muK ε).prod (muK ε)) :=
      integrable_prod_of_continuousK (F := fun z : KG ε × KG ε => star (p z.1) * ((κ (z.1⁻¹ * z.2) : ℂ) * p z.2))
        (by fun_prop)
    rw [integral_integral_swap hint]
    have e2 : ∀ k, ∫ x, star (p x) * ((κ (x⁻¹ * k) : ℂ) * p k) ∂(muK ε) =
        (∫ x, star (p x) * (κ (x⁻¹ * k) : ℂ) ∂(muK ε)) * p k := by
      intro k; rw [← integral_mul_const]; congr 1; funext x; ring
    simp_rw [e2, horth, zero_mul, integral_zero]
  have hκ1c : ∫ k, (κ k : ℂ) ∂(muK ε) = 1 := by rw [integral_complex_ofReal, hκ1, Complex.ofReal_one]
  have hinner : ∀ x, ∫ k, (κ k : ℂ) * (p x - p (x * k)) ∂(muK ε) =
      p x - ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) := by
    intro x
    have i1 : Integrable (fun k => (κ k : ℂ) * p x) (muK ε) := integrable_of_continuousK (by fun_prop)
    have i2 : Integrable (fun k => (κ k : ℂ) * p (x * k)) (muK ε) := integrable_of_continuousK (by fun_prop)
    simp_rw [mul_sub]
    rw [integral_sub i1 i2, integral_mul_const, hκ1c, one_mul]
  have hcontT : Continuous (fun x => ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε)) :=
    continuous_integral_paramK (F := fun x k => (κ k : ℂ) * p (x * k)) (by fun_prop)
  have hkey : ((∫ x, ‖p x‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) =
      ∫ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) ∂(muK ε) := by
    have e1 : ∀ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) =
        ∫ x, star (p x) * ((κ k : ℂ) * (p x - p (x * k))) ∂(muK ε) := by
      intro k; rw [← integral_const_mul]; congr 1; funext x; ring
    simp_rw [e1]
    have hint : Integrable (Function.uncurry fun x k => star (p x) * ((κ k : ℂ) * (p x - p (x * k))))
        ((muK ε).prod (muK ε)) :=
      integrable_prod_of_continuousK
        (F := fun z : KG ε × KG ε => star (p z.1) * ((κ z.2 : ℂ) * (p z.1 - p (z.1 * z.2)))) (by fun_prop)
    rw [← integral_integral_swap hint]
    have e2 : ∀ x, ∫ k, star (p x) * ((κ k : ℂ) * (p x - p (x * k))) ∂(muK ε) =
        star (p x) * p x - star (p x) * ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) := by
      intro x; rw [integral_const_mul, hinner, mul_sub]
    simp_rw [e2]
    have iA : Integrable (fun x => star (p x) * p x) (muK ε) := integrable_of_continuousK (by fun_prop)
    have iB : Integrable (fun x => star (p x) * ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε)) (muK ε) :=
      integrable_of_continuousK ((continuous_star.comp hp).mul hcontT)
    rw [integral_sub iA iB, hzero, sub_zero, hAc]
  have hCS : ∀ k, ‖∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)‖ ≤
      Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) :=
    fun k => norm_integral_star_mul_le_sqrtK (g := fun x => p x - p (x * k)) hp (by fun_prop)
  have hIc : Continuous (fun k => ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)) :=
    continuous_integral_paramK (F := fun k x => star (p x) * (p x - p (x * k))) (by fun_prop)
  have hDc : Continuous (fun k => ∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) :=
    continuous_integral_paramK (F := fun k x => ‖p x - p (x * k)‖ ^ 2) (by fun_prop)
  have hmain : ∫ x, ‖p x‖ ^ 2 ∂(muK ε) ≤ Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) *
      ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) := by
    have e : ∫ x, ‖p x‖ ^ 2 ∂(muK ε) =
        (∫ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) ∂(muK ε)).re := by
      rw [← hkey, Complex.ofReal_re]
    have hl : Continuous (fun k => ‖(κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)‖) := by
      fun_prop
    have hr : Continuous (fun k => κ k * (Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) *
        Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)))) := by fun_prop
    calc ∫ x, ‖p x‖ ^ 2 ∂(muK ε)
        ≤ ‖∫ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) ∂(muK ε)‖ := by
          rw [e]; exact Complex.re_le_norm _
      _ ≤ ∫ k, ‖(κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)‖ ∂(muK ε) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ k, κ k * (Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) *
            Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε))) ∂(muK ε) := by
          refine integral_mono (hl.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            (hr.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) fun k => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hκ0 k)]
          exact mul_le_mul_of_nonneg_left (hCS k) (hκ0 k)
      _ = _ := by rw [← integral_const_mul]; congr 1; funext k; ring
  rcases hA0.lt_or_eq with hpos | hz
  · have hs : 0 < Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) := Real.sqrt_pos.2 hpos
    refine le_of_mul_le_mul_left ?_ hs
    rw [Real.mul_self_sqrt hA0]
    exact hmain
  · rw [← hz, Real.sqrt_zero]
    exact integral_nonneg fun k => mul_nonneg (hκ0 k) (Real.sqrt_nonneg _)

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.LowerBoundConstAtLargeMultipleNumericalBounds
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem three_le_dimY_of_rank (D : D7) (j : ℕ) (hj : InR D j) (hr : 8 ≤ D.R.r) : 3 ≤ WeightFamilies.dimY D j := by
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := D.R.ord_pos
    omega
  have hs : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := Formalism.L2.Geo.sigW_sum D hj.1 hj.2
  unfold WeightFamilies.dimY
  generalize (D.R.sigW j).1 = a at hs ⊢
  generalize (D.R.sigW j).2 = b at hs ⊢
  have key : ∀ c : ℕ, 3 ≤ c → 3 ≤ c * (c - 1) / 2 := fun c hc => by
    have : 3 * 2 ≤ c * (c - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have h3 : 3 ≤ a * b + a * (a - 1) / 2 + b * (b - 1) / 2 := by
    rcases le_or_gt 3 a with h | h
    · have := key a h; omega
    · have := key b (by omega); omega
  calc 3 = 1 * 3 := rfl
    _ ≤ _ := Nat.mul_le_mul hf h3

theorem DF_add_one_le_size {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) : (DF w : ℝ) + 1 ≤ w.size := by
  unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
  have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
  push_cast at h2 ⊢
  linarith

theorem lamConst_lamR_rows : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 CL : ℝ) (N del : ℕ), InR D j → PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → 0 < CL → 0 < N → 0 < del → Real.log N ≤ nbR large₂ wL → Real.log del ≤ 1041 * Zb D large₂ ^ 3 → LamConst j large₂ CL 2 (wsmul (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL) (lamR large₂ CL wL) (8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊)) wL.size ∧ 3 ≤ WeightFamilies.dimY D j ∧ wL.n = nW ∧ 0 < wL.n ∧ (DF wL : ℝ) ≤ wL.size ∧ 2 ≤ wL.size ∧ 1 ≤ PO D large₂ ∧ 1 ≤ zBase large₂ ∧ cc D large₂ C2 A2 7 wL * (g0 D : ℝ) ≤ 1 / 2 ∧ PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2) ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) := by
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 CL N del hj hP hCL hN hdel hlN hld
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := D.R.ord_pos
    omega
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hPO : 1 ≤ PO D large₂ := by
    unfold PO
    have h1 : 0 ≤ 19 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * large₂.sc.L := by positivity
    have h2 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 2 * large₂.sc.L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hf') hL
    nlinarith
  obtain ⟨-, hS, h3, -⟩ := hP.hyp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hIL, -, -, -, -, h40, -, h22, -⟩ := hS
  obtain ⟨-, -, -, hc, -⟩ := h3
  obtain ⟨-, -, t1, t2, t3, -⟩ := hP.tie
  rw [t1, t2, t3] at hc
  have hdf : (3 : ℝ) ≤ DF wL := by exact_mod_cast hP.df
  have hsz := DF_add_one_le_size wL
  have hn : wL.n = nW := hIL.1
  refine ⟨?_, three_le_dimY_of_rank D j hj hP.r8, hn, by omega, by linarith, by linarith, hPO,
    WeightFamilies.one_le_zBase large₂, ?_, le_max_right _ _⟩
  · set n : ℕ := 8 * ((WeightFamilies.dimY D j + 2) * N) ^ 2 * (WeightFamilies.dimY D j + 1) * del * (1 + ⌈PO D large₂⌉₊) with hndef
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (by rw [hndef]; positivity)
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hs1 : (wsmul n wL).size ≤ (n : ℝ) * wL.size :=
      GlobalTheory.RunWeights.size_le_mul _ _ n hn1 (fun _ _ => le_rfl) (fun _ _ => le_rfl) le_rfl
    have hs0 : 1 ≤ (wsmul n wL).size := by
      have := DF_add_one_le_size (wsmul n wL)
      have h0 : (0 : ℝ) ≤ DF (wsmul n wL) := Nat.cast_nonneg _
      linarith
    have hP0 : 0 ≤ WeightFamilies.PP0v D large₂ CL 2 := by
      unfold WeightFamilies.PP0v
      rw [Real.rpow_two]
      positivity
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hdel' : (0 : ℝ) < del := by exact_mod_cast hdel
    have hceil : (1 : ℝ) + (⌈PO D large₂⌉₊ : ℝ) ≤ 2 + PO D large₂ := by
      have := Nat.ceil_lt_add_one (a := PO D large₂) (by linarith)
      linarith
    have hd0 : (0 : ℝ) ≤ WeightFamilies.dimY D j := Nat.cast_nonneg _
    have hnle : (n : ℝ) ≤ 8 * ((WeightFamilies.dimY D j : ℝ) + 2) ^ 3 * (2 + PO D large₂) * (N : ℝ) ^ 2 * del := by
      rw [hndef]
      push_cast
      calc 8 * (((WeightFamilies.dimY D j : ℝ) + 2) * N) ^ 2 * ((WeightFamilies.dimY D j : ℝ) + 1) * del * (1 + (⌈PO D large₂⌉₊ : ℝ))
          ≤ 8 * (((WeightFamilies.dimY D j : ℝ) + 2) * N) ^ 2 * ((WeightFamilies.dimY D j : ℝ) + 2) * del * (2 + PO D large₂) := by
            gcongr; norm_num
        _ = _ := by ring
    have hA : (0 : ℝ) < 8 * ((WeightFamilies.dimY D j : ℝ) + 2) ^ 3 * (2 + PO D large₂) := by positivity
    have hlogn := Real.log_le_log (by linarith) hnle
    rw [Real.log_mul (by positivity) hdel'.ne', Real.log_mul hA.ne' (by positivity), Real.log_pow] at hlogn
    push_cast at hlogn
    have hlogs := Real.log_le_log (by linarith) hs1
    rw [Real.log_mul (by linarith) (by linarith)] at hlogs
    have hl0 : 0 ≤ Real.log (wsmul n wL).size := Real.log_nonneg hs0
    have hmain : WeightFamilies.PP0v D large₂ CL 2 * (1 + Real.log (wsmul n wL).size) ≤ lamR large₂ CL wL := by
      refine le_trans ?_ (le_max_right _ _)
      exact mul_le_mul_of_nonneg_left (by linarith) hP0
    have hlam : 0 ≤ lamR large₂ CL wL := le_trans zero_le_one (le_max_left _ _)
    unfold LamConst
    rw [mul_assoc (lamR large₂ CL wL)]
    exact mul_le_mul hmain hs1 (by linarith) hlam
  · have hT : (2 : ℝ) ≤ Tn := by
      have : 2 ≤ Tn := by omega
      exact_mod_cast this
    rw [mul_assoc] at hc
    by_contra hcon
    push Not at hcon
    nlinarith

end GlobalTheory.RunJoin
end

