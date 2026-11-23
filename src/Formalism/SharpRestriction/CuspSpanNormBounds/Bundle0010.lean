module

public import Formalism.SharpRestriction.CuspSpanNormBounds.StarVecMulDM
public import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SigmaFiniteRestrictSubgroup
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrsSecondCountableAbs
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0003
public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrdStronglyMeasurable
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnitaryRepUnimodularOfFiniteVolume
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkbLeOneAddSq
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0002
public import Formalism.LogSumExpBounds.StatementD
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
public import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
public import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
public import Formalism.GelfandTransference.Bundle0001
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.LatticeRigidity.StatementC
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0003
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ExistsTowerOfLocalSetting
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.BesselExistenceUniformOfFacts
public import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BcWeightEqZeroOf
section
open MeasureTheory Matrix Finset
open scoped ContDiff

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def sBig (r : ℕ) (κ τ : ℝ) (p : (Fin r → ℂ) × ℂ) : (Fin r → ℂ) × ℂ :=
  (fun a => ((tF r κ τ a.val ^ 2 : ℝ) : ℂ) * p.1 a, ((τ ^ 2 : ℝ) : ℂ) * p.2)

def sBigL (r : ℕ) (κ τ : ℝ) : ((Fin r → ℂ) × ℂ) →ₗ[ℝ] ((Fin r → ℂ) × ℂ) :=
  LinearMap.prodMap (LinearMap.pi fun a => ((tF r κ τ a.val ^ 2) • LinearMap.id) ∘ₗ LinearMap.proj a)
    ((τ ^ 2) • LinearMap.id)

theorem sBigL_apply (r : ℕ) (κ τ : ℝ) (p : (Fin r → ℂ) × ℂ) : sBigL r κ τ p = sBig r κ τ p := by
  ext a <;> simp [sBigL, sBig, Complex.real_smul]

def jacBig (r : ℕ) (κ τ : ℝ) : ℝ := (∏ a : Fin r, tF r κ τ a.val ^ 4) * τ ^ 4

def wBig (k r : ℕ) (κ τ : ℝ) : ℝ :=
  (∏ a : Fin r, (tF r κ τ a.val ^ 2) ^ (2 * (Mdim k r a - 2))) * (τ ^ 4) ^ (k - 1)

section Norm

variable {k r : ℕ} {κ τ : ℝ}

theorem det_sBigL : LinearMap.det (sBigL r κ τ) = jacBig r κ τ := by
  rw [sBigL, LinearMap.det_prodMap, LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex, mul_one, jacBig]
  congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_; ring
  · ring

theorem jacBig_pos (hκ : 0 < κ) (hτ : 0 < τ) : 0 < jacBig r κ τ :=
  mul_pos (Finset.prod_pos fun a _ => pow_pos (tF_pos hκ hτ _) 4) (pow_pos hτ 4)

theorem wBig_pos (hκ : 0 < κ) (hτ : 0 < τ) : 0 < wBig k r κ τ :=
  mul_pos (Finset.prod_pos fun a _ => pow_pos (pow_pos (tF_pos hκ hτ _) 2) _) (pow_pos (pow_pos hτ 4) _)

theorem lintegral_sBig (hκ : 0 < κ) (hτ : 0 < τ) (G : (Fin r → ℂ) × ℂ → ENNReal) :
    ∫⁻ p, G p = ENNReal.ofReal (jacBig r κ τ) * ∫⁻ p, G (sBig r κ τ p) := by
  have hdet : LinearMap.det (sBigL r κ τ) ≠ 0 := by rw [det_sBigL]; exact (jacBig_pos hκ hτ).ne'
  let e : ((Fin r → ℂ) × ℂ) ≃ₗ[ℝ] ((Fin r → ℂ) × ℂ) := LinearMap.equivOfDetNeZero (sBigL r κ τ) hdet
  let eM : ((Fin r → ℂ) × ℂ) ≃ᵐ ((Fin r → ℂ) × ℂ) := e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have : (volume : Measure ((Fin r → ℂ) × ℂ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
  have hmap : Measure.map eM (volume : Measure ((Fin r → ℂ) × ℂ)) =
      ENNReal.ofReal |(LinearMap.det (sBigL r κ τ))⁻¹| • volume := by
    rw [← Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet]
    rfl
  have h1 : ∫⁻ p, G (sBig r κ τ p) = ENNReal.ofReal |(jacBig r κ τ)⁻¹| * ∫⁻ p, G p := by
    have : (fun p => G (sBig r κ τ p)) = fun p => G (eM p) := by
      funext p; rw [← sBigL_apply]; rfl
    rw [this, ← lintegral_map_equiv, hmap, lintegral_smul_measure, det_sBigL, smul_eq_mul]
  rw [h1, ← mul_assoc, ← ENNReal.ofReal_mul (jacBig_pos hκ hτ).le, abs_inv,
    abs_of_pos (jacBig_pos hκ hτ), mul_inv_cancel₀ (jacBig_pos hκ hτ).ne', ENNReal.ofReal_one, one_mul]

theorem bcWeight_sBig (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (p : (Fin r → ℂ) × ℂ) :
    bcWeight k r (τ ^ 2 * T) (τ ^ 2 * T') (sBig r κ τ p) = wBig k r κ τ * bcWeight k r T T' p := by
  have hn : Complex.normSq (((τ ^ 2 : ℝ) : ℂ) * p.2) = τ ^ 4 * Complex.normSq p.2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]; ring
  have h4 : 0 < τ ^ 4 := pow_pos hτ 4
  unfold bcWeight sBig
  simp only
  rw [hn]
  by_cases hc : T * T' ≤ Complex.normSq p.2
  · rw [if_pos (by nlinarith), if_pos hc]
    have hprod : ∏ a : Fin r, ‖((tF r κ τ a.val ^ 2 : ℝ) : ℂ) * p.1 a‖ ^ (2 * (Mdim k r a - 2)) =
        (∏ a : Fin r, (tF r κ τ a.val ^ 2) ^ (2 * (Mdim k r a - 2))) *
          ∏ a : Fin r, ‖p.1 a‖ ^ (2 * (Mdim k r a - 2)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos (tF_pos hκ hτ _) 2), mul_pow]
    rw [hprod, show τ ^ 4 * Complex.normSq p.2 - τ ^ 2 * T * (τ ^ 2 * T') =
      τ ^ 4 * (Complex.normSq p.2 - T * T') by ring, mul_pow, wBig]
    ring
  · rw [if_neg (by intro h; apply hc; nlinarith), if_neg hc, mul_zero]

theorem hsNormSq_eq_sum {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

theorem hsNormSq_nonneg {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_sum]; positivity

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (C : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (C • A) = ‖C‖ ^ 2 * hsNormSq A := by
  rw [hsNormSq_eq_sum, hsNormSq_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FunLike.coe_smul, Pi.smul_apply, norm_smul, mul_pow]

theorem bcWeight_eq_zero_of {T T' : ℝ} (hk : 2 ≤ k) (p : (Fin r → ℂ) × ℂ)
    (h : ¬ ((∀ a, p.1 a ≠ 0) ∧ T * T' < Complex.normSq p.2)) : bcWeight k r T T' p = 0 := by
  unfold bcWeight
  split_ifs with hc
  · rcases not_and_or.mp h with h1 | h1
    · push Not at h1
      obtain ⟨a, ha⟩ := h1
      have hpos : 2 * (Mdim k r a - 2) ≠ 0 := by unfold Mdim; omega
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (by rw [ha, norm_zero, zero_pow hpos]), zero_mul]
    · have : Complex.normSq p.2 = T * T' := le_antisymm (not_lt.mp h1) hc
      rw [this, sub_self, zero_pow (by omega), mul_zero]
  · rfl

theorem jNorm2_tr (hκ : 0 < κ) (hτ : 0 < τ) (L L₁ : LocBessel k r)
    (e1 : Tz k r L₁.z = τ ^ 2 * Tz k r L.z) (e2 : Tz k r L₁.z' = τ ^ 2 * Tz k r L.z')
    (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (f₁ : Mx k r → (L₁.Wq →L[ℂ] L₁.Wp))
    (μsec μsec₁ : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (C : ℂ)
    (hk : 2 ≤ k)
    (hJ : ∀ p : (Fin r → ℂ) × ℂ, (∀ a, p.1 a ≠ 0) → Tz k r L.z * Tz k r L.z' < Complex.normSq p.2 →
      hsNormSq (L₁.J f₁ (bigCell k r (sBig r κ τ p).1 (μsec₁ (sBig r κ τ p).2))) =
        ‖C‖ ^ 2 * hsNormSq (L.J f (bigCell k r p.1 (μsec p.2)))) :
    jNorm2 L₁ f₁ μsec₁ = ENNReal.ofReal (jacBig r κ τ * wBig k r κ τ * ‖C‖ ^ 2) * jNorm2 L f μsec := by
  unfold jNorm2 jNormSq
  rw [e1, e2, lintegral_sBig hκ hτ]
  have hw := wBig_pos (k := k) (r := r) hκ hτ
  have hpt : ∀ p : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (bcWeight k r (τ ^ 2 * Tz k r L.z) (τ ^ 2 * Tz k r L.z') (sBig r κ τ p) *
        ‖Real.sqrt (hsNormSq (L₁.J f₁ (bigCell k r (sBig r κ τ p).1 (μsec₁ (sBig r κ τ p).2))))‖ ^ 2) =
      ENNReal.ofReal (wBig k r κ τ * ‖C‖ ^ 2) *
        ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
          ‖Real.sqrt (hsNormSq (L.J f (bigCell k r p.1 (μsec p.2))))‖ ^ 2) := by
    intro p
    by_cases hD : (∀ a, p.1 a ≠ 0) ∧ Tz k r L.z * Tz k r L.z' < Complex.normSq p.2
    swap
    · have h0 := bcWeight_eq_zero_of (T := Tz k r L.z) (T' := Tz k r L.z') hk p (by tauto)
      rw [bcWeight_sBig hκ hτ, h0]; simp
    rw [← ENNReal.ofReal_mul (by positivity), hJ p hD.1 hD.2, bcWeight_sBig hκ hτ,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      Real.sq_sqrt (mul_nonneg (sq_nonneg _) (hsNormSq_nonneg _)), Real.sq_sqrt (hsNormSq_nonneg _)]
    congr 1; ring
  beta_reduce
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul (jacBig_pos hκ hτ).le,
    mul_assoc (jacBig r κ τ)]

theorem wbPart_smul (z : Fin (2 * r + k + 1) → ℂ) (t : ℂ) : wbPart k r (t • z) = t • wbPart k r z := by
  funext j; rfl

def secTr (τ : ℝ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun ζ => μsec (ζ / ((τ ^ 2 : ℝ) : ℂ))

theorem secTr_sBig (hτ : 0 < τ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin r → ℂ) × ℂ) :
    secTr τ μsec (sBig r κ τ p).2 = μsec p.2 := by
  unfold secTr sBig
  have : ((τ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hτ 2).ne'
  simp only
  rw [mul_div_cancel_left₀ _ this]

theorem isSection_tr (hτ : 0 < τ) {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h : IsSection k r z z' μsec) : IsSection k r ((τ : ℂ) • z) ((τ : ℂ) • z') (secTr τ μsec) := by
  have h2 : ((τ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hτ 2).ne'
  have h4 : 0 < τ ^ 4 := pow_pos hτ 4
  have hns : ∀ ζ : ℂ, Complex.normSq (ζ / ((τ ^ 2 : ℝ) : ℂ)) = Complex.normSq ζ / τ ^ 4 := by
    intro ζ; rw [Complex.normSq_div, Complex.normSq_ofReal]; ring
  have hreg : ∀ ζ : ℂ, Tz k r ((τ : ℂ) • z) * Tz k r ((τ : ℂ) • z') < Complex.normSq ζ →
      Tz k r z * Tz k r z' < Complex.normSq (ζ / ((τ ^ 2 : ℝ) : ℂ)) := by
    intro ζ hζ
    rw [Tz_smul, Tz_smul] at hζ
    rw [hns, lt_div_iff₀ h4]; nlinarith
  refine ⟨fun i j => ?_, fun ζ hζ => ?_⟩
  · have hc : ContDiff ℝ ∞ (fun ζ : ℂ => ζ / ((τ ^ 2 : ℝ) : ℂ)) := by
      have : (fun ζ : ℂ => ζ / ((τ ^ 2 : ℝ) : ℂ)) = fun ζ => ((τ ^ 2)⁻¹ : ℝ) • ζ := by
        funext ζ; rw [Complex.real_smul, div_eq_inv_mul]; push_cast; ring
      rw [this]; exact contDiff_const_smul _
    exact (h.1 i j).comp hc.contDiffOn fun ζ hζ => hreg ζ hζ
  · obtain ⟨hu, hv⟩ := h.2 _ (hreg ζ hζ)
    refine ⟨hu, ?_⟩
    unfold secTr
    rw [wbPart_smul, wbPart_smul]
    unfold herm at hv ⊢
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, hv]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    field_simp
    push_cast; ring

end Norm

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.DiscreteSeriesInnerProducts

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.TheoremBConstants

section Fdeg

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem integral_normSq_coef {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} :
    ∫ g, f g * star (f g) ∂μ = ((∫ g, ‖f g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  funext g
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem inner_self_C {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : E) :
    ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  simp

theorem fdegOf_eq {μ : Measure (Formalism.REAL.UJ ε)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (h : IsFdeg μ σ d) {v : H} (hv : v ≠ 0) : fdegOf μ σ v = d := by
  obtain ⟨hd, hF⟩ := h
  have e := (hF v v v v).2
  rw [integral_normSq_coef, inner_self_C] at e
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have e' : (∫ g, ‖coefOn σ v v g‖ ^ 2 ∂μ) = ‖v‖ ^ 4 / d := by
    have : (((∫ g, ‖coefOn σ v v g‖ ^ 2 ∂μ : ℝ)) : ℂ) = ((‖v‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [e]; push_cast; ring_nf
    exact_mod_cast this
  unfold fdegOf
  rw [e']
  field_simp

end Fdeg

section SchurH

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end SchurH

section P90P

open Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

theorem ds_one (hσ : IsDSHpk k r ε lam σ) : σ 1 = 1 := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have h := hDS.2.2.1.1.1
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  simpa [Matrix.nonsing_inv_mul _ hu] using h

theorem ds_inv_adj (hσ : IsDSHpk k r ε lam σ) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) (y z : H) : ⟪σ a⁻¹ y, z⟫_ℂ = ⟪y, σ a z⟫_ℂ := by
  have h1 := Formalism.MainNotions.LeviCoordinates.discrete_series_inner hσ ha (σ a⁻¹ y) z
  have h2 : σ a (σ a⁻¹ y) = y := by
    have e : σ (a * a⁻¹) = (σ a).comp (σ a⁻¹) := Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ ha (uh_inv ha)
    rw [Matrix.mul_nonsing_inv _ (isUnit_of_uh ha), ds_one hσ] at e
    have := congrArg (fun T : H →L[ℂ] H => T y) e
    simpa using this.symm
  rw [h2] at h1
  exact h1.symm

end P90P

section Named

open Formalism.QuantumDeterminants.WeylGroupFacts

def KFinSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ → ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → v ∈ smoothVecs (k := k) (r := r) σ

end Named

end Formalism.MainNotions.DiscreteSeriesInnerProducts
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.BridgeCS3d

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

theorem dsigW_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    PI.UpqRep.dsigW (k := k) (r := r) σ w v = Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v := by
  induction w generalizing v with
  | nil => rfl
  | cons X w ih =>
    show PI.UpqRep.dsig (k := k) (r := r) σ X (PI.UpqRep.dsigW (k := k) (r := r) σ w v) =
      Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v)
    rw [ih]
    rfl

theorem isBesselMapSm_iff {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ)
    (ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (l : H → Wp) :
    Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π l ↔
      PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π l := by
  simp only [PI.BesselMapUniq.IsBesselMapSm, Formalism.MainNotions.S.IsBesselMapSm, PI.BesselMapUniq.IsCWCont,
    Formalism.MainNotions.S.IsCWCont, dsigW_eq]
  exact Iff.rfl

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

end Formalism.MainNotions.BridgeCS3d
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures
section

end

