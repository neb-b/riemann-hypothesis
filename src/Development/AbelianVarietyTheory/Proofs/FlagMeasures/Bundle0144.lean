module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0128
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HolomorphicExtensionCompactRep
section
open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace
open MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.HolExt

theorem differentiable_det (n : ℕ) :
    Differentiable ℂ fun y : Fin n → Fin n → ℂ => (Matrix.of y).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  fun_prop

theorem differentiable_adjugate (n : ℕ) (i j : Fin n) :
    Differentiable ℂ fun y : Fin n → Fin n → ℂ => (Matrix.of y).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  have : (fun y : Fin n → Fin n → ℂ => ((Matrix.of y).updateRow j (Pi.single i 1)).det) =
      (fun y : Fin n → Fin n → ℂ => (Matrix.of y).det) ∘ fun y => Function.update y j (Pi.single i 1) := rfl
  rw [this]
  refine (differentiable_det n).comp (differentiable_pi.2 fun a => ?_)
  by_cases h : a = j
  · subst h
    simp
  · simp only [Function.update_of_ne h]
    fun_prop

theorem differentiableOn_inv (n : ℕ) (i j : Fin n) :
    DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => (Matrix.of y)⁻¹ i j) {y | IsUnit (Matrix.of y)} := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  refine ((differentiable_det n).differentiableOn.inv fun y hy => ?_).mul
    (differentiable_adjugate n i j).differentiableOn
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hy).ne_zero

def peak {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := 1 + 2 * n + 2 * g.trace.re

theorem peak_coe {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ((peak g : ℝ) : ℂ) = 1 + 2 * n + g.trace + gᴴ.trace := by
  rw [Matrix.trace_conjTranspose, add_assoc, Complex.star_def, Complex.add_conj, peak]
  push_cast
  ring

theorem peak_pos {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * g = 1) : 0 < peak g := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self (g + 1)).trace_nonneg
  have h2 := (Complex.le_def.1 h).1
  simp only [conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.mul_add, hg, Matrix.mul_one,
    Matrix.one_mul, trace_add, trace_one, trace_conjTranspose, Fintype.card_fin, Complex.add_re,
    Complex.natCast_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h2
  unfold peak
  linarith

theorem peak_lt {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * g = 1) (h1 : g ≠ 1) :
    peak g < peak (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self (g - 1)).trace_nonneg
  have hne : ((g - 1)ᴴ * (g - 1)).trace ≠ 0 := by
    rw [Ne, Matrix.trace_conjTranspose_mul_self_eq_zero_iff, sub_eq_zero]
    exact h1
  have h2 := (Complex.lt_def.1 (lt_of_le_of_ne h hne.symm)).1
  simp only [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, hg, Matrix.mul_one,
    Matrix.one_mul, trace_sub, trace_one, trace_conjTranspose, Fintype.card_fin, Complex.sub_re,
    Complex.natCast_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h2
  simp only [peak, trace_one, Fintype.card_fin, Complex.natCast_re]
  linarith

def intCLM {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K]
    (μ : Measure K) [IsFiniteMeasure μ] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (p : K → B) (hp : Continuous p) : C(K, ℂ) →L[ℂ] B := GlobalTheory.IntegralAgainstMeasure.integralAgainst μ ⟨p, hp⟩

theorem exists_holomorphic_extension : ∀ (n : ℕ) (ε : Fin n → Bool) (B : Type) [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → B), π 1 = 1 → (∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, π (a * b) = π a * π b) → ContinuousOn π (Formalism.REAL.Kset ε) → ∃ τ : Matrix (Fin n) (Fin n) ℂ → B, DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)} ∧ ∀ k ∈ Formalism.REAL.Kset ε, τ k = π k := by
  intro n ε B _ _ _ π h1 hmul hcont
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  haveI : TopologicalSpace.MetrizableSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : TopologicalSpace.MetrizableSpace (KG ε) := hemb.metrizableSpace
  haveI : SecondCountableTopology (KG ε) := hemb.secondCountableTopology
  set μ := muK ε
  have hmem : ∀ g : KG ε, toMK g ∈ Kset ε := fun g => g.2
  have hun : ∀ x ∈ Kset ε, xᴴ * x = 1 := fun x hx => Unitary.star_mul_self_of_mem hx.1
  have hu : Continuous fun g : KG ε => toMK g := hemb.continuous
  have hb : Continuous fun g : KG ε => π (toMK g) := hcont.comp_continuous hu hmem
  have hc : Continuous fun g : KG ε => peak (toMK g) := by
    unfold peak
    fun_prop
  have hone : toMK (1 : KG ε) = 1 := rfl
  have hlim := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    (μ := μ) (s := Set.univ) (x₀ := (1 : KG ε)) (c := fun g : KG ε => peak (toMK g))
    (g := fun g : KG ε => π (toMK g)) isCompact_univ hc.continuousOn
    (fun y _ hy => peak_lt (hun _ (hmem y)) fun h => hy (hemb.injective h))
    (fun y _ => (peak_pos (hun _ (hmem y))).le) (peak_pos (hun _ (hmem 1))) (by simp) hb.continuousOn
  simp only [Measure.restrict_univ, hone, h1] at hlim
  obtain ⟨N, hN⟩ := (hlim.eventually (Metric.ball_mem_nhds _ one_pos)).exists
  set c := ∫ g : KG ε, peak (toMK g) ^ N ∂μ
  set A := ∫ g : KG ε, peak (toMK g) ^ N • π (toMK g) ∂μ with hA
  have hint : Integrable (fun g : KG ε => peak (toMK g) ^ N • π (toMK g)) μ :=
    ((hc.pow N).smul hb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAu : ∃ A' : B, A * A' = 1 := by
    have e3 : ‖(1 : B) - c⁻¹ • A‖ < 1 := by
      rw [← dist_eq_norm, dist_comm]
      exact hN
    obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one e3
    rw [sub_sub_cancel] at hu
    refine ⟨c⁻¹ • (↑u⁻¹ : B), ?_⟩
    rw [mul_smul_comm, ← smul_mul_assoc, ← hu, Units.mul_inv]
  obtain ⟨A', hA'⟩ := hAu
  have hform : ∀ x ∈ Kset ε, π x * A = ∫ g : KG ε, peak (xᴴ * toMK g) ^ N • π (toMK g) ∂μ := by
    intro x hx
    obtain ⟨z, hz⟩ : x ∈ Set.range (fun g : KG ε => toMK g) := by
      rw [range_toMK]; exact hx
    have hz' : toMK z = x := hz
    have := (ContinuousLinearMap.mul ℂ B (π x)).integral_comp_comm hint
    rw [ContinuousLinearMap.mul_apply'] at this
    rw [hA, ← this,
      ← integral_mul_left_eq_self (fun g : KG ε => peak (xᴴ * toMK g) ^ N • π (toMK g)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : toMK (z * g) = x * toMK g := by rw [← hz']; rfl
    simp only [e]
    rw [← Matrix.mul_assoc, hun x hx, Matrix.one_mul, hmul _ hx _ (hmem g), ContinuousLinearMap.mul_apply',
      mul_smul_comm]
  let e : Fin n → Fin n → C(KG ε, ℂ) := fun i j => ⟨fun g => toMK g i j, hu.matrix_elem i j⟩
  let F : Matrix (Fin n) (Fin n) ℂ → C(KG ε, ℂ) := fun y =>
    ((1 + 2 * n : ℂ) • (1 : C(KG ε, ℂ)) + ∑ i, ∑ j, y⁻¹ i j • e j i + ∑ i, ∑ j, y j i • star (e j i)) ^ N
  refine ⟨fun y => intCLM μ _ hb (F y) * A', ?_, fun k hk => ?_⟩
  · refine DifferentiableOn.mul_const ((intCLM μ _ hb).differentiable.comp_differentiableOn ?_) _
    refine DifferentiableOn.pow (DifferentiableOn.add (DifferentiableOn.add (differentiableOn_const _) ?_) ?_) N
    · exact DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        (differentiableOn_inv n i j).smul_const _
    · refine DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        DifferentiableOn.smul_const ?_ _
      simp only [Matrix.of_apply]
      fun_prop
  · have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv (hun k hk)
    have hI : intCLM μ _ hb (F k) = π k * A := by
      rw [hform k hk]
      show ∫ g, F k g • π (toMK g) ∂μ = _
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have : F k g = ((peak (kᴴ * toMK g) ^ N : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow, peak_coe, conjTranspose_mul, conjTranspose_conjTranspose]
        simp [F, e, hinv, Matrix.trace, Matrix.mul_apply, mul_comm]
      simp only [this, Complex.coe_smul]
    show intCLM μ _ hb (F k) * A' = π k
    rw [hI, mul_assoc, hA', mul_one]

end GlobalTheory.HolExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InitialLengthsProductMomentLe
section
open MeasureTheory Finset
open scoped ENNReal

namespace GlobalTheory.MomentHolder

theorem initial_product_moment_le :
    ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r l : ℕ) (hl : l ≤ r + 1)
      (len : Fin (r + 1) → Ω → ℝ) (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) →
      (∀ a, ∀ᵐ x ∂ν, 0 < len a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) →
      ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr →
      (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (A ^ q)) →
      (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2,
        ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν
          ≤ ENNReal.ofReal (Rr ^ (2 * q))) →
      ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, len (Fin.castLE hl a) x ^ 2) * Ph x) ∂ν
        ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ l) := by
  intro Ω _ ν r l hl len Ph A Rr hlen hpos hPh h0 hmass hA hR hm0 hrat
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · simp [hmass]
  obtain ⟨s, rfl⟩ : ∃ s, l = s + 1 := ⟨l - 1, by omega⟩
  have hs : s ≤ r := by omega
  have hq' : ∀ q, q ≤ (s + 1) ^ 2 → q ≤ (r + 1) ^ 2 :=
    fun q hq => hq.trans (Nat.pow_le_pow_left (by omega) 2)
  have h1 : ∀ q ≤ (s + 1) ^ 2,
      ∫⁻ x, ENNReal.ofReal ((fun a : Fin (s + 1) => len (Fin.castLE hl a)) 0 x ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (A ^ q) := by
    intro q hq
    have e : Fin.castLE hl (0 : Fin (s + 1)) = 0 := Fin.ext (by simp)
    simp only [e]
    exact hm0 q (hq' q hq)
  have h2 : ∀ a : Fin s, ∀ q ≤ (s + 1) ^ 2,
      ∫⁻ x, ENNReal.ofReal (((fun a : Fin (s + 1) => len (Fin.castLE hl a)) a.succ x /
        (fun a : Fin (s + 1) => len (Fin.castLE hl a)) a.castSucc x) ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (Rr ^ (2 * q)) := by
    intro a q hq
    have e1 : Fin.castLE hl a.succ = (⟨a, by omega⟩ : Fin r).succ := Fin.ext (by simp)
    have e2 : Fin.castLE hl a.castSucc = (⟨a, by omega⟩ : Fin r).castSucc := Fin.ext (by simp)
    simp only [e1, e2]
    exact hrat _ q (hq' q hq)
  have key := product_moment_le Ω ν s (fun a => len (Fin.castLE hl a)) Ph A Rr
    (fun _ => hlen _) (fun _ => hpos _) hPh h0 hmass hA hR h1 h2
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  exact pow_le_pow_left₀ (mul_nonneg hA (pow_nonneg (zero_le_one.trans hR) _))
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (by omega)) hA) _

end GlobalTheory.MomentHolder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableAndNormAmplitudeLeOfPairings
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.OpNorm

theorem norm_le_sum_inner {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ W) (u : W) : ‖u‖ ≤ ∑ i, ‖⟪b i, u⟫_ℂ‖ := by
  calc ‖u‖ = ‖∑ i, ⟪b i, u⟫_ℂ • b i‖ := by rw [b.sum_repr']
    _ ≤ ∑ i, ‖⟪b i, u⟫_ℂ • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖⟪b i, u⟫_ℂ‖ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_smul, b.orthonormal.1 i, mul_one]

theorem rankOne_integral {X : Type} [MeasurableSpace X] (ν : Measure X)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (f : X → Wp) (g : X → Wq) (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 →
      ∫⁻ x, ENNReal.ofReal (‖⟪v, f x⟫_ℂ‖ * ‖⟪w, g x⟫_ℂ‖) ∂ν ≤ ENNReal.ofReal K) :
    Integrable (fun x => (innerSL ℂ (g x)).smulRight (f x)) ν ∧
      ‖∫ x, (innerSL ℂ (g x)).smulRight (f x) ∂ν‖ ≤ K := by
  haveI := FiniteDimensional.complete ℂ Wp
  set T : X → (Wq →L[ℂ] Wp) := fun x => (innerSL ℂ (g x)).smulRight (f x) with hT
  set e := stdOrthonormalBasis ℂ Wp
  set b := stdOrthonormalBasis ℂ Wq
  have hcont : Continuous (Function.uncurry fun (a : Wq) (c : Wp) => (innerSL ℂ a).smulRight c) := by
    fun_prop
  have hmeas : AEStronglyMeasurable T ν := hcont.comp_aestronglyMeasurable₂ hg hf
  have hbd : ∀ x, ‖f x‖ * ‖g x‖ ≤ ∑ j, ∑ i, ‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖ := fun x => by
    rw [← Finset.sum_mul_sum]
    exact mul_le_mul (norm_le_sum_inner e _) (norm_le_sum_inner b _) (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hnormT : ∀ x, ‖T x‖ = ‖g x‖ * ‖f x‖ := fun x => by
    simp only [hT, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  have hterm : ∀ j i, AEMeasurable
      (fun x => ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖)) ν := fun j i =>
    ((aestronglyMeasurable_const.inner hf).norm.mul
      (aestronglyMeasurable_const.inner hg).norm).aemeasurable.ennreal_ofReal
  have hfin : (∫⁻ x, ENNReal.ofReal ‖T x‖ ∂ν) < ⊤ := by
    calc (∫⁻ x, ENNReal.ofReal ‖T x‖ ∂ν)
        ≤ ∫⁻ x, ∑ j, ∑ i, ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖) ∂ν := by
          refine lintegral_mono fun x => ?_
          rw [hnormT, mul_comm]
          refine (ENNReal.ofReal_le_ofReal (hbd x)).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity]
          exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity
      _ = ∑ j, ∑ i, ∫⁻ x, ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖) ∂ν := by
          have hsum : ∀ j, AEMeasurable
              (fun x => ∑ i, ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖)) ν := by
            intro j
            first
              | exact Finset.aemeasurable_fun_sum _ fun i _ => hterm j i
              | exact Finset.aemeasurable_sum' _ fun i _ => hterm j i
              | exact (Finset.aemeasurable_sum _ fun i _ => hterm j i).congr
                  (Filter.Eventually.of_forall fun x => by simp [Finset.sum_apply])
          rw [MeasureTheory.lintegral_finsetSum' _ fun j _ => hsum j]
          exact Finset.sum_congr rfl fun j _ => MeasureTheory.lintegral_finsetSum' _ fun i _ => hterm j i
      _ ≤ ∑ j, ∑ i, ENNReal.ofReal K :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
            h (e j) (b i) (e.orthonormal.1 j) (b.orthonormal.1 i)
      _ < ⊤ := by simp [ENNReal.mul_lt_top]
  have hi : Integrable T ν := ⟨hmeas, hasFiniteIntegral_iff_norm _ |>.2 hfin⟩
  refine ⟨hi, ?_⟩
  have key : ∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 → ‖⟪v, (∫ x, T x ∂ν) w⟫_ℂ‖ ≤ K := by
    intro v w hv hw
    rw [ContinuousLinearMap.integral_apply hi w, ← integral_inner (hi.apply_continuousLinearMap w) v]
    refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal hK ?_)
    refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) (h v w hv hw)
    show ENNReal.ofReal ‖⟪v, ⟪g x, w⟫_ℂ • f x⟫_ℂ‖ = ENNReal.ofReal (‖⟪v, f x⟫_ℂ‖ * ‖⟪w, g x⟫_ℂ‖)
    rw [inner_smul_right, norm_mul, norm_inner_symm, mul_comm]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hK fun w hw => ?_
  set y := (∫ x, T x ∂ν) w
  by_cases hy : y = 0
  · rw [hy, norm_zero]; exact hK
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hv : ‖((‖y‖⁻¹ : ℝ) : ℂ) • y‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hy'), inv_mul_cancel₀ hy'.ne']
  have hk := key _ w hv hw
  rw [inner_smul_left, norm_mul, Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hy'), inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at hk
  calc ‖y‖ = ‖y‖⁻¹ * ‖y‖ ^ 2 := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hy'.ne', one_mul]
    _ ≤ K := hk

private theorem mul_mem_dualWeyl_complex {k r : ℕ} {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) :
    a * b ∈ GG k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private theorem measurableSet_of_isOpen' (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hc : IsClosed {x : Mt k r | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r} :=
    isClosed_eq ((hof.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hof) continuous_const
  exact hc.measurableSet

theorem integrable_and_norm_ampJ_le : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ν : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c K : ℝ), γ ∈ GG k r → ν {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → 0 < c → 0 ≤ K → (∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (‖⟪v, Φ (γ * Matrix.of x)⟫_ℂ‖ * ‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖) ∂ν ≤ ENNReal.ofReal K) → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) ν ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ ν c Φ Φ' γ)‖ ≤ K / c := by
  intro k r Wp _ _ _ Wq _ _ _ ν Φ Φ' γ c K hγ hν hΦ hΦ' hc hK h
  haveI := FiniteDimensional.complete ℂ Wp
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hS := measurableSet_of_isOpen' k r
  have hae : ν.restrict {x : Mt k r | Matrix.of x ∈ GG k r} = ν :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hν)
  have hf : AEStronglyMeasurable (fun x : Mt k r => Φ (γ * Matrix.of x)) ν := by
    rw [← hae]
    exact (hΦ.comp (continuous_const.mul hof).continuousOn fun x hx => mul_mem_dualWeyl_complex hγ hx).aestronglyMeasurable hS
  have hg : AEStronglyMeasurable (fun x : Mt k r => Φ' (Matrix.of x)) ν := by
    rw [← hae]
    exact (hΦ'.comp hof.continuousOn fun x hx => hx).aestronglyMeasurable hS
  obtain ⟨hi, hn⟩ := rankOne_integral ν _ _ hf hg K hK h
  refine ⟨hi, ?_⟩
  simp only [ampJ, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hn (inv_nonneg.2 hc.le)

end GlobalTheory.Amp.OpNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfLeftEigenvectorOfLattice
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

theorem isIntegral_of_left_eigenvector_of_lattice {E K : Type} [Field E] [NumberField E] [Field K]
    [Algebra E K] [Algebra (𝓞 E) K] [IsScalarTower (𝓞 E) E K] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (B : Matrix (Fin n) (Fin n) E) (c : E) (w : K)
    (v : Fin n → K) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hc : c ≠ 0) (hB : ∀ y ∈ Λ, ∃ z ∈ Λ, B *ᵥ y = c • z) (hv : v ≠ 0)
    (hw : v ᵥ* (B.map (algebraMap E K)) = (algebraMap E K c * w) • v) :
    IsIntegral (𝓞 E) w := by
  let φ : (Fin n → E) →ₗ[E] K :=
    { toFun := fun y => v ⬝ᵥ (fun i => algebraMap E K (y i))
      map_add' := by
        intro x y
        simp [dotProduct, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        simp [dotProduct, Finset.mul_sum, Algebra.smul_def, mul_left_comm] }
  have hφ : ∀ y, φ (B *ᵥ y) = (algebraMap E K c * w) * φ y := by
    intro y
    have h1 : (fun i => algebraMap E K ((B *ᵥ y) i))
        = (B.map (algebraMap E K)) *ᵥ (fun i => algebraMap E K (y i)) := by
      ext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mulVec, dotProduct, map_sum]
    show v ⬝ᵥ (fun i => algebraMap E K ((B *ᵥ y) i)) = _ * (v ⬝ᵥ (fun i => algebraMap E K (y i)))
    rw [h1, Matrix.dotProduct_mulVec, hw, smul_dotProduct, smul_eq_mul]
  have hcK : algebraMap E K c ≠ 0 := by simpa using hc
  let N : Submodule (𝓞 E) K := Λ.map (φ.restrictScalars (𝓞 E))
  refine isIntegral_of_smul_mem_submodule N ?_ (hfg.map _) w ?_
  · intro hN
    apply hv
    have h0 : ∀ y ∈ Λ, φ y = 0 := by
      intro y hy
      have : φ y ∈ N := ⟨y, hy, rfl⟩
      rw [hN] at this
      simpa using this
    have hk : (⊤ : Submodule E (Fin n → E)) ≤ LinearMap.ker φ := by
      rw [← hsp, Submodule.span_le]
      intro y hy
      exact h0 y hy
    ext i
    have := hk (Submodule.mem_top (x := Pi.single i (1 : E)))
    have h2 : v ⬝ᵥ (fun j => algebraMap E K ((Pi.single i (1 : E) : Fin n → E) j)) = 0 := this
    simpa [dotProduct, Pi.single_apply, apply_ite] using h2
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hyz⟩ := hB y hy
    refine ⟨z, hz, ?_⟩
    have h := hφ y
    rw [hyz, map_smul, Algebra.smul_def, mul_assoc] at h
    have h' := mul_left_cancel₀ hcK h
    simpa using h'

theorem trace_mem_of_nilpotent_mod_radical (E : Type) [Field E] [NumberField E] (n m g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hrad : (Ideal.span {(g : 𝓞 E)}).IsRadical) (hg : 1 ≤ g)
    (hA : ∀ y ∈ Λ, A *ᵥ y ∈ Λ) (hm : ∀ y ∈ Λ, ∃ z ∈ Λ, (A ^ m) *ᵥ y = (g : E) • z) :
    ∃ t : 𝓞 E, A.trace = (g : E) * (t : E) := by
  let K := AlgebraicClosure E
  let f : E →+* K := algebraMap E K
  let R := integralClosure (𝓞 E) K
  have hgE : (g : E) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  have hgK : (g : K) ≠ 0 := by
    have : f (g : E) ≠ 0 := by simpa only [map_ne_zero] using hgE
    simpa using this
  have hroot : ∀ z ∈ (A.map f).charpoly.roots,
      ∃ r : R, r ∈ (Ideal.span {(g : R)}).radical ∧ (r : K) = z := by
    intro z hz
    have h0 : (Matrix.scalar (Fin n) z - A.map f).det = 0 := by
      rw [← Matrix.eval_charpoly]
      exact (Polynomial.mem_roots'.1 hz).2
    obtain ⟨v, hv, hvz⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    have h1 : v ᵥ* (A.map f) = z • v := by
      rw [Matrix.vecMul_sub, sub_eq_zero] at hvz
      rw [← hvz]
      ext i
      simp [Matrix.vecMul_diagonal, mul_comm]
    have hk : ∀ k : ℕ, v ᵥ* ((A ^ k).map f) = z ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, Matrix.map_mul, ← Matrix.vecMul_vecMul, ih, Matrix.smul_vecMul, h1,
          smul_smul, pow_succ]
    have hi1 : IsIntegral (𝓞 E) z :=
      isIntegral_of_left_eigenvector_of_lattice Λ A 1 z v hfg hsp one_ne_zero
        (fun y hy => ⟨_, hA y hy, by simp⟩) hv (by simpa using h1)
    have hi2 : IsIntegral (𝓞 E) (z ^ m / (g : K)) :=
      isIntegral_of_left_eigenvector_of_lattice Λ (A ^ m) (g : E) _ v hfg hsp hgE hm hv (by
        rw [map_natCast, mul_div_cancel₀ _ hgK]
        exact hk m)
    refine ⟨⟨z, hi1⟩, ⟨m, Ideal.mem_span_singleton'.2 ⟨⟨_, hi2⟩, ?_⟩⟩, rfl⟩
    apply Subtype.ext
    show z ^ m / (g : K) * ((g : R) : K) = z ^ m
    have : ((g : R) : K) = (g : K) := by simp
    rw [this, div_mul_cancel₀ _ hgK]
  have hsum : ∃ r : R, r ∈ (Ideal.span {(g : R)}).radical ∧
      (r : K) = (A.map f).charpoly.roots.sum := by
    refine Multiset.sum_induction (fun x : K => ∃ r : R,
      r ∈ (Ideal.span {(g : R)}).radical ∧ (r : K) = x) _ ?_ ⟨0, Ideal.zero_mem _, rfl⟩ hroot
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, Ideal.add_mem _ ha hb, rfl⟩
  rw [← Matrix.trace_eq_sum_roots_charpoly, ← AddMonoidHom.map_trace f A] at hsum
  obtain ⟨r, ⟨N, hN⟩, hr⟩ := hsum
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hN
  have hdown : ∀ x : E, IsIntegral (𝓞 E) (f x) → ∃ t : 𝓞 E, (t : E) = x := by
    intro x hx
    exact IsIntegrallyClosed.isIntegral_iff.1
      ((isIntegral_algebraMap_iff ).1 hx)
  obtain ⟨t₀, ht₀⟩ := hdown A.trace (hr ▸ r.2)
  have hsK : (s : K) * (g : K) = f A.trace ^ N := by
    have := congrArg (fun x : R => (x : K)) hs
    simpa [hr] using this
  obtain ⟨u, hu⟩ := hdown (A.trace ^ N / (g : E)) (by
    rw [map_div₀, map_pow, map_natCast, ← hsK, mul_div_cancel_right₀ _ hgK]
    exact s.2)
  have hmem : t₀ ∈ Ideal.span {(g : 𝓞 E)} := by
    apply hrad
    refine ⟨N, Ideal.mem_span_singleton'.2 ⟨u, ?_⟩⟩
    apply RingOfIntegers.coe_injective
    have h : (u : E) * (g : E) = (t₀ : E) ^ N := by
      rw [hu, ht₀, div_mul_cancel₀ _ hgE]
    simpa using h
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨t, ?_⟩
  rw [← ht₀, ← ht]
  simp [mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsMirabolicConjInvariantTwistedTailMeanFunStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMirabolicConjInvariant_twistedTailMeanFun : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (m n : ℕ) (F : Gn g n → ℂ), 1 ≤ m → m ≤ n → IsMirClass F → IsMirClass (tail ψ m F) := by
  first | exact @GlobalTheory.GLm.TailClass.isMirClass_tail | exact GlobalTheory.GLm.TailClass.isMirClass_tail | (intros; apply GlobalTheory.GLm.TailClass.isMirClass_tail <;> assumption)
end

