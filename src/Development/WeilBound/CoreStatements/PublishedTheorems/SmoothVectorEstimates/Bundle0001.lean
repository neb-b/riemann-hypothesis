module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.ExistsLogarithmLinear
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace ExistsLogarithmLinear

theorem exists_log_lin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (χ : AddChar V ℂ) (hχ : Continuous χ)
    (h0 : ∀ z, χ z ≠ 0) : ∃ L : V →L[ℝ] ℂ, ∀ z, χ z = Complex.exp (L z) := by
  let f : C(V, {z : ℂ // z ≠ 0}) := ⟨fun z => ⟨χ z, h0 z⟩, hχ.subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (Subtype.ext (by simp [f]))
  have hF' : ∀ z, Complex.exp (F z) = χ z := fun z => congrArg Subtype.val (congrFun hF z)
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y => F (x + y) - F y := by fun_prop
    have := Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by
      simp only [Complex.exp_sub, hF', AddChar.map_add_eq_mul]
      rw [mul_div_assoc, mul_div_assoc, div_self (h0 _), div_self (h0 _)])) y 0
    simp only [add_zero, hF0, sub_zero] at this
    rw [← this]; ring
  exact ⟨(AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous, fun z => (hF' z).symm⟩

end ExistsLogarithmLinear

theorem exists_logarithm_linear : S8 := by
  intro ι _ χ hχ h1
  obtain ⟨L, hL⟩ := ExistsLogarithmLinear.exists_log_lin χ hχ (fun z h => by simpa [h] using h1 z)
  refine ⟨Complex.imCLM.comp L, fun z => ?_⟩
  have hre : (L z).re = 0 := by
    have := h1 z
    rw [hL z, Complex.norm_exp] at this
    exact Real.exp_eq_one_iff _ |>.1 this
  rw [hL z]
  congr 1
  apply Complex.ext <;> simp [hre]

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FourierIntegralBound
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace FourierIntegralBound

open Real

lemma one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) :=
  _root_.UpperTheory.Reformulated.B.OneAddPowLeTwoPowMul.main t ht N

lemma pi_pow_le {d : ℕ} (z : Fin d → ℝ) (N : ℕ) : ‖z‖ ^ N ≤ 1 + ∑ i, |z i| ^ N := by
  have hs : 0 ≤ ∑ i, |z i| ^ N := Finset.sum_nonneg (fun i _ => by positivity)
  rcases isEmpty_or_nonempty (Fin d) with h | h
  · have : ‖z‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => isEmptyElim i)
    have h0 : ‖z‖ ^ N ≤ 1 := pow_le_one₀ (norm_nonneg _) this
    linarith
  · obtain ⟨i0, -, hi0⟩ :=
      Finset.exists_max_image Finset.univ (fun i => |z i|) Finset.univ_nonempty
    have h1 : ‖z‖ ≤ |z i0| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 (fun i => by
      rw [Real.norm_eq_abs]; exact hi0 i (Finset.mem_univ _))
    have h2 : ‖z‖ ^ N ≤ |z i0| ^ N := pow_le_pow_left₀ (norm_nonneg _) h1 N
    have h3 : |z i0| ^ N ≤ ∑ i, |z i| ^ N :=
      Finset.single_le_sum (f := fun i => |z i| ^ N) (fun i _ => by positivity) (Finset.mem_univ i0)
    linarith

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def sc (β : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V →L[ℝ] ℝ := (2 * π)⁻¹ • β

lemma sc_apply (β : V →L[ℝ] V →L[ℝ] ℝ) (x y : V) : sc β x y = (2 * π)⁻¹ * β x y := by
  simp [sc]

lemma FT_eq [MeasurableSpace V] {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (μ : Measure V) (β : V →L[ℝ] V →L[ℝ] ℝ) (F : V → X) :
    FT μ β F = VectorFourier.fourierIntegral Real.fourierChar μ (sc β).toLinearMap₁₂ F := by
  ext y
  unfold FT VectorFourier.fourierIntegral
  congr 1
  ext x
  rw [Circle.smul_def, Real.fourierChar_apply]
  congr 2
  rw [show (sc β).toLinearMap₁₂ x y = sc β x y from rfl, sc_apply]
  push_cast
  field_simp

lemma exists_strictHenselian_absolutely_closed_local_ring [FiniteDimensional ℝ V] (β : V →L[ℝ] V →L[ℝ] ℝ)
    (hβ : ∀ y, (∀ x, β x y = 0) → y = 0) :
    ∃ (d : ℕ) (b : Fin d → V) (K : ℝ), 0 ≤ K ∧
      ∀ y, ‖y‖ ≤ K * ‖(fun i => β (b i) y : Fin d → ℝ)‖ := by
  let b := Module.finBasis ℝ V
  let T : V →ₗ[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
    LinearMap.pi (fun i => ((β (b i) : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ))
  have hT : ∀ y, T y = fun i => β (b i) y := fun y => rfl
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    apply hβ y
    have h1 : ∀ i, β (b i) y = 0 := fun i => by
      have := congrFun hy i
      rw [hT] at this
      simpa using this
    have h2 : ((β.flip y : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ) = 0 :=
      b.ext (fun i => by simpa using h1 i)
    intro x
    have := LinearMap.congr_fun h2 x
    simpa using this
  obtain ⟨K, -, hK⟩ := T.exists_antilipschitzWith hker
  refine ⟨_, b, K, K.2, fun y => ?_⟩
  have := hK.le_mul_dist y 0
  rw [map_zero, dist_zero_right, dist_zero_right] at this
  exact this

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

omit [FiniteDimensional ℝ V] in
lemma integ {F : V → X} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (μ : Measure V)
    [IsFiniteMeasureOnCompacts μ] (k n : ℕ) :
    Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n F v‖) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_norm.pow k).mul (hF.continuous_iteratedFDeriv (mod_cast le_top)).norm
  · exact (hc.iteratedFDeriv n).norm.mul_left

lemma pw_bd (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →L[ℝ] V →L[ℝ] ℝ) {F : V → X}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (n : ℕ) :
    ∃ B : ℝ, ∀ v y, |β v y| ^ n * ‖FT μ β F y‖ ≤ ‖v‖ ^ n * B := by
  refine ⟨(2 * π) ^ n * ((2 * π * ‖sc β‖) ^ 0 * (2 * ((0 : ℕ) : ℝ) + 2) ^ n *
      ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 F v‖ ∂μ), fun v y => ?_⟩
  have H := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (L := sc β) (μ := μ)
    (K := ⊤) (N := ⊤) hF (fun k n _ _ => integ hF hc μ k n) (k := 0) (n := n) le_top le_top v y
  rw [norm_iteratedFDeriv_zero, ← FT_eq] at H
  have e : |β v y| = 2 * π * |sc β v y| := by
    rw [sc_apply, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹)]
    field_simp
  rw [e, mul_pow, mul_assoc]
  calc (2 * π) ^ n * (|sc β v y| ^ n * ‖FT μ β F y‖)
      ≤ (2 * π) ^ n * (‖v‖ ^ n * (2 * π * ‖sc β‖) ^ 0 * (2 * ((0 : ℕ) : ℝ) + 2) ^ n *
          ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
            ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 F v‖ ∂μ) := by gcongr
    _ = _ := by ring

end FourierIntegralBound

open FourierIntegralBound in
theorem valuation_bound_of_three : S4 := by
  unfold S4 ForV
  intro V _ _ _ _ _ μ _ β hβ X _ _ _ F hF hc
  refine ⟨?_, fun N => ?_⟩
  · rw [FT_eq]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by apply (sc β).continuous₂) (hF.continuous.integrable_of_hasCompactSupport hc)
  · obtain ⟨d, b, K, hK0, hK⟩ := exists_strictHenselian_absolutely_closed_local_ring β hβ
    obtain ⟨A, hA⟩ := pw_bd μ β hF hc 0
    obtain ⟨B, hB⟩ := pw_bd μ β hF hc N
    refine ⟨2 ^ N * (A + K ^ N * (A + ∑ i, ‖b i‖ ^ N * B)), fun y => ?_⟩
    have hA' : ‖FT μ β F y‖ ≤ A := by simpa using hA 0 y
    have hy := pi_pow_le (fun i => β (b i) y) N
    have h1 : ‖y‖ ^ N ≤ K ^ N * (1 + ∑ i, |β (b i) y| ^ N) := by
      calc ‖y‖ ^ N ≤ (K * ‖(fun i => β (b i) y : Fin d → ℝ)‖) ^ N :=
            pow_le_pow_left₀ (norm_nonneg _) (hK y) N
        _ = K ^ N * ‖(fun i => β (b i) y : Fin d → ℝ)‖ ^ N := mul_pow _ _ _
        _ ≤ _ := by gcongr
    have h3 : (1 + ∑ i, |β (b i) y| ^ N) * ‖FT μ β F y‖ ≤ A + ∑ i, ‖b i‖ ^ N * B := by
      rw [add_mul, Finset.sum_mul, one_mul]
      exact add_le_add hA' (Finset.sum_le_sum fun i _ => hB (b i) y)
    have hFn := norm_nonneg (FT μ β F y)
    calc (1 + ‖y‖) ^ N * ‖FT μ β F y‖ ≤ 2 ^ N * (1 + ‖y‖ ^ N) * ‖FT μ β F y‖ := by
          gcongr; exact one_add_pow_le _ (norm_nonneg _) N
      _ = 2 ^ N * (‖FT μ β F y‖ + ‖y‖ ^ N * ‖FT μ β F y‖) := by ring
      _ ≤ 2 ^ N * (A + K ^ N * (A + ∑ i, ‖b i‖ ^ N * B)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hA' ?_) (by positivity)
          calc ‖y‖ ^ N * ‖FT μ β F y‖
              ≤ K ^ N * (1 + ∑ i, |β (b i) y| ^ N) * ‖FT μ β F y‖ := by gcongr
            _ = K ^ N * ((1 + ∑ i, |β (b i) y| ^ N) * ‖FT μ β F y‖) := by ring
            _ ≤ _ := by gcongr

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.HaarPairing
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace HaarPairing

open scoped FourierTransform RealInnerProductSpace Real SchwartzMap

theorem inv_E {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (v : EuclideanSpace ℝ (Fin d)) :
    ∫ w, 𝐞 ⟪w, v⟫ • (∫ z, 𝐞 (-⟪z, w⟫) • g z) = g v := by
  have hI : Integrable (𝓕 g) := by
    let G : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := 𝓕 (hc.toSchwartzMap hg)
    have e : (𝓕 g) = ⇑G := by
      simp only [G, SchwartzMap.fourier_coe]; rfl
    rw [e]; exact G.integrable
  have h := congrFun (hg.continuous.fourierInv_fourier_eq
    (hg.continuous.integrable_of_hasCompactSupport hc) hI) v
  rw [Real.fourierInv_eq] at h
  simpa only [Real.fourier_eq] using h

theorem haar_E {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {d : ℕ}
    (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∃ c : NNReal, c ≠ 0 ∧ ∀ h : EuclideanSpace ℝ (Fin d) → ℂ,
      ∫ x, h (e x) ∂μ = ((c : ℝ) : ℂ) * ∫ z, h z := by
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  set c := Measure.addHaarScalarFactor (μ.map e) volume with hc
  have hm : μ.map e = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨c, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', fun h => ?_⟩
  have key : ∫ x, h (e x) ∂μ = ∫ z, h z ∂(μ.map e) :=
    (e.toHomeomorph.measurableEmbedding.integral_map h).symm
  rw [key, hm, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem pair {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (hβ : ∀ y, (∀ x, β x y = 0) → y = 0) :
    ∃ T A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      ∀ x y, β x y = 2 * π * ⟪T x, A y⟫ := by
  let T : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let φ : V → StrongDual ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) := fun y =>
    (2 * π)⁻¹ • (β.flip y).comp (T.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)
  have φadd : ∀ y y', φ (y + y') = φ y + φ y' := by
    intro y y'; simp only [φ, map_add (f := _), ContinuousLinearMap.add_comp, smul_add]
  have φsmul : ∀ (r : ℝ) y, φ (r • y) = r • φ y := by
    intro r y; simp only [φ, map_smul, ContinuousLinearMap.smul_comp, smul_comm r]
  let L : V →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    { toFun := fun y => (InnerProductSpace.toDual ℝ _).symm (φ y)
      map_add' := fun y y' => by simp only [φadd, map_add (f := _)]
      map_smul' := fun r y => by
        simp only [φsmul, LinearIsometryEquiv.map_smulₛₗ, RingHom.id_apply, RCLike.conj_to_real] }
  have hL : ∀ x y, ⟪T x, L y⟫ = (2 * π)⁻¹ * β x y := by
    intro x y
    rw [real_inner_comm]
    change ⟪(InnerProductSpace.toDual ℝ _).symm (φ y), T x⟫ = _
    rw [InnerProductSpace.toDual_symm_apply]
    simp [φ]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hβ
    intro x
    have h1 := hL x y
    rw [hy, inner_zero_right] at h1
    have hp : (2 * π)⁻¹ ≠ 0 := by positivity
    exact (mul_eq_zero.mp h1.symm).resolve_left hp
  let A := (L.linearEquivOfInjective hinj finrank_euclideanSpace_fin.symm).toContinuousLinearEquiv
  refine ⟨T, A, fun x y => ?_⟩
  have hA : A y = L y := rfl
  rw [hA, hL]
  field_simp

end HaarPairing

theorem haar_measure_pairing : S5 := by
  intro V _ _ _ _ _ μ _ β hβ
  obtain ⟨T, A, hTA⟩ := HaarPairing.pair β hβ
  obtain ⟨c1, hc1, h1⟩ := HaarPairing.haar_E μ T
  obtain ⟨c2, hc2, h2⟩ := HaarPairing.haar_E μ A
  refine ⟨((c1 : ℝ) : ℂ) * ((c2 : ℝ) : ℂ), mul_ne_zero (by exact_mod_cast hc1) (by exact_mod_cast hc2),
    fun f hf hc ξ => ?_⟩
  set g : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ := f ∘ T.symm with hg_def
  have hgs : ContDiff ℝ ∞ g := hf.comp T.symm.contDiff
  have hgc : HasCompactSupport g := hc.comp_homeomorph T.symm.toHomeomorph
  have hFT : ∀ y, FT μ β f y = ((c1 : ℝ) : ℂ) *
      ∫ z, Real.fourierChar (-inner ℝ z (A y)) • g z := by
    intro y
    rw [FT, ← h1 (fun z => Real.fourierChar (-inner ℝ z (A y)) • g z)]
    congr 1 with x
    simp only [g, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, Circle.smul_def,
      Real.fourierChar_apply, smul_eq_mul, hTA]
    push_cast
    ring_nf
  have step : ∫ y, Complex.exp ((β ξ y : ℝ) * Complex.I) * FT μ β f y ∂μ =
      ((c1 : ℝ) : ℂ) * ∫ y, Real.fourierChar (inner ℝ (A y) (T ξ)) •
        (∫ z, Real.fourierChar (-inner ℝ z (A y)) • g z) ∂μ := by
    rw [← integral_const_mul]
    congr 1 with y
    simp only [hFT, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hTA, real_inner_comm (A y)]
    push_cast
    ring_nf
  have h2' := h2 (fun w => Real.fourierChar (inner ℝ w (T ξ)) •
    ∫ z, Real.fourierChar (-inner ℝ z w) • g z)
  rw [step, h2', HaarPairing.inv_E g hgs hgc]
  simp only [g, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  ring

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.LieAlgebraAction
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace LieAlgebraAction

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def lmL (A : LieI ι a) : LieI ι a →ₗ[ℝ] LieI ι a where
  toFun Z := Matrix.of.symm (Matrix.of A * Matrix.of Z)
  map_add' x y := by
    change Matrix.of.symm (Matrix.of A * (Matrix.of x + Matrix.of y)) = _
    rw [Matrix.mul_add]; rfl
  map_smul' c x := by
    change Matrix.of.symm (Matrix.of A * (c • Matrix.of x)) = _
    rw [Matrix.mul_smul]; rfl

def lmC : LieI ι a →ₗ[ℝ] (LieI ι a →L[ℝ] LieI ι a) where
  toFun A := LinearMap.toContinuousLinearMap (lmL A)
  map_add' A B := by
    ext1 Z
    change Matrix.of.symm ((Matrix.of A + Matrix.of B) * Matrix.of Z) = _
    rw [Matrix.add_mul]; rfl
  map_smul' c A := by
    ext1 Z
    change Matrix.of.symm ((c • Matrix.of A) * Matrix.of Z) = _
    rw [Matrix.smul_mul]; rfl

def lm : LieI ι a →L[ℝ] (LieI ι a →L[ℝ] LieI ι a) := LinearMap.toContinuousLinearMap lmC

theorem isOpen_U : IsOpen {M : LieI ι a | IsUnit (Matrix.of M)} := by
  have : {M : LieI ι a | IsUnit (Matrix.of M)} = (fun M : LieI ι a => (Matrix.of M).det) ⁻¹' {u | IsUnit u} := by
    ext M; exact Matrix.isUnit_iff_isUnit_det _
  rw [this]
  refine Units.isOpen.preimage (Continuous.matrix_det ?_)
  exact continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i)

def invL (M : LieI ι a) : LieI ι a := Matrix.of.symm (Matrix.of M)⁻¹

theorem lm_inv_mul {M : LieI ι a} (hM : IsUnit (Matrix.of M)) (Z : LieI ι a) : lm (invL M) (lm M Z) = Z := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hM
  change Matrix.of.symm ((Matrix.of M)⁻¹ * (Matrix.of M * Matrix.of Z)) = Z
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd]; rfl

theorem lm_mul_inv {M : LieI ι a} (hM : IsUnit (Matrix.of M)) (Z : LieI ι a) : lm M (lm (invL M) Z) = Z := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hM
  change Matrix.of.symm (Matrix.of M * ((Matrix.of M)⁻¹ * Matrix.of Z)) = Z
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hd]; rfl

theorem isUnit_lm {M : LieI ι a} (hM : IsUnit (Matrix.of M)) : IsUnit (lm M) :=
  ⟨⟨lm M, lm (invL M), ContinuousLinearMap.ext fun Z => lm_mul_inv hM Z,
    ContinuousLinearMap.ext fun Z => lm_inv_mul hM Z⟩, rfl⟩

theorem inverse_lm {M : LieI ι a} (hM : IsUnit (Matrix.of M)) : Ring.inverse (lm M) = lm (invL M) := by
  have : (⟨lm M, lm (invL M), ContinuousLinearMap.ext fun Z => lm_mul_inv hM Z,
    ContinuousLinearMap.ext fun Z => lm_inv_mul hM Z⟩ : (LieI ι a →L[ℝ] LieI ι a)ˣ) = (isUnit_lm hM).unit :=
    Units.ext rfl
  have h2 := Ring.inverse_unit (isUnit_lm hM).unit
  rw [← this] at h2
  exact h2

omit [Fintype ι] in
theorem orb_unit (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (v : X) {M : LieI ι a} (hM : IsUnit (Matrix.of M)) :
    orb ρ v M = ρ hM.unit v := by
  unfold orb; rw [dite_eq_left hM]

omit [Fintype ι] in
theorem orb_mul (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (v : X) (g : GL (Fin a) (ι → ℂ)) (M : LieI ι a) :
    orb ρ v (Matrix.of.symm (g.val * Matrix.of M)) = ρ g (orb ρ v M) := by
  by_cases hM : IsUnit (Matrix.of M)
  · have h' : IsUnit (Matrix.of (Matrix.of.symm (g.val * Matrix.of M))) := by
      change IsUnit (g.val * Matrix.of M); exact g.isUnit.mul hM
    rw [orb_unit ρ v h', orb_unit ρ v hM]
    have : h'.unit = g * hM.unit := Units.ext rfl
    rw [this, map_mul]; rfl
  · have h' : ¬ IsUnit (Matrix.of (Matrix.of.symm (g.val * Matrix.of M))) := by
      intro h
      apply hM
      have e : Matrix.of M = (g⁻¹).val * (g.val * Matrix.of M) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      rw [e]; exact (g⁻¹).isUnit.mul h
    unfold orb; rw [dite_eq_right hM, dite_eq_right h', map_zero]

theorem hasFDerivAt_orb (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) {v : X} {D : LieI ι a →L[ℝ] X}
    (hD : HasFDerivAt (orb ρ v) D (oneI ι a)) {M : LieI ι a} (hM : IsUnit (Matrix.of M)) :
    HasFDerivAt (orb ρ v) ((((ρ hM.unit).restrictScalars ℝ).comp D).comp (Ring.inverse (lm M))) M := by
  rw [inverse_lm hM]
  have h1 : lm (invL M) M = oneI ι a := by
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp hM
    change Matrix.of.symm ((Matrix.of M)⁻¹ * Matrix.of M) = Matrix.of.symm 1
    rw [Matrix.nonsing_inv_mul _ hd]
  have hD' : HasFDerivAt (orb ρ v) D (lm (invL M) M) := by rw [h1]; exact hD
  have hc := (((ρ hM.unit).restrictScalars ℝ).hasFDerivAt).comp M (hD'.comp M (lm (invL M)).hasFDerivAt)
  refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun Z => ?_)
  change orb ρ v Z = ρ hM.unit (orb ρ v (lm (invL M) Z))
  rw [← orb_mul]
  congr 1
  exact (lm_mul_inv hM Z).symm

theorem fderiv_orb (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) {v : X} {D : LieI ι a →L[ℝ] X}
    (hD : HasFDerivAt (orb ρ v) D (oneI ι a)) {M : LieI ι a} (hM : IsUnit (Matrix.of M))
    {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ (LieI ι a)) :
    fderiv ℝ (orb ρ v) M = ∑ i, ((LinearMap.toContinuousLinearMap (b.coord i)).comp
      (Ring.inverse (lm M))).smulRight (orb ρ (D (b i)) M) := by
  rw [(hasFDerivAt_orb ρ hD hM).fderiv]
  ext1 Z
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← b.sum_repr (Ring.inverse (lm M) Z)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, orb_unit ρ _ hM]
  rfl

end LieAlgebraAction

open LieAlgebraAction in
theorem lie_algebra_action_exists : S1 := by
  intro ι _ a X _ _ _ ρ _ 𝒮 hS
  choose D hD hDS using hS
  let b := Module.finBasis ℝ (LieI ι a)
  have key : ∀ N : ℕ, ∀ v (hv : v ∈ 𝒮), ContDiffOn ℝ N (orb ρ v) {M | IsUnit (Matrix.of M)} := by
    intro N
    induction N with
    | zero =>
      intro v hv
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun M hM => (hasFDerivAt_orb ρ (hD v hv) hM).continuousAt.continuousWithinAt
    | succ N ih =>
      intro v hv
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_U]
      refine ⟨fun M hM => (hasFDerivAt_orb ρ (hD v hv) hM).differentiableAt.differentiableWithinAt,
        fun h => by simp at h, ?_⟩
      have hR : ContDiffOn ℝ N (fun M : LieI ι a => Ring.inverse (lm M)) {M | IsUnit (Matrix.of M)} := by
        intro M hM
        obtain ⟨u, hu⟩ := isUnit_lm hM
        have h1 : ContDiffAt ℝ N Ring.inverse (u : LieI ι a →L[ℝ] LieI ι a) := contDiffAt_ringInverse (𝕜 := ℝ) u
        rw [hu] at h1
        exact (h1.comp M ((lm (ι := ι) (a := a)).contDiff.contDiffAt)).contDiffWithinAt
      have hsum : ContDiffOn ℝ N (fun M : LieI ι a => ∑ i, ((LinearMap.toContinuousLinearMap (b.coord i)).comp
          (Ring.inverse (lm M))).smulRight (orb ρ (D v hv (b i)) M)) {M | IsUnit (Matrix.of M)} :=
        ContDiffOn.sum fun i _ =>
          ((contDiffOn_const (c := LinearMap.toContinuousLinearMap (b.coord i))).clm_comp hR).smulRight
            (ih _ (hDS v hv (b i)))
      exact hsum.congr fun M hM => fderiv_orb ρ (hD v hv) hM b
  intro v hv
  exact contDiffOn_infty.mpr fun N => key N v hv

end PositivityTheory.jumpWindows

end
end

