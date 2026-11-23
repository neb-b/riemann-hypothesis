module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import GroundTheory.GlobalFields.TateThesis.GlobalZeta
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.WhittakerHecke.SummableTsumInvOneAddHeightPowLe
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0013
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0011
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.LintegralIdeleRatPolyDecayMulNormRpowLtTop
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem mult_eq_one (w : InfinitePlace ℚ) : w.mult = 1 := by
  simp [InfinitePlace.mult, IsTotallyReal.isReal w]

private theorem lint_real (w : InfinitePlace ℚ) {s : ℝ} (hs : 1 < s) :
    ∫⁻ z, ENNReal.ofReal ((1 + ‖z‖) ^ (-s)) ∂infinitePlaceMeasure w < ∞ := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  have hm : Measurable fun z : w.Completion ↦ ENNReal.ofReal ((1 + ‖z‖) ^ (-s)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_const.add continuous_norm).rpow_const fun z ↦
        Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg z)).ne').measurable
  rw [infinitePlaceMeasure_of_isReal hw,
    lintegral_map hm (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.measurable]
  have h : ∀ y : ℝ, ‖(InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm y‖ = ‖y‖ := fun y ↦ by
    rw [← norm_isometryEquivRealOfIsReal hw, IsometryEquiv.apply_symm_apply]
  simp_rw [h]
  exact finite_integral_one_add_norm (by simpa using hs)

private theorem int_place (w : InfinitePlace ℚ) {x : ℝ} (h1 : 1 < x) {r : ℕ} (hr : x < r) :
    Integrable (fun z : (w.Completion)ˣ ↦ ‖(z : w.Completion)‖ ^ x / (1 + ‖(z : w.Completion)‖) ^ r)
      (infinitePlaceUnitsMeasure w) := by
  have hG : Continuous fun z : w.Completion ↦ ‖z‖ ^ x / (1 + ‖z‖) ^ r :=
    (continuous_norm.rpow_const fun _ ↦ Or.inr (by linarith)).div
      ((continuous_const.add continuous_norm).pow r) fun _ ↦ by positivity
  refine ⟨(hG.comp Units.continuous_val).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z ↦ by positivity)]
  refine (lintegral_unitsMeasure_le (infinitePlaceMeasure w) w.mult
    (g := fun z ↦ ENNReal.ofReal (‖z‖ ^ x / (1 + ‖z‖) ^ r))
    (ENNReal.measurable_ofReal.comp hG.measurable)).trans_lt ?_
  refine lt_of_le_of_lt (lintegral_mono fun z ↦ ?_) (lint_real w (s := r - x + 1) (by linarith))
  rw [← ENNReal.ofReal_mul (by positivity), mult_eq_one, pow_one]
  refine ENNReal.ofReal_le_ofReal ?_
  set t := ‖z‖
  have ht : 0 ≤ t := norm_nonneg _
  have ha : 1 ≤ 1 + t := by linarith
  have hapos : 0 < 1 + t := by linarith
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith), zero_div, mul_zero]
    positivity
  · have e1 : t⁻¹ * (t ^ x / (1 + t) ^ r) = t ^ (x - 1) * ((1 + t) ^ (r : ℝ))⁻¹ := by
      rw [← Real.rpow_natCast (1 + t) r, Real.rpow_sub hpos, Real.rpow_one, div_eq_mul_inv,
        div_eq_mul_inv]
      ring
    have e2 : (1 + t) ^ (-((r : ℝ) - x + 1)) = (1 + t) ^ (x - 1) * ((1 + t) ^ (r : ℝ))⁻¹ := by
      rw [← Real.rpow_neg hapos.le, ← Real.rpow_add hapos]
      congr 1
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow ht (by linarith) (by linarith)) (by positivity)

private noncomputable def hInf (x : ℝ) (r : ℕ) (a : (InfiniteAdeleRing ℚ)ˣ) : ℝ :=
  ∏ w : InfinitePlace ℚ, ‖(a : InfiniteAdeleRing ℚ) w‖ ^ x / (1 + ‖(a : InfiniteAdeleRing ℚ) w‖) ^ r

private theorem int_hInf {x : ℝ} (h1 : 1 < x) {r : ℕ} (hr : x < r) :
    Integrable (hInf x r) (infiniteIdeleMeasure ℚ) := by
  have h := Integrable.fintype_prod_dep (𝕜 := ℝ)
    (f := fun (w : InfinitePlace ℚ) (z : (w.Completion)ˣ) ↦
      ‖(z : w.Completion)‖ ^ x / (1 + ‖(z : w.Completion)‖) ^ r)
    (μ := fun w ↦ infinitePlaceUnitsMeasure w) fun w ↦ int_place w h1 hr
  rw [infiniteIdeleMeasure]
  refine (integrable_map_equiv (infiniteUnitsEquiv ℚ).symm.toHomeomorph.toMeasurableEquiv _).2 ?_
  exact h

private theorem abs_re (y : IdeleGroup ℚ) :
    |re (y : A ℚ)| = ‖((IdeleGroup.toInfinite ℚ y : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) Rat.infinitePlace‖ := by
  have hw : (Rat.infinitePlace).IsReal := IsTotallyReal.isReal _
  have e : re (y : A ℚ) = InfinitePlace.Completion.isometryEquivRealOfIsReal hw
      (((IdeleGroup.toInfinite ℚ y : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) Rat.infinitePlace) := rfl
  rw [e, ← Real.norm_eq_abs, norm_isometryEquivRealOfIsReal]

theorem UpperTheory.lintegral_idele_rat_polyDecay_mul_norm_rpow_lt_top :
    ∀ (K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)), IsCompact K → ∀ x : ℝ, 1 < x → ∀ r : ℕ, x < r →
        ∫⁻ y : IdeleGroup ℚ, (if (y : A ℚ).2 ∈ K then ENNReal.ofReal (((1 + |re (y : A ℚ)|) ^ r)⁻¹ * ab y ^ x) else 0) ∂(ideleMeasure ℚ) < ⊤ := by
  intro K hK x hx r hr
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles hK
  have hG : Integrable (fun y : IdeleGroup ℚ ↦
      hInf x r (IdeleGroup.toInfinite ℚ y) * finiteZetaBound L x (IdeleGroup.toFinite ℚ y))
      (ideleMeasure ℚ) := by
    have h := (int_hInf hx hr).mul_prod (integrable_finiteZetaBound L hx)
    exact ((measurePreserving_prodEquiv ℚ).integrable_comp_emb
      (IdeleGroup.prodEquiv ℚ).toHomeomorph.measurableEmbedding).2 h
  refine lt_of_le_of_lt (lintegral_mono fun y ↦ ?_) hG.lintegral_lt_top
  split_ifs with hy
  · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hb : ((IdeleGroup.toFinite ℚ y : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ idealFiniteAdeles L :=
      hL hy
    rw [finiteZetaBound, if_pos hb, hInf, ab, ideleModule_rpow_eq, abs_re,
      Fintype.prod_subsingleton _ Rat.infinitePlace, Fintype.prod_subsingleton _ Rat.infinitePlace,
      mult_eq_one]
    simp only [Nat.cast_one, one_mul]
    rw [div_eq_mul_inv]
    ring_nf
  · exact zero_le
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.LseriesTwistedCoeffEqTsumCoprimeOfSummable
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.lseries_twisted_coeff_eq_tsum_coprime_of_summable :
    ∀ (N : ℕ) (χ : HChar ℚ) (μ : ℕ → ℂ) (s : ℂ),
        Summable (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s)) →
        LSeriesSummable (bN N χ μ) s ∧
          LSeries (bN N χ μ) s = ∑' n : {n : ℕ // 0 < n ∧ n.Coprime N}, μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) := by
  intro N χ μ s hS
  have hterm : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, LSeries.term (bN N χ μ) s (n : ℕ) =
      μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) := by
    rintro ⟨n, hn, hc⟩
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [LSeries.term_of_ne_zero hn.ne']
    simp only [bN, if_pos hc]
    rw [Complex.cpow_sub _ _ hn0, Complex.cpow_one]
    ring
  have hzero : ∀ x ∉ Set.range (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ),
      LSeries.term (bN N χ μ) s x = 0 := by
    intro x hx
    by_cases h0 : x = 0
    · rw [h0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero h0]
      have hc : ¬ x.Coprime N := fun hc => hx ⟨⟨x, Nat.pos_of_ne_zero h0, hc⟩, rfl⟩
      simp only [bN, if_neg hc, zero_div]
  have heq : (LSeries.term (bN N χ μ) s) ∘ (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ) =
      fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) :=
    funext hterm
  refine ⟨(Subtype.val_injective.summable_iff hzero).1 (heq ▸ hS), ?_⟩
  have hsupp : Function.support (LSeries.term (bN N χ μ) s) ⊆
      Set.range (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ) := by
    intro x hx
    by_contra h
    exact hx (hzero x h)
  rw [LSeries, ← Subtype.val_injective.tsum_eq hsupp]
  exact tsum_congr hterm
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.MaximalCompactMeasureMapConjDiagEq
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private lemma inv_mem_UU' {t : (A ℚ)ˣ} (ht : t ∈ UU) : t⁻¹ ∈ UU := by
  refine ⟨?_, fun v => ?_⟩
  · have h : (t : A ℚ).1 * ((t⁻¹ : (A ℚ)ˣ) : A ℚ).1 = 1 := congrArg Prod.fst (Units.mul_inv t)
    rw [ht.1, one_mul] at h
    exact h
  · have hm : H.cp v (t : A ℚ) * H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have := congrArg Valued.v hm
    rwa [map_mul, ht.2 v, one_mul, map_one] at this

private lemma cD_mem_KK {t : (A ℚ)ˣ} (ht : t ∈ UU) {k : G1 ℚ} (hk : k ∈ KK ℚ) : cD t k ∈ KK ℚ := by
  have hi := inv_mem_UU' ht
  have fm : ∀ a b : A ℚ, (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  have fa : ∀ a b : A ℚ, (a + b).1 = a.1 + b.1 := fun _ _ => rfl
  have c00 : (cD t k) 0 0 = k 0 0 := rfl
  have c01 : (cD t k) 0 1 = k 0 1 * ((t⁻¹ : (A ℚ)ˣ) : A ℚ) := rfl
  have c10 : (cD t k) 1 0 = (t : A ℚ) * k 1 0 := rfl
  have c11 : (cD t k) 1 1 = k 1 1 := rfl
  have e1 : ∀ i j, ((cD t k) i j).1 = (k i j).1 := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact congrArg Prod.fst c00
    · show ((cD t k) 0 1).1 = (k 0 1).1
      rw [c01, fm, hi.1, mul_one]
    · show ((cD t k) 1 0).1 = (k 1 0).1
      rw [c10, fm, ht.1, one_mul]
    · exact congrArg Prod.fst c11
  refine ⟨fun i j => ?_, fun v i j => ?_⟩
  · have h := hk.1 i j
    rw [← h]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    have e3 : ∀ a b c d a' b' c' d' : A ℚ, a.1 = a'.1 → b.1 = b'.1 → c.1 = c'.1 → d.1 = d'.1 →
        (a * b + c * d).1 = (a' * b' + c' * d').1 := by
      intro a b c d a' b' c' d' h1 h2 h3 h4
      rw [fa, fa, fm, fm, fm, fm, h1, h2, h3, h4]
    exact e3 _ _ _ _ _ _ _ _ (e1 _ _) (e1 _ _) (e1 _ _) (e1 _ _)
  · have ti : ((t : A ℚ)).2 v ∈ v.adicCompletionIntegers ℚ := (ht.2 v).le
    have tj : (((t⁻¹ : (A ℚ)ˣ) : A ℚ)).2 v ∈ v.adicCompletionIntegers ℚ := (hi.2 v).le
    fin_cases i <;> fin_cases j
    · exact hk.2 v 0 0
    · show ((cD t k) 0 1).2 v ∈ v.adicCompletionIntegers ℚ
      rw [c01]
      exact mul_mem (hk.2 v 0 1) tj
    · show ((cD t k) 1 0).2 v ∈ v.adicCompletionIntegers ℚ
      rw [c10]
      exact mul_mem ti (hk.2 v 1 0)
    · exact hk.2 v 1 1

theorem UpperTheory.maximalCompact_measure_map_conjDiag_eq :
    ∀ (M₀ : Meas ℚ) (t : IdeleGroup ℚ), t ∈ UU → M₀.κ.map (cD t) = M₀.κ := by
  intro m t ht
  haveI := m.prob
  have hm : Measurable (cD t : G1 ℚ → G1 ℚ) := (M.continuous_cD t).measurable
  have hae : ∀ᵐ y ∂m.κ, y ∈ KK ℚ := by
    rw [ae_iff]
    exact m.supp
  have right : ∀ f : G1 ℚ → ℝ≥0∞, Measurable f → ∀ k ∈ KK ℚ, ∫⁻ x, f (x * k) ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    intro f hf k hk
    conv_rhs => rw [← m.κ_right k hk]
    rw [lintegral_map hf (measurable_mul_const k)]
  have left : ∀ f : G1 ℚ → ℝ≥0∞, Measurable f → ∀ k ∈ KK ℚ, ∫⁻ x, f (k * x) ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    intro f hf k hk
    conv_rhs => rw [← m.κ_left k hk]
    rw [lintegral_map hf (measurable_const_mul k)]
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf hm]
  have hF : Measurable (fun p : G1 ℚ × G1 ℚ => f (p.1 * cD t p.2)) :=
    hf.comp (measurable_fst.mul (hm.comp measurable_snd))
  have hA : ∫⁻ y, ∫⁻ x, f (x * cD t y) ∂m.κ ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    have h : ∀ᵐ y ∂m.κ, ∫⁻ x, f (x * cD t y) ∂m.κ = ∫⁻ x, f x ∂m.κ :=
      hae.mono fun y hy => right f hf _ (cD_mem_KK ht hy)
    rw [lintegral_congr_ae h, lintegral_const, measure_univ, mul_one]
  have hB : ∫⁻ x, ∫⁻ y, f (x * cD t y) ∂m.κ ∂m.κ = ∫⁻ y, f (cD t y) ∂m.κ := by
    have h : ∀ᵐ x ∂m.κ, ∫⁻ y, f (x * cD t y) ∂m.κ = ∫⁻ y, f (cD t y) ∂m.κ := by
      refine hae.mono fun x hx => ?_
      have hk : cD t⁻¹ x ∈ KK ℚ := cD_mem_KK (inv_mem_UU' ht) hx
      have ex : x = cD t (cD t⁻¹ x) := by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      have e : ∀ y, f (x * cD t y) = (f ∘ cD t) (cD t⁻¹ x * y) := by
        intro y
        rw [Function.comp_apply, M.cD_mul, ← ex]
      simp only [e]
      exact left (f ∘ cD t) (hf.comp hm) _ hk
    rw [lintegral_congr_ae h, lintegral_const, measure_univ, mul_one]
  rw [← hB, ← hA]
  exact lintegral_lintegral_swap hF.aemeasurable
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.NormThetaSeriesSiegelSetLeExp
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

namespace UpperTheory.QuaternionSwap

private noncomputable def Yv (b : A ℚ) (a : (A ℚ)ˣ) (ξ : Fin 2 → ℚ) : Fin 2 → A ℚ :=
  ![rt (ξ 0) * (a : A ℚ), (rt (ξ 0) * b + rt (ξ 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)]

private theorem row_eq (b : A ℚ) (a : (A ℚ)ˣ) (k : GL (Fin 2) (A ℚ)) (ξ : Fin 2 → ℚ) :
    (fun i => rt (ξ i)) ᵥ* (gl (nU b * mD a) * k).val = Yv b a ξ ᵥ* k.val := by
  have h1 : (gl (nU b * mD a) * k).val = (nU b * mD a).val * k.val := rfl
  rw [h1, ← Matrix.vecMul_vecMul]
  congr 1
  have h2 : (nU b * mD a).val = !![1, b; 0, 1] * !![(a : A ℚ), 0; 0, ((a⁻¹ : (A ℚ)ˣ) : A ℚ)] := rfl
  rw [h2]
  funext j
  fin_cases j <;> simp [Yv, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply] <;> ring

private def swapQ (q : ℚ) (hq : q ≠ 0) : Rw ℚ ≃ Rw ℚ where
  toFun ξ := ⟨![q * ξ.1 0, q⁻¹ * ξ.1 1], fun h => ξ.2 (by
    funext i
    fin_cases i
    · have := congrFun h 0
      simpa [hq] using this
    · have := congrFun h 1
      simpa [hq] using this)⟩
  invFun ξ := ⟨![q⁻¹ * ξ.1 0, q * ξ.1 1], fun h => ξ.2 (by
    funext i
    fin_cases i
    · have := congrFun h 0
      simpa [hq] using this
    · have := congrFun h 1
      simpa [hq] using this)⟩
  left_inv ξ := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [hq]
  right_inv ξ := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [hq]

private theorem Yv_swap (q : ℚ) (hq : q ≠ 0) (b : A ℚ) (a a' : (A ℚ)ˣ) (ha : (a' : A ℚ) = rt q * (a : A ℚ))
    (ξ : Rw ℚ) : Yv b a (swapQ q hq ξ).1 = Yv (rt (q ^ 2) * b) a' ξ.1 := by
  have hqq : rt q * rt q⁻¹ = (1 : A ℚ) := by
    rw [← map_mul, mul_inv_cancel₀ hq, map_one]
  have hinv : ((a'⁻¹ : (A ℚ)ˣ) : A ℚ) = rt q⁻¹ * ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [ha]
    calc rt q * (a : A ℚ) * (rt q⁻¹ * ((a⁻¹ : (A ℚ)ˣ) : A ℚ))
        = (rt q * rt q⁻¹) * ((a : A ℚ) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)) := by ring
      _ = 1 := by rw [hqq, Units.mul_inv, one_mul]
  have rm : ∀ x y : ℚ, rt (x * y) = rt x * rt y := fun x y => map_mul (algebraMap ℚ (A ℚ)) x y
  funext j
  fin_cases j
  · change rt (q * ξ.1 0) * (a : A ℚ) = rt (ξ.1 0) * (a' : A ℚ)
    rw [ha, rm]
    ring
  · change (rt (q * ξ.1 0) * b + rt (q⁻¹ * ξ.1 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ) =
      (rt (ξ.1 0) * (rt (q ^ 2) * b) + rt (ξ.1 1)) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ)
    have e2 : rt (q ^ 2) = rt q * rt q := by rw [pow_two, rm]
    rw [hinv, rm, rm, e2]
    have e : rt q = rt q * rt q * rt q⁻¹ := by rw [mul_assoc, hqq, mul_one]
    calc (rt q * rt (ξ.1 0) * b + rt q⁻¹ * rt (ξ.1 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)
        = ((rt q * rt q * rt q⁻¹) * rt (ξ.1 0) * b + rt q⁻¹ * rt (ξ.1 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by rw [← e]
      _ = _ := by ring

private theorem re_mul (x y : A ℚ) : re (x * y) = re x * re y := by
  simp [re, map_mul]
private theorem re_add (x y : A ℚ) : re (x + y) = re x + re y := by
  simp [re, map_add (f := _)]
private theorem re_rat (q : ℚ) : re (rt q) = (q : ℝ) := by
  exact eq_ratCast (((Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) Rat.infinitePlace).comp
    (TR.pInf ℚ)).comp (algebraMap ℚ (A ℚ))) q
private theorem re_inv (a : (A ℚ)ˣ) : re ((a⁻¹ : (A ℚ)ˣ) : A ℚ) = (re (a : A ℚ))⁻¹ := by
  have h : re (a : A ℚ) * re ((a⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
    rw [← re_mul, Units.mul_inv]
    simp [re]
  exact eq_inv_of_mul_eq_one_right h

end UpperTheory.QuaternionSwap

open UpperTheory.QuaternionSwap in
theorem UpperTheory.norm_thetaSeries_siegelSet_le_exp :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2) → ∀ (C : Set (GL (Fin 2) (A ℚ))), IsCompact C → ∀ (c : ℝ), 0 < c → ∀ n : ℕ,
        ∃ (r : ℕ) (B : ℝ), ∀ t : ℝ, 0 ≤ t → ∀ (b : A ℚ) (a : (A ℚ)ˣ), ∀ k ∈ C, c ≤ ab a →
          ‖ThR Φ t (gl (nU b * mD a) * k)‖ ≤ B * Real.exp (-((n : ℝ) * t)) * ab a ^ r := by
  intro Φ hΦ C hC c hc n
  obtain ⟨B0, κ, L, hB0, hκ, hκ1, hL, hmaj⟩ := UpperTheory.schwartzBruhat_translate_decay_bound Φ hΦ C hC (n + 4)
  obtain ⟨S, Bu, hS, hBu, hred⟩ := UpperTheory.exists_rat_mul_idele_finitePart_mem_compact_of_le_norm c hc
  obtain ⟨d, hd, hden⟩ := UpperTheory.exists_common_denom_of_isCompact_unipotent_translates L hL S hS
  obtain ⟨B1, hB1, hsum⟩ := UpperTheory.summable_tsum_inv_one_add_height_pow_le n d κ Bu hd hκ hκ1 hBu
  refine ⟨n + 2, B0 * B1 * (Bu / c) ^ (n + 2), fun t ht b a k hk hca => ?_⟩
  obtain ⟨q, a', u, hq, ha', hu, hf, hfi, hlo, hhi⟩ := hred a hca
  set b' : A ℚ := rt (q ^ 2) * b with hb'
  set α : ℝ := |re (a' : A ℚ)| with hα
  set β : ℝ := re b' with hβ
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.2 (by linarith)) hlo
  have hab : 0 < ab a := lt_of_lt_of_le hc hca
  set T : ℝ := Bu * (ab a / c) with hT
  have hT1 : 1 ≤ T := by
    have : 1 ≤ ab a / c := (one_le_div hc).2 hca
    nlinarith
  let R : Set (Rw ℚ) := {ξ | (fun j => (Yv b' a' ξ.1 j).2) ∈ L}
  let Wt : Rw ℚ → ℝ := fun ξ =>
    ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹
  have hfin : ∀ ξ : Fin 2 → ℚ, (fun j => (Yv b' a' ξ j).2) =
      ![algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2,
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b'.2 + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) *
          ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2] := by
    intro ξ
    funext j
    fin_cases j
    · change (rt (ξ 0)).2 * (a' : A ℚ).2 = _
      rw [hf]
      rfl
    · change ((rt (ξ 0)).2 * b'.2 + (rt (ξ 1)).2) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ).2 = _
      rw [hfi]
      rfl
  have hR : ∀ ξ ∈ R, ∀ ξ' ∈ R, _ := fun ξ h ξ' h' =>
    hden u hu b'.2 ξ.1 ξ'.1 (by have := h; simp only [R, Set.mem_setOf_eq, hfin] at this; exact this)
      (by have := h'; simp only [R, Set.mem_setOf_eq, hfin] at this; exact this)
  obtain ⟨hs, hle⟩ := hsum R β α T t ht hlo hhi hT1 (fun ξ h => (hR ξ h ξ h).1) (fun ξ h => (hR ξ h ξ h).2.1)
    (fun ξ h ξ' h' => (hR ξ h ξ' h').2.2)
  have hterm : ∀ ξ : Rw ℚ, ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖ ≤ B0 * R.indicator Wt ξ := by
    intro ξ
    obtain ⟨h1, h2⟩ := hmaj t k hk (Yv b' a' ξ.1)
    have e0 : |re (Yv b' a' ξ.1 0)| = |((ξ.1 0 : ℚ) : ℝ)| * α := by
      change |re (rt (ξ.1 0) * (a' : A ℚ))| = _
      rw [re_mul, re_rat, abs_mul]
    have e1 : |re (Yv b' a' ξ.1 1)| = |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α := by
      change |re ((rt (ξ.1 0) * b' + rt (ξ.1 1)) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ))| = _
      rw [re_mul, re_add, re_mul, re_rat, re_rat, re_inv, abs_mul, abs_inv, div_eq_mul_inv]
    by_cases hξ : ξ ∈ R
    · rw [Set.indicator_of_mem hξ]
      rw [e0, e1] at h1
      exact h1
    · rw [Set.indicator_of_notMem hξ, mul_zero]
      have h0 : (Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j) = 0 := by
        by_contra h
        exact hξ (h2 h)
      rw [h0, norm_zero]
  have hrew : ThR Φ t (gl (nU b * mD a) * k) =
      ∑' ξ : Rw ℚ, Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j := by
    unfold ThR
    rw [← (swapQ q hq).tsum_eq]
    refine tsum_congr fun ξ => ?_
    rw [row_eq, Yv_swap q hq b a a' ha' ξ]
  have hsn : Summable fun ξ : Rw ℚ => ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hs.mul_left B0)
  rw [hrew]
  calc ‖∑' ξ : Rw ℚ, Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖
      ≤ ∑' ξ : Rw ℚ, ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' ξ : Rw ℚ, B0 * R.indicator Wt ξ := hsn.tsum_le_tsum hterm (hs.mul_left _)
    _ = B0 * ∑' ξ : Rw ℚ, R.indicator Wt ξ := tsum_mul_left
    _ ≤ B0 * (B1 * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2)) := mul_le_mul_of_nonneg_left hle hB0
    _ = B0 * B1 * (Bu / c) ^ (n + 2) * Real.exp (-((n : ℝ) * t)) * ab a ^ (n + 2) := by
        have : T = Bu / c * ab a := by rw [hT]; ring
        rw [this, mul_pow]
        ring
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.PowerSeriesCompleteHomogeneousTwoMulEqOne
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem UpperTheory.geometric_power_series_inverse (x : ℂ) :
    (PowerSeries.mk fun k : ℕ => x ^ k) * (1 - PowerSeries.C x * PowerSeries.X) = 1 := by
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  cases n with
  | zero => simp
  | succ n =>
    rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
    simp [PowerSeries.coeff_one, pow_succ]

theorem UpperTheory.powerSeries_completeHomogeneous_two_mul_eq_one :
    ∀ x y : ℂ, (PowerSeries.mk fun k : ℕ => (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i))) * ((1 - PowerSeries.C x * PowerSeries.X) * (1 - PowerSeries.C y * PowerSeries.X)) = 1 := by
  intro x y
  have h : (PowerSeries.mk fun k : ℕ => (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i)))
      = (PowerSeries.mk fun k : ℕ => x ^ k) * (PowerSeries.mk fun k : ℕ => y ^ k) := by
    ext n
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp
  rw [h, mul_mul_mul_comm, UpperTheory.geometric_power_series_inverse, UpperTheory.geometric_power_series_inverse, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.StandardAddCharNegArchimedeanRat
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.standardAddChar_neg_archimedean_rat :
    ∀ x : ℝ, ψ (-(TR.sInf ℚ fun _ => x)) = Complex.exp (2 * Real.pi * Complex.I * x) := by
  intro x
  have hu : Nonempty (InfinitePlace ℚ) := inferInstance
  obtain ⟨w⟩ := hu
  have huniq : ∀ v : InfinitePlace ℚ, v = w := fun v => Subsingleton.elim v w
  have hreal : InfinitePlace.IsReal w := IsTotallyReal.isReal w
  have h : adelicChar ℚ (TR.sInf ℚ fun _ => x) = Real.fourierChar (-x) := by
    have e : TR.sInf ℚ (fun _ => x) = infiniteAdeleInl (TR.infEq ℚ fun _ => x) := rfl
    rw [e, adelicChar_infiniteAdeleInl, Fintype.prod_eq_single w (fun v hv => absurd (huniq v) hv)]
    rw [infiniteAdelicChar_apply_of_isReal hreal]
    have e2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal (TR.infEq ℚ (fun _ => x) w) = x :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal hreal).apply_symm_apply x
    rw [e2]
  have h2 : adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) = Real.fourierChar x := by
    rw [AddChar.map_neg_eq_inv, h, AddChar.map_neg_eq_inv, inv_inv]
  have h3 : ψ (-(TR.sInf ℚ fun _ => x)) = ((adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) : Circle) : ℂ) := rfl
  rw [h3, h2, Real.fourierChar_apply]
  congr 1
  push_cast
  ring
end

