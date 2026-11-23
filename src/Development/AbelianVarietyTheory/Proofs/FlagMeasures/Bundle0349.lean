module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorph
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberNormalFormEqGramProjection
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RadicalCoordinatesBoundedMajorantLengths
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0215
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramEqGramDetProjectionNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerSetEqRangeNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagUnipotentEqStabilizerTimesSection
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0337
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0107

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreGramNumberNullAndCutoffIntegralBound
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibNf

theorem card_UT (r : ℕ) : Fintype.card (UT r) = r * (r - 1) / 2 := by
  rw [Fintype.card_subtype, ← Nat.choose_two_right]
  have := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin r)))
  simpa using this

theorem vol_polydisc (ι : Type) [Fintype ι] {R : ℝ} (hR : 0 ≤ R) :
    volume {y : ι → ℂ | ∀ p, ‖y p‖ ≤ R} = ENNReal.ofReal ((Real.pi * R ^ 2) ^ Fintype.card ι) := by
  have h : {y : ι → ℂ | ∀ p, ‖y p‖ ≤ R} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R := by
    ext y; simp
  rw [h, volume_pi_pi]
  simp only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hR, mul_comm]
  congr 2
  rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

theorem vol_cube (r : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume {y : Fin r → ℝ | ∀ p, |y p| ≤ R} = ENNReal.ofReal ((2 * R) ^ r) := by
  have h : {y : Fin r → ℝ | ∀ p, |y p| ≤ R} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℝ) R := by
    ext y; simp
  rw [h, volume_pi_pi]
  simp only [Real.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

theorem sfinite_PPar (k r : ℕ) : SFinite (volume : Measure (PPar k r)) := by
  have : SFinite (volume : Measure (Fin r → Fin (k + 1) → ℂ)) := inferInstance
  have : SFinite (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))) := inferInstance
  infer_instance

theorem vol_PPar (k r : ℕ) (S : Set (Fin r → Fin (k + 1) → ℂ)) (T : Set (UT r → ℂ)) (U : Set (Fin r → ℝ)) :
    (volume : Measure (PPar k r)) (S ×ˢ (T ×ˢ U)) = volume S * (volume T * volume U) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]

theorem coords_upper {r : ℕ} (u : UT r → ℂ) : USplit.coords (upper u) = u := by
  funext p
  exact USplit.upper_of_lt u p.2

theorem measurable_coord (k r : ℕ) : Measurable fun q : (UT r → ℂ) × PPar k r =>
    (Matrix.of.symm (uEmb k r (upper q.1) * pOf k r q.2) : Mt k r) :=
  (show Continuous fun q : (UT r → ℂ) × PPar k r =>
    (Matrix.of.symm (uEmb k r (upper q.1) * pOf k r q.2) : Mt k r) from (NCoord.coord_homeo k r).2.1).measurable

theorem coord_mem (k r : ℕ) (u : UT r → ℂ) (q : PPar k r) : uEmb k r (upper u) * pOf k r q ∈ Nset k r := by
  have := (NCoord.coord_homeo k r).1.mapsTo (Set.mem_univ (u, q))
  simpa only using this

theorem coord_off_mem (k r : ℕ) (β : Fin r → ℕ) (y : UToff β → ℂ) (q : PPar k r) :
    uEmb k r (upperOff β y) * pOf k r q ∈ Nset k r := by
  unfold upperOff
  exact coord_mem k r _ q

theorem cut_le {k r : ℕ} {β : Fin r → ℕ} (φ : Mt k r → ℝ≥0∞) (hφ : SubCut (Nset k r) (lebR k r β) φ)
    (n : Mat k r) (hN : n ∈ Nset k r) :
    ∫⁻ x : UTin β → ℂ, φ (Matrix.of.symm (uEmb k r (upperIn β x) * n)) ≤ 1 := by
  have h1 := hφ.2 (Matrix.of.symm n) hN
  have hl : Measurable fun ρ : Mt k r => φ (lmulM (Matrix.of ρ) (Matrix.of.symm n : Mt k r)) :=
    hφ.1.comp (continuous_rmulM n).measurable
  have hi : Measurable fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r) := by
    have : Continuous fun x : UTin β → ℂ => uEmb k r (upperIn β x) := by
      unfold upperIn
      refine (NCoord.cont_uEmb k r).comp (continuous_pi fun p => ?_)
      split_ifs
      · exact continuous_apply _
      · exact continuous_const
    exact Continuous.measurable (γ := Mt k r) this
  unfold lebR at h1
  rw [lintegral_map hl hi] at h1
  exact h1

theorem lintegral_le {k r : ℕ} {β : Fin r → ℕ} (hβ : Monotone β) (φ : Mt k r → ℝ≥0∞)
    (hφ : SubCut (Nset k r) (lebR k r β) φ) (E : Set (Mt k r)) (hE : MeasurableSet E)
    (A : Set (UToff β → ℂ)) (B : Set (PPar k r))
    (h : ∀ x y q, (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q)) : Mt k r) ∈ E →
      y ∈ A ∧ q ∈ B) :
    ∫⁻ n, φ n * E.indicator 1 n ∂(lebN k r) ≤ volume A * volume B := by
  have hm : Measurable fun n => φ n * E.indicator 1 n := hφ.1.mul (measurable_one.indicator hE)
  have hF := measurable_coord k r
  have := sfinite_PPar k r
  unfold lebN
  rw [lintegral_map hm hF, Measure.volume_eq_prod]
  refine le_trans (lintegral_prod_symm' _ (hm.comp hF)).le ?_
  refine le_trans (lintegral_mono fun q => ?_) (lintegral_indicator_const_le B (volume A))
  have hc : Measurable fun U : Fin r → Fin r → ℂ => USplit.coords (Matrix.of U) :=
    measurable_pi_iff.2 fun p => (measurable_pi_apply p.1.2).comp (measurable_pi_apply p.1.1)
  have hs := (USplit.lebesgue_split r β hβ).2 _ ((hm.comp hF).comp (hc.prodMk (measurable_const (a := q))))
  simp only [Function.comp_apply, Equiv.apply_symm_apply, coords_upper] at hs
  have hp : ∀ x y, uEmb k r (upper (USplit.coords (upperIn β x * upperOff β y))) * pOf k r q =
      uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q) := by
    intro x y
    have : upper (USplit.coords (upperIn β x * upperOff β y)) = upperIn β x * upperOff β y :=
      USplit.upper_coords_mul _ _
    rw [this, UEmb.uEmb_mul, Matrix.mul_assoc]
  simp only [hp] at hs
  simp only [Function.comp_apply]
  rw [hs]
  have key : ∀ y, ∫⁻ x : UTin β → ℂ,
      φ (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q))) *
        E.indicator 1 (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q)) : Mt k r) ≤
      A.indicator (fun _ => B.indicator 1 q) y := by
    intro y
    by_cases hy : y ∈ A ∧ q ∈ B
    · rw [Set.indicator_of_mem hy.1, Set.indicator_of_mem hy.2]
      refine le_trans (lintegral_mono fun x => ?_) (cut_le φ hφ _ (coord_off_mem k r β y q))
      exact mul_le_of_le_one_right' (Set.indicator_le_self' (fun _ _ => zero_le) _)
    · refine le_trans (le_of_eq ?_) zero_le
      have : ∀ x : UTin β → ℂ, E.indicator (1 : Mt k r → ℝ≥0∞)
          (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q)) : Mt k r) = 0 :=
        fun x => Set.indicator_of_notMem (fun hx => hy (h x y q hx)) _
      simp only [this, mul_zero, lintegral_zero]
  refine le_trans (lintegral_mono key) (le_trans (lintegral_indicator_const_le A _) (le_of_eq ?_))
  by_cases hq : q ∈ B <;> simp [hq]

theorem arith {a b c d e f g : ℝ} (hpos : 0 ≤ e * f) (har : a * (b * c) * d ≤ g) :
    a * (d * e * f * (b * c)) ≤ g * e * f := by
  have := mul_le_mul_of_nonneg_right har hpos
  refine le_trans (le_of_eq ?_) (le_trans this (le_of_eq ?_)) <;> ring

theorem null_of {k r : ℕ} (Z : Set (Mt k r)) (hZ : MeasurableSet Z) (S : Set (Fin r → Fin (k + 1) → ℂ))
    (hS : volume S = 0)
    (h : ∀ u q, (Matrix.of.symm (uEmb k r (upper u) * pOf k r q) : Mt k r) ∈ Z → q.1 ∈ S) : lebN k r Z = 0 := by
  have := sfinite_PPar k r
  unfold lebN
  rw [Measure.map_apply (measurable_coord k r) hZ]
  refine measure_mono_null (t := Set.univ ×ˢ (S ×ˢ (Set.univ ×ˢ Set.univ))) (fun q hq => ?_) ?_
  · exact ⟨trivial, h q.1 q.2 hq, trivial, trivial⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod, vol_PPar, hS, zero_mul, mul_zero]

theorem mem_of_mul {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g₀ ρ x : Mat k r} {R₀ y : ℝ}
    (hz : inWb k r z) (hz' : inWb k r z') (hg : g₀ ∈ GG k r) (hρ : ρ ∈ Rset k r g₀) (hx0 : x ∈ GG k r)
    (hx : (Matrix.of.symm (ρ * x) : Mt k r) ∈ Eset k r z z' g₀ R₀ y) :
    Sg k r z' x ≤ R₀ ∧ Sg k r z (g₀ * x) ≤ R₀ ∧ y < Yv k r z z' g₀ x ∧ Yv k r z z' g₀ x ≤ 2 * y := by
  have hx' : Sg k r z' (ρ * x) ≤ R₀ ∧ Sg k r z (g₀ * (ρ * x)) ≤ R₀ ∧ y < Yv k r z z' g₀ (ρ * x) ∧
      Yv k r z z' g₀ (ρ * x) ≤ 2 * y := hx.2
  have h1 : (1 : Mat k r) ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))) :=
    ⟨(nSubgroup k r).1.1, one_mem _⟩
  have e1 := ((LInv.lengths_basic k r z' hz').1 _ hx0 _ (YInv.N_sub_S z' hρ.1) 1 h1).2
  have e2 := ((LInv.lengths_basic k r z hz).1 _ (YInv.mul_mem hg hx0) _ (YInv.N_sub_S z hρ.2) 1 h1).2
  have e3 := (YInv.yv_invariant k r z z' g₀ hz hz' hg _ hx0).2.2 _ hρ
  rw [Matrix.mul_one] at e1 e2
  rw [Matrix.mul_assoc _ g₀⁻¹, ← Matrix.mul_assoc g₀⁻¹, Matrix.nonsing_inv_mul _ (YInv.det_unit hg),
    Matrix.one_mul, Matrix.mul_assoc g₀] at e2
  rwa [e1, e2, e3] at hx'

theorem vol_bound {k r : ℕ} (β : Fin r → ℕ) {R₀ De y : ℝ} (hr : 1 ≤ r) (hR : 1 ≤ R₀) (h1De : 1 ≤ De) (hy : 0 < y)
    (S : Set (Fin r → Fin (k + 1) → ℂ))
    (hS : volume S ≤ ENNReal.ofReal ((Real.pi * (r * R₀ ^ (2 * r - 1) * De) ^ 2) ^ (3 * r) * 4 *
      (r * R₀ ^ (2 * r - 1) * De) ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) *
      (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r)))) :
    volume {y : UToff β → ℂ | ∀ p, ‖y p‖ ≤ R₀ ^ (2 * r) * De} *
      (volume : Measure (PPar k r)) (S ×ˢ ({s : UT r → ℂ | ∀ p, ‖s p‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2} ×ˢ
          {t : Fin r → ℝ | ∀ p, |t p| ≤ r * R₀ ^ (4 * r - 2) * De ^ 2})) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  have hR1 : 1 ≤ R₀ ^ (2 * r) * De := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) h1De
  have hR3 : 0 ≤ r * R₀ ^ (4 * r - 2) * De ^ 2 := by positivity
  rw [vol_PPar, vol_polydisc _ (zero_le_one.trans hR1), vol_polydisc _ hR3, vol_cube _ hR3, card_UT]
  have hcard : Fintype.card (UToff β) ≤ r * (r - 1) / 2 := card_UT r ▸ Fintype.card_subtype_le _
  have hb : 1 ≤ Real.pi * (R₀ ^ (2 * r) * De) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (by linarith [Real.pi_gt_three]) (one_le_pow₀ hR1)
  refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hb hcard))
    (mul_le_mul' hS le_rfl)) ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have har := _root_.GlobalTheory.Amp.volume_product_le r R₀ De hr hR h1De
  have hpos : 0 ≤ (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) *
    (2 * y) ^ (2 * (k - 2 - r)) := by positivity
  unfold fibVol
  exact arith hpos har

theorem fibre_bound : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yv k r z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR k r β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  intro k r z z' g₀ β De hr hk hT hN hD m hm a ha
  obtain ⟨P₀, hP₀, hY⟩ := _root_.GlobalTheory.Amp.NormGram.Yv_normal k r z z' g₀ β (by omega) hT hN m hm
  obtain ⟨hV0, hV⟩ := _root_.GlobalTheory.Amp.GramVol.vol_gram_codim_three k r hr hk m hm P₀ hP₀
  obtain ⟨hM1, hM2⟩ := _root_.GlobalTheory.Amp.YMeas.yv_measurable k r z z' g₀ hN.1
  have hU := fun R₀ hR => _root_.GlobalTheory.Amp.NfOff.offBlock_le k r z z' g₀ β De R₀ hT hN hD hR m hm
  have hB := fun R₀ hR => _root_.GlobalTheory.Amp.RadBound.radical_coords_le k r z z' g₀ β De R₀ hT hN hD hR m hm
  have hdG : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) ∈ GG k r := by
    apply UEmb.uEmb_mem
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun b _ => by exact_mod_cast (ha b).ne'
  have hmG : mEmb k r m ∈ GG k r := Rad.mEmb_mem m hm
  have hNq := coord_mem k r
  have hY' := fun u q => hY u q a ha
  have hU' := fun R₀ hR w q => hU R₀ hR w q a ha
  have hB' := fun R₀ hR w q => hB R₀ hR w q a ha
  have hcG := YInv.mul_mem hdG hmG
  simp only [Matrix.mul_assoc _ (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)))] at hY' hU' hB'
  clear hY hU hB
  generalize uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m = c at *
  have hrm : Measurable (rmulM c) := (continuous_rmulM c).measurable
  constructor
  · have hZ : MeasurableSet ((Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r}
        (fun x => Yv k r z z' g₀ (Matrix.of x)) ∘ rmulM c) ⁻¹' {0}) := (hM1.comp hrm) (measurableSet_singleton 0)
    refine measure_mono_null (fun n hn => ?_) (null_of _ hZ _ hV0 fun u q hq => ?_)
    · exact Set.indicator_apply_eq_zero.2 fun _ => hn
    · have := Set.indicator_apply_eq_zero.1 hq (YInv.mul_mem (hNq u q).1 hcG)
      exact (hY' u q).symm.trans this
  · intro φ hφ R₀ y hR hy
    have h1De : 1 ≤ De := hD.1
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hR2 : 1 ≤ r * R₀ ^ (2 * r - 1) * De :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hr' (one_le_pow₀ hR)) h1De
    refine le_trans ?_ (vol_bound β hr hR h1De hy _ (hV _ y hR2 hy))
    refine le_trans (le_of_eq ?_) (lintegral_le hN.2.2.1 φ hφ (rmulM c ⁻¹' Eset k r z z' g₀ R₀ y) (hrm (hM2 R₀ y)) _ _ ?_)
    · refine lintegral_congr fun n => ?_
      congr 1
    · intro x w q hx
      have hρ : uEmb k r (upperIn β x) ∈ Rset k r g₀ := by
        rw [(_root_.GlobalTheory.Amp.StabNormal.stabiliser_normal k r g₀ β hN).1]; exact ⟨x, rfl⟩
      have hn0 : uEmb k r (upperOff β w) * pOf k r q ∈ Nset k r := coord_off_mem k r β w q
      have hx0 : uEmb k r (upperOff β w) * pOf k r q * c ∈ GG k r := YInv.mul_mem hn0.1 hcG
      have hx1 : (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β w) * pOf k r q * c)) : Mt k r) ∈
          Eset k r z z' g₀ R₀ y := by
        rw [← Matrix.mul_assoc]; exact hx
      obtain ⟨s1, s2, s3, s4⟩ := mem_of_mul hT.1 hT.2.1 hN.1 hρ hx0 hx1
      have e4 : Yv k r z z' g₀ (uEmb k r (upperOff β w) * pOf k r q * c) = gramProj P₀ fun b => m⁻¹ *ᵥ q.1 b := by
        unfold upperOff
        exact hY' _ q
      rw [e4] at s3 s4
      obtain ⟨b1, b2, b3⟩ := hB' R₀ hR w q s1 s2
      exact ⟨hU' R₀ hR w q s1 s2, ⟨b1, s3, s4⟩, b2, b3⟩

end GlobalTheory.Amp.FibNf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentGramNullAndFibreVolumeNormalForm
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibreNormal

theorem vol_discs (ι : Type) [Fintype ι] {M : ℝ} (hM : 0 ≤ M) :
    volume {x : ι → ℂ | ∀ p, ‖x p‖ ≤ M} = ENNReal.ofReal ((Real.pi * M ^ 2) ^ Fintype.card ι) := by
  have h : {x : ι → ℂ | ∀ p, ‖x p‖ ≤ M} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) M := by
    ext x; simp
  rw [h, volume_pi_pi, Finset.prod_const, Finset.card_univ, Complex.volume_closedBall,
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hM, mul_comm]
  congr 2
  exact (ENNReal.ofReal_coe_nnreal (p := NNReal.pi)).symm

theorem vol_ints (ι : Type) [Fintype ι] {M : ℝ} (hM : 0 ≤ M) :
    volume {x : ι → ℝ | ∀ p, |x p| ≤ M} = ENNReal.ofReal ((2 * M) ^ Fintype.card ι) := by
  have h : {x : ι → ℝ | ∀ p, |x p| ≤ M} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℝ) M := by
    ext x; simp
  rw [h, volume_pi_pi, Finset.prod_const, Finset.card_univ, Real.volume_closedBall,
    ENNReal.ofReal_pow (by positivity)]

def lowEquiv {r j : ℕ} (hj : j ≤ r) : Fin j ≃ {a : Fin r // a.val < j} where
  toFun b := ⟨Fin.castLE hj b, b.2⟩
  invFun a := ⟨a.1.val, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem vol_reindex {k r j : ℕ} (hj : j ≤ r) (T : Set (Fin j → Fin (k + 1) → ℂ)) :
    volume {B : {a : Fin r // a.val < j} → Fin (k + 1) → ℂ | (fun b : Fin j => B ⟨Fin.castLE hj b, b.2⟩) ∈ T} =
      volume T := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : {a : Fin r // a.val < j} => Fin (k + 1) → ℂ)
    (lowEquiv hj)).symm
  rw [← h.measure_preimage_equiv T]
  rfl

theorem card_UT (r : ℕ) : 2 * Fintype.card (UT r) ≤ r * (r - 1) := by
  have h : Fintype.card (UT r) = r.choose 2 := by
    rw [Fintype.card_subtype, ← Finset.univ_product_univ, Finset.card_product_filter_lt]
    simp
  rw [h, Nat.choose_two_right]
  exact Nat.mul_div_le _ _

theorem vol_box {k r j : ℕ} (β : Fin r → ℕ) (A : Set ({a : Fin r // a.val < j} → Fin (k + 1) → ℂ))
    (B : Set ({p : UT r // p.1.1.val < j} → ℂ)) (C : Set ({a : Fin r // a.val < j} → ℝ)) (D : Set (UToff β → ℂ)) :
    (volume : Measure (PSec k r j × (UToff β → ℂ))) ((A ×ˢ B ×ˢ C) ×ˢ D) =
      volume A * (volume B * volume C) * volume D := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod]

theorem sEl_mem {k r j : ℕ} (β : Fin r → ℕ) (q : PSec k r j × (UToff β → ℂ)) : sEl k r j β q ∈ Nset k r :=
  isClosedSub_Nset.2.2.2.1 _ ((((Rad.radical k r).1 _ _).2.2.2 (Rad.skewM_skew _ _)).1) _ (UEmb.upper_mem _)

theorem ae_mem_range {k r j : ℕ} (β : Fin r → ℕ) {S : Set (Mat k r)} (hS : IsClosed S)
    (h : Set.range (rEl k r j β) ⊆ S) : ∀ᵐ ρ ∂(lebR0 k r j β), Matrix.of ρ ∈ S := by
  unfold lebR0
  have hS' : IsClosed {x : Mt k r | Matrix.of x ∈ S} := hS
  have hu : Measurable fun x : UTin β → ℂ =>
      (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r) := by
    have hU : Continuous (upperIn β) := by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [upperIn, upper]
      split_ifs <;> first | exact continuous_apply _ | exact continuous_const
    have heq : ∀ x, (upperIn β x)⁻¹ = (upperIn β x).adjugate := fun x => by
      rw [Matrix.inv_def, upperIn, UEmb.det_upper]; simp
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => Continuous.measurable ?_
    simp only [Matrix.of_symm_apply, uEmb, heq]
    split_ifs
    · exact hU.matrix_elem _ _
    · exact (hU.matrix_adjugate.matrix_elem _ _).star
    · exact continuous_const
    · exact continuous_const
  have hp : Measurable fun q : PTop k r j => (Matrix.of.symm (pTop k r j q) : Mt k r) := by
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => Continuous.measurable ?_
    simp only [Matrix.of_symm_apply, pTop, pOf, pEl, skewM, herm, bvec, dotProduct, Matrix.mulVec]
    split_ifs <;> fun_prop
  have hm : AEMeasurable (fun q => (Matrix.of.symm (rEl k r j β q) : Mt k r))
      (volume : Measure ((UTin β → ℂ) × PTop k r j)) := by
    unfold rEl
    apply Measurable.aemeasurable
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
    simp only [Matrix.of_symm_apply, Matrix.mul_apply]
    exact Finset.measurable_sum _ fun i _ =>
      (((measurable_pi_iff.1 (measurable_pi_iff.1 hu a)) i).comp measurable_fst).mul
        (((measurable_pi_iff.1 (measurable_pi_iff.1 hp i)) b).comp measurable_snd)
  rw [ae_map_iff hm hS'.measurableSet]
  exact Filter.Eventually.of_forall fun q => h ⟨q, rfl⟩

theorem N_sub_S {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, (isClosedSub_UWset z).2.2.1, n, hn, (Matrix.one_mul n).symm⟩

theorem Sg2_N {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {n x : Mat k r}
    (hn : n ∈ Nset k r) (hx : x ∈ GG k r) : Sg2 k r z (n * x) = Sg2 k r z x := by
  have := (TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.1 x hx n (N_sub_S z hn) 1
    ⟨isClosedSub_GG.2.2.1, (Matrix.unitaryGroup _ ℂ).one_mem⟩
  rwa [Matrix.mul_one] at this

theorem fibre_volume : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → 1 ≤ j → j + 2 ≤ k → ∀ De : ℝ, DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yj k r hj z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR0 k r j β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset0 k r hj z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y) := by
  intro k r j hj z z' g₀ β c hz hz' hT hN h1j hjk De hDe m hm a ha
  have hT' : 0 < Tz k r z' := by rw [(GlobalTheory.Amp.NfMid.normal0_middle k r j hj z z' g₀ β c hz hz' hT hN).1]; exact hT
  obtain ⟨hR, hRc⟩ := _root_.GlobalTheory.Amp.rset_normal0 k r j hj z z' g₀ β c hz hz' hT hN
  obtain ⟨P₀, hP₀, hY⟩ := _root_.GlobalTheory.Amp.NormalGram.Yj_eq_gramProj k r j hj z z' g₀ β c hz hz' hT hN m hm
  obtain ⟨hnull, hvol⟩ := GlobalTheory.Amp.GramVol.vol_gram k j h1j hjk m hm P₀ hP₀
  obtain ⟨hYm, hEm⟩ := _root_.GlobalTheory.Amp.YMeas.yj_measurable k r j hj z z' g₀ hz hz' hT hT' hN.1
  have hsplit := _root_.GlobalTheory.Amp.RadConj.lebN_split k r j β hN.2.2.2.1 hN.2.2.2.2.1
  have hB := fun R₀ hR₀ q => GlobalTheory.T.siegel_height_bound_section k r j hj z z' g₀ β c hz hz' hT hN De R₀ hDe hR₀ m hm q a ha
  have hY' := fun q => hY q a ha
  have hmul := (isClosedSub_GG (k := k) (r := r)).2.2.2.1
  have ht : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m ∈ GG k r := by
    refine hmul _ (UEmb.uEmb_mem _ ?_) _ (Rad.mEmb_mem m hm)
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun b _ => Complex.ofReal_ne_zero.2 (ha b).ne'
  generalize uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m = t at *
  have hae : ∀ᵐ ρ ∂(lebR0 k r j β), Matrix.of ρ ∈ Rset k r g₀ := ae_mem_range β hRc.2.1 hR.ge
  have hst : ∀ q : PSec k r j × (UToff β → ℂ), sEl k r j β q * t ∈ GG k r := fun q => hmul _ (sEl_mem β q).1 _ ht
  have hassoc : ∀ (q : PSec k r j × (UToff β → ℂ)) (ρ : Mt k r),
      (Matrix.of (rmulM t (rmulM (sEl k r j β q) ρ)) : Mat k r) = Matrix.of ρ * (sEl k r j β q * t) :=
    fun q ρ => by rw [of_rmulM, of_rmulM, Matrix.mul_assoc]
  have hYρ : ∀ (q : PSec k r j × (UToff β → ℂ)) (ρ : Mt k r), Matrix.of ρ ∈ Rset k r g₀ →
      Yj k r hj z z' g₀ (Matrix.of ρ * (sEl k r j β q * t)) =
        gramProj P₀ fun b : Fin j => m⁻¹ *ᵥ q.1.1 ⟨Fin.castLE hj b, b.2⟩ := fun q ρ hρ => by
    rw [(GlobalTheory.Amp.YjInv.yj_invariant k r j hj z z' g₀ hz hz' hN.1 _ (hst q)).2.2 _ hρ, hY' q]
  have htm : Measurable (rmulM t : Mt k r → Mt k r) := (continuous_rmulM t).measurable
  constructor
  · set S : Set (Mt k r) := {n | Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r}
      (fun x => Yj k r hj z z' g₀ (Matrix.of x)) (rmulM t n) = 0} with hS
    have hSm : MeasurableSet S := (hYm.comp htm) (measurableSet_singleton 0)
    refine measure_mono_null (t := S) (fun n hn => ?_) ?_
    · exact Set.indicator_apply_eq_zero.2 fun _ => hn
    rw [← lintegral_indicator_one hSm, hsplit _ (measurable_one.indicator hSm)]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    have h0 : (volume : Measure (PSec k r j × (UToff β → ℂ)))
        (({B | (fun b : Fin j => B ⟨Fin.castLE hj b, b.2⟩) ∈
          {B : Fin j → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0}} ×ˢ Set.univ ×ˢ Set.univ) ×ˢ Set.univ) = 0 := by
      rw [vol_box, vol_reindex hj, hnull, zero_mul, zero_mul]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with q hq
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hae] with ρ hρ
    refine Set.indicator_of_notMem (fun hmem => hq ⟨⟨?_, trivial, trivial⟩, trivial⟩) _
    have hG : rmulM t (rmulM (sEl k r j β q) ρ) ∈ {x : Mt k r | Matrix.of x ∈ GG k r} := by
      rw [Set.mem_ofPred_eq, hassoc]; exact hmul _ hρ.1.1 _ (hst q)
    have h2 : Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r}
      (fun x => Yj k r hj z z' g₀ (Matrix.of x)) (rmulM t (rmulM (sEl k r j β q) ρ)) = 0 := hmem
    rw [Set.indicator_of_mem hG, hassoc, hYρ q ρ hρ] at h2
    exact h2
  · intro φ hφ R₀ y hR₀ hy
    have hM : 1 ≤ R₀ ^ (2 * r) * De := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR₀) hDe.1
    have hB' := hB R₀ hR₀
    unfold fibVol0
    generalize R₀ ^ (2 * r) * De = M at *
    have hM0 : 0 ≤ M := zero_le_one.trans hM
    rw [hsplit (fun n => φ n * (Eset0 k r hj z z' g₀ R₀ y).indicator 1 (rmulM t n)) (hφ.1.mul ((measurable_one.indicator (hEm R₀ y)).comp htm))]
    set Box : Set (PSec k r j × (UToff β → ℂ)) :=
      ({B | (fun b : Fin j => B ⟨Fin.castLE hj b, b.2⟩) ∈
          {B : Fin j → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ M) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y}} ×ˢ
        {x | ∀ p, ‖x p‖ ≤ 2 * r * M ^ 2} ×ˢ {x | ∀ p, |x p| ≤ 2 * r * M ^ 2}) ×ˢ {x | ∀ p, ‖x p‖ ≤ M} with hBox
    refine (lintegral_mono (g := Box.indicator 1) fun q => ?_).trans ((lintegral_indicator_one_le Box).trans ?_)
    · by_cases hq : q ∈ Box
      · rw [Set.indicator_of_mem hq]
        refine le_trans (lintegral_mono fun ρ => ?_) (hφ.2 (Matrix.of.symm (sEl k r j β q)) (sEl_mem β q))
        exact mul_le_of_le_one_right' (Set.indicator_le_self' (fun _ _ => zero_le_one) _)
      · rw [Set.indicator_of_notMem hq]
        refine (lintegral_eq_zero_of_ae_eq_zero ?_).le
        filter_upwards [hae] with ρ hρ
        refine mul_eq_zero_of_right _ (Set.indicator_of_notMem (fun hmem => hq ?_) _)
        obtain ⟨-, h1, h2, -, h3⟩ := hmem
        rw [hassoc] at h1 h2 h3
        rw [hYρ q ρ hρ] at h3
        rw [Sg2_N hz' hT' hρ.1 (hst q)] at h1
        have he : g₀ * (Matrix.of ρ * (sEl k r j β q * t)) =
            (g₀ * Matrix.of ρ * g₀⁻¹) * (g₀ * (sEl k r j β q * t)) := by
          rw [Matrix.mul_assoc (g₀ * Matrix.of ρ), Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hN.1),
            Matrix.mul_assoc]
        rw [he, Sg2_N hz hT hρ.2 (hmul _ hN.1 _ (hst q))] at h2
        obtain ⟨b1, b2, b3, b4⟩ := hB' q h1 (((TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.2.2 _).2.1.trans h2)
        exact ⟨⟨⟨fun b => b2 _, h3⟩, b3, b4⟩, b1⟩
    · have hr : (0 : ℝ) ≤ 2 * r * M ^ 2 := by positivity
      rw [hBox, vol_box, vol_reindex hj, vol_discs _ hr, vol_ints _ hr, vol_discs _ hM0]
      refine (mul_le_mul_left (mul_le_mul_left (hvol M y hM hy) _) _).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have har := box_volume_arith r j (Fintype.card (UToff β)) (Fintype.card {p : UT r // p.1.1.val < j})
        (Fintype.card {a : Fin r // a.val < j}) M h1j hj
        ((Nat.mul_le_mul_left 2 (Fintype.card_subtype_le _)).trans (card_UT r))
        ((Nat.mul_le_mul_left 2 (Fintype.card_subtype_le _)).trans (card_UT r))
        ((Fintype.card_subtype_le _).trans (Fintype.card_fin r).le) hM
      have hK : (0 : ℝ) ≤ (Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (2 * y) ^ (2 * (k - 1 - j)) := by
        positivity
      refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_right har hK).trans (le_of_eq ?_)) <;> ring

end GlobalTheory.Amp.FibreNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportCoeffMapBijectiveOntoValues
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem transport_J_bijective_onto :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F),
      Function.Injective Tr.J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, Tr.J ξ = p := by
  intro D X u F Tr
  obtain ⟨c, -⟩ := F.cls0.y_bij.2 (Quotient.mk'' 1)
  have hinj : Function.Injective Tr.J := by
    intro ξ η h
    have h1 := Tr.J_isom c ξ η
    have h2 := Tr.J_isom c ξ ξ
    have h3 := Tr.J_isom c η ξ
    have h4 := Tr.J_isom c η η
    rw [h] at h1 h2 h3
    rw [h4] at h1 h2 h3
    have h0 : ⟪ξ - η, ξ - η⟫_ℂ = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, ← h1, ← h2, ← h3]
      ring
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)
  refine ⟨hinj, ?_⟩
  obtain ⟨J₀, -, hJ₀⟩ := _root_.GlobalTheory.St.coefficient_map_exists_onto D X u F Tr.wt ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  exact GlobalTheory.conjLinear_onto_of_injective_of_le_range (X.Vpi u) _ _ J₀ Tr.J hJ₀ hinj Tr.J_val

end GlobalTheory
end

