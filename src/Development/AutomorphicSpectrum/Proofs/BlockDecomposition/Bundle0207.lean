module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0196
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0195
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0200
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarChartIntegralComparison

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorAdjoint
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.Ibp

variable {n : ℕ}

section Int

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem integrable_of_cpt (hL : LgFacts) {φ : Mat n → ℂ} (hφ : ContinuousOn φ (GLs n)) (cφ : Cpt φ) :
    Integrable (fun y : G n => φ y.val) μ := by
  obtain ⟨R, hR⟩ := cφ
  have hc : Continuous (fun y : G n => φ y.val) :=
    hφ.comp_continuous Units.continuous_val val_mem
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_)
  intro y hy
  exact hR _ (val_mem y) (not_le.1 hy)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem sm_inner {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => ⟪f y, h y⟫_ℂ) (GLs n) :=
  hf.inner ℂ hh

theorem Cpt_inner {f h : Mat n → V} (cf : Cpt f) : Cpt (fun y => ⟪f y, h y⟫_ℂ) := by
  obtain ⟨R, hR⟩ := cf
  exact ⟨R, fun y hy hl => by simp [hR y hy hl]⟩

theorem Cpt_inner' {f h : Mat n → V} (ch : Cpt h) : Cpt (fun y => ⟪f y, h y⟫_ℂ) := by
  obtain ⟨R, hR⟩ := ch
  exact ⟨R, fun y hy hl => by simp [hR y hy hl]⟩

theorem int_inner (hL : LgFacts) {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) :
    Integrable (fun y : G n => ⟪f y.val, h y.val⟫_ℂ) μ :=
  integrable_of_cpt μ hL (sm_inner hf hh).continuousOn (Cpt_inner cf)

theorem int_inner' (hL : LgFacts) {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hh : ContDiffOn ℝ ∞ h (GLs n)) (ch : Cpt h) :
    Integrable (fun y : G n => ⟪f y.val, h y.val⟫_ℂ) μ :=
  integrable_of_cpt μ hL (sm_inner hf hh).continuousOn (Cpt_inner' ch)

theorem ibp_Rd (hL : LgFacts) (hR : RCalc) (X : Mat n) {f h : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Rd X f y.val, h y.val⟫_ℂ ∂μ = -∫ y : G n, ⟪f y.val, Rd X h y.val⟫_ℂ ∂μ := by
  have h0 := (hR n).2.2 μ ℂ (fun y => ⟪f y, h y⟫_ℂ) (sm_inner hf hh) (Cpt_inner cf) X
  have e : ∀ y : G n, Rd X (fun y => ⟪f y, h y⟫_ℂ) y.val =
      ⟪f y.val, Rd X h y.val⟫_ℂ + ⟪Rd X f y.val, h y.val⟫_ℂ := by
    intro y
    exact fderiv_inner_apply ℂ (diffAt hf (val_mem y)) (diffAt hh (val_mem y)) _
  simp_rw [e] at h0
  rw [integral_add (int_inner' μ hL hf (sm_Rd hR X hh) (Cpt_Rd hL X ch))
    (int_inner μ hL (sm_Rd hR X hf) hh (Cpt_Rd hL X cf))] at h0
  exact eq_neg_of_add_eq_zero_right h0

theorem ibp_Eu (hL : LgFacts) (hR : RCalc) (s : Bool) (a b : Fin n) {f h : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Eu s a b f y.val, h y.val⟫_ℂ ∂μ = -∫ y : G n, ⟪f y.val, Eu (!s) a b h y.val⟫_ℂ ∂μ := by
  set X : Mat n := Matrix.single a b 1
  set Y : Mat n := Matrix.single a b Complex.I
  set c : ℂ := if !s then -Complex.I else Complex.I with hc
  have hc' : conj (if s then -Complex.I else Complex.I) = c := by
    cases s <;> simp [hc]
  have e1 : ∀ y : G n, ⟪Eu s a b f y.val, h y.val⟫_ℂ =
      (1 / 2 : ℂ) * (⟪Rd X f y.val, h y.val⟫_ℂ + c * ⟪Rd Y f y.val, h y.val⟫_ℂ) := by
    intro y
    have h2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    simp only [Eu, Pi.smul_apply, Pi.add_apply, inner_smul_left, inner_add_left, hc', h2]
    rfl
  have e2 : ∀ y : G n, ⟪f y.val, Eu (!s) a b h y.val⟫_ℂ =
      (1 / 2 : ℂ) * (⟪f y.val, Rd X h y.val⟫_ℂ + c * ⟪f y.val, Rd Y h y.val⟫_ℂ) := by
    intro y
    simp only [Eu, Pi.smul_apply, Pi.add_apply, inner_smul_right, inner_add_right]
    simp [X, Y, hc]
  simp_rw [e1, e2]
  rw [integral_const_mul, integral_const_mul,
    integral_add (int_inner μ hL (sm_Rd hR X hf) hh (Cpt_Rd hL X cf))
      ((int_inner μ hL (sm_Rd hR Y hf) hh (Cpt_Rd hL Y cf)).const_mul c),
    integral_add (int_inner' μ hL hf (sm_Rd hR X hh) (Cpt_Rd hL X ch))
      ((int_inner' μ hL hf (sm_Rd hR Y hh) (Cpt_Rd hL Y ch)).const_mul c),
    integral_const_mul, integral_const_mul, ibp_Rd μ hL hR X hf hh cf ch, ibp_Rd μ hL hR Y hf hh cf ch]
  ring

theorem ibp_Epow (hL : LgFacts) (hR : RCalc) (s : Bool) (m : ℕ) (a b : Fin n) {f h : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Epow s m a b f y.val, h y.val⟫_ℂ ∂μ =
      (-1 : ℂ) ^ m * ∫ y : G n, ⟪f y.val, EpowT (!s) m b a h y.val⟫_ℂ ∂μ := by
  induction m generalizing a h with
  | zero =>
    by_cases hab : a = b
    · subst hab
      simp [Epow, EpowT]
    · simp [Epow, EpowT, hab, Ne.symm hab]
  | succ m ih =>
    have e1 : ∀ y : G n, ⟪Epow s (m + 1) a b f y.val, h y.val⟫_ℂ =
        ∑ c, ⟪Eu s a c (Epow s m c b f) y.val, h y.val⟫_ℂ := by
      intro y
      simp only [Epow, Finset.sum_apply, sum_inner]
    have e2 : ∀ y : G n, ⟪f y.val, EpowT (!s) (m + 1) b a h y.val⟫_ℂ =
        ∑ c, ⟪f y.val, EpowT (!s) m b c (Eu (!s) a c h) y.val⟫_ℂ := by
      intro y
      rw [EpowT_succ' hR (!s) m a b hh (val_mem y), Finset.sum_apply, inner_sum]
    simp_rw [e1, e2]
    rw [MeasureTheory.integral_finsetSum _ fun c _ => int_inner μ hL (sm_Eu hR s a c (sm_Epow hR s m c b hf)) hh
        (Cpt_Eu hL s a c (Cpt_Epow hL s m c b cf)),
      MeasureTheory.integral_finsetSum _ fun c _ => int_inner μ hL hf
        (sm_EpowT hR (!s) m b c (sm_Eu hR (!s) a c hh)) cf,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ibp_Eu μ hL hR s a c (sm_Epow hR s m c b hf) hh (Cpt_Epow hL s m c b cf) ch,
      ih c (sm_Eu hR (!s) a c hh) (Cpt_Eu hL (!s) a c ch), pow_succ]
    ring

end Int

theorem ibp_gel : LgFacts → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)]
    (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (s : Bool) (m : ℕ) (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
    ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h →
    ∫ y : G n, ⟪gel s m f y.val, h y.val⟫_ℂ ∂μ =
      (-1 : ℂ) ^ m * ∫ y : G n, ⟪f y.val, gelT (!s) m h y.val⟫_ℂ ∂μ := by
  intro hL hR n _ _ μ _ V _ _ _ s m f h hf hh cf ch
  have e1 : ∀ y : G n, ⟪gel s m f y.val, h y.val⟫_ℂ = ∑ a, ⟪Epow s m a a f y.val, h y.val⟫_ℂ := by
    intro y
    simp only [gel, Finset.sum_apply, sum_inner]
  have e2 : ∀ y : G n, ⟪f y.val, gelT (!s) m h y.val⟫_ℂ =
      ∑ a, ⟪f y.val, EpowT (!s) m a a h y.val⟫_ℂ := by
    intro y
    simp only [gelT, Finset.sum_apply, inner_sum]
  simp_rw [e1, e2]
  rw [MeasureTheory.integral_finsetSum _ fun a _ => int_inner μ hL (sm_Epow hR s m a a hf) hh
      (Cpt_Epow hL s m a a cf),
    MeasureTheory.integral_finsetSum _ fun a _ => int_inner μ hL hf (sm_EpowT hR (!s) m a a hh) cf,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => ibp_Epow μ hL hR s m a a hf hh cf ch

end GlobalTheory.CompanionTheory.WaveMult.Ibp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandValueNegation
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.ValPhi

open PowerSeries

section
variable {A : Type} [Ring A] (N : A) (τ : ℕ → A)

theorem bco_of_lt : ∀ (m j : ℕ), m < j → bco N τ m j = 0 := by
  intro m
  induction m with
  | zero =>
    intro j h
    cases j with
    | zero => omega
    | succ j => simp [bco]
  | succ m ih =>
    intro j h
    cases j with
    | zero => omega
    | succ j => rw [bco, ih j (by omega), ih (j + 1) (by omega)]; simp

theorem bco_self (m : ℕ) : bco N τ m m = 1 := by
  induction m with
  | zero => simp [bco]
  | succ m ih => rw [bco, ih, bco_of_lt N τ m (m + 1) (by omega)]; simp

theorem eq_phiSeq (p : ℕ → A) (h : ∀ m, ∑ j ∈ range (m + 1), bco N τ m j * p j = τ m) (m : ℕ) :
    p m = phiSeq N τ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have e : ∑ j ∈ range m, bco N τ m j * phiSeq N τ j = ∑ j ∈ range m, bco N τ m j * p j :=
      sum_congr rfl fun j hj => by rw [ih j (mem_range.1 hj)]
    rw [phiSeq, Fin.sum_univ_eq_sum_range (fun j => bco N τ m j * phiSeq N τ j) m, e, ← h m,
      sum_range_succ, bco_self, one_mul]
    abel
end

section
variable (N : ℂ) (τ : ℕ → ℂ)

noncomputable def bser (j : ℕ) : PowerSeries ℂ := PowerSeries.mk (fun m => bco N τ m j)

theorem coeff_bser (j m : ℕ) : coeff m (bser N τ j) = bco N τ m j := by simp [bser]

theorem constantCoeff_bser (j : ℕ) : constantCoeff (bser N τ j) = bco N τ 0 j := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_bser]

theorem bser_zero : (1 - C N * X) * bser N τ 0 = 1 - X * PowerSeries.mk τ := by
  have e : ∀ f : PowerSeries ℂ, (1 - C N * X) * f = f - C N * (X * f) := fun f => by ring
  rw [e]
  ext k
  cases k with
  | zero => simp [constantCoeff_bser, bco]
  | succ k =>
    simp [coeff_bser, bco, coeff_succ_X_mul, coeff_one]

theorem bser_succ (j : ℕ) : (1 - C N * X) * bser N τ (j + 1) = X * bser N τ j := by
  have e : ∀ f : PowerSeries ℂ, (1 - C N * X) * f = f - C N * (X * f) := fun f => by ring
  rw [e]
  ext k
  cases k with
  | zero => simp [constantCoeff_bser, bco]
  | succ k =>
    simp [coeff_bser, bco, coeff_succ_X_mul]

theorem bser_eq {w : PowerSeries ℂ} (hw : (1 - C N * X) * w = 1) (j : ℕ) :
    bser N τ j = (1 - X * PowerSeries.mk τ) * w ^ (j + 1) * X ^ j := by
  induction j with
  | zero =>
    have := bser_zero N τ
    rw [← this]
    linear_combination (-(bser N τ 0)) * hw
  | succ j ih =>
    have := bser_succ N τ j
    rw [ih] at this
    linear_combination (-(bser N τ (j + 1))) * hw + w * this

end

theorem mk_decomp (g : ℕ → ℂ) (m : ℕ) :
    PowerSeries.mk g = ∑ j ∈ range (m + 1), g j • (X : PowerSeries ℂ) ^ j
      + X ^ (m + 1) * PowerSeries.mk (fun i => g (i + (m + 1))) := by
  ext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, coeff_mk, coeff_X_pow_mul', LinearMap.map_smul, coeff_X_pow,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hk : m + 1 ≤ k
  · rw [if_pos hk, Nat.sub_add_cancel hk, sum_ite_eq]
    simp [mem_range]
    omega
  · rw [if_neg hk, sum_ite_eq, if_pos (mem_range.2 (by omega))]
    simp

theorem sum_of_subst (N : ℂ) (τ g : ℕ → ℂ) {w : PowerSeries ℂ} (hw : (1 - C N * X) * w = 1)
    (ha : HasSubst (-(X * w)))
    (h : (1 - X * PowerSeries.mk τ) * subst (-(X * w)) (1 - X * PowerSeries.mk g) = 1) (m : ℕ) :
    ∑ j ∈ range (m + 1), bco N τ m j * ((-1) ^ j * g j) = τ m := by
  let θ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ := substAlgHom ha
  have hθ : ∀ f, subst (-(X * w)) f = θ f := fun f => by simp [θ, coe_substAlgHom]
  have hX : θ X = -(X * w) := by rw [← hθ]; exact subst_X ha
  set H := PowerSeries.mk (fun i => g (i + (m + 1))) with hH
  set Q := 1 - X * PowerSeries.mk τ with hQ
  have hG : θ (PowerSeries.mk g) = ∑ j ∈ range (m + 1), g j • (-(X * w)) ^ j
      + (-(X * w)) ^ (m + 1) * θ H := by
    conv_lhs => rw [mk_decomp g m]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, map_mul, map_pow, hX, hH]
  rw [hθ, map_sub, map_one, map_mul, hX, hG] at h
  have hterm : ∀ j, Q * (X * w) * (g j • (-(X * w)) ^ j)
      = (g j * (-1) ^ j) • (X * bser N τ j) := by
    intro j
    rw [bser_eq N τ hw j, neg_pow]
    simp only [smul_eq_C_mul, map_mul, map_pow, map_neg, map_one]
    ring
  have hfin : Q + ∑ j ∈ range (m + 1), (g j * (-1) ^ j) • (X * bser N τ j)
      + X ^ (m + 2) * (Q * w * (-w) ^ (m + 1) * θ H) = 1 := by
    rw [← h, ← sum_congr rfl fun j _ => hterm j, ← mul_sum, neg_mul_eq_mul_neg X w, mul_pow]
    ring
  have hc := congrArg (coeff (m + 1)) hfin
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, LinearMap.map_smul, coeff_succ_X_mul, coeff_bser, coeff_X_pow_mul',
    smul_eq_mul, hQ, map_sub, coeff_mk, coeff_one] at hc
  simp at hc
  have e : ∑ j ∈ range (m + 1), bco N τ m j * ((-1) ^ j * g j)
      = ∑ x ∈ range (m + 1), g x * (-1) ^ x * bco N τ m x :=
    sum_congr rfl fun j _ => by ring
  rw [e]
  linear_combination hc

theorem mul_subst_eq_one (n : ℕ) (cc : Fin n → ℂ) {w : PowerSeries ℂ}
    (hw : (1 - C (n : ℂ) * X) * w = 1) (ha : HasSubst (-(X * w))) :
    (1 - X * gser cc) * subst (-(X * w)) (1 - X * gser (fun a => - cc a)) = 1 := by
  let θ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ := substAlgHom ha
  have hθ : ∀ f, subst (-(X * w)) f = θ f := fun f => by simp [θ, coe_substAlgHom]
  have hX : θ X = -(X * w) := by rw [← hθ]; exact subst_X ha
  have hC : ∀ c : ℂ, θ (C c) = C c := fun c => θ.commutes c
  have e1 : ∀ i, 1 - C (-cc i + ((n : ℂ) - 1) / 2) * -(X * w)
      = w * (1 - C (cc i + ((n : ℂ) - 1) / 2 + 1) * X) := by
    intro i
    have hn : C (n : ℂ) = C (-cc i + ((n : ℂ) - 1) / 2) + C (cc i + ((n : ℂ) - 1) / 2 + 1) := by
      rw [← map_add (f := _)]; congr 1; ring
    linear_combination (-1 : PowerSeries ℂ) * hw - X * w * hn
  have e2 : ∀ i, 1 - C (-cc i + ((n : ℂ) - 1) / 2 + 1) * -(X * w)
      = w * (1 - C (cc i + ((n : ℂ) - 1) / 2) * X) := by
    intro i
    have hn : C (n : ℂ) = C (-cc i + ((n : ℂ) - 1) / 2 + 1) + C (cc i + ((n : ℂ) - 1) / 2) := by
      rw [← map_add (f := _)]; congr 1; ring
    linear_combination (-1 : PowerSeries ℂ) * hw - X * w * hn
  have h1 := _root_.GlobalTheory.CompanionTheory.WaveMult.gser_mul_prod n cc
  have h2 := congrArg θ (_root_.GlobalTheory.CompanionTheory.WaveMult.gser_mul_prod n (fun a => - cc a))
  simp only [map_mul, map_prod, map_sub, map_one, hC, hX, e1, e2, prod_mul_distrib, prod_const,
    card_univ, Fintype.card_fin] at h2
  set D := ∏ a, (1 - C (cc a + ((n : ℂ) - 1) / 2 + 1) * (X : PowerSeries ℂ)) with hD
  set E := ∏ a, (1 - C (cc a + ((n : ℂ) - 1) / 2) * (X : PowerSeries ℂ)) with hE
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hD0 : D ≠ 0 := by
    refine prod_ne_zero_iff.2 fun i _ h0 => ?_
    have := congrArg constantCoeff h0
    simp at this
  rw [hθ, map_sub, map_one, map_mul, hX]
  refine mul_right_cancel₀ (mul_ne_zero (pow_ne_zero n hw0) hD0) ?_
  linear_combination (1 - X * gser cc) * h2 + w ^ n * h1

theorem gelfVal_neg_eq_phiSeq : ∀ (n : ℕ) (cc : Fin n → ℂ) (m : ℕ),
    (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m = phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal cc) m := by
  intro n cc m
  have hu : constantCoeff (1 - C (n : ℂ) * X : PowerSeries ℂ) ≠ 0 := by simp
  have hw := PowerSeries.mul_inv_cancel _ hu
  have ha : HasSubst (-(X * (1 - C (n : ℂ) * X : PowerSeries ℂ)⁻¹)) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  exact eq_phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal cc)
    (fun m => (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m)
    (sum_of_subst (n : ℂ) _ _ hw ha (mul_subst_eq_one n cc hw ha)) m

end GlobalTheory.CompanionTheory.WaveMult.ValPhi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateRightDerivativeStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_translate_right_derivative : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
    ContDiffOn ℝ ∞ f (GLs n) → ∀ x ∈ GLs n, ContDiffOn ℝ ∞ (fun y => f (x * y)) (GLs n) ∧
      ∀ (w : List (Idx n)), ∀ y ∈ GLs n, Rw w (fun y => f (x * y)) y = Rw w f (x * y) := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left | exact GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left | (intros; apply GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthContinuousProperSublevelStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_continuous_proper_sublevel : ∀ n : ℕ, ContinuousOn (lg (n := n)) (GLs n) ∧ ∀ R : ℝ, IsCompact {y : G n | lg y.val ≤ R} := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact | exact GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact | (intros; apply GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.PresSobA

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.SobGL.HaarDom

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev CLof (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] : Type :=
  E →L[ℝ] F

def expC (X : Mat n) (t : ℝ) : G n := (Matrix.isUnit_exp (t • X)).unit

theorem expC_val (X : Mat n) (t : ℝ) : (expC X t).val = NormedSpace.exp (t • X) := rfl

theorem expC_zero (X : Mat n) : expC X 0 = 1 := by
  apply Units.ext
  simp [expC_val]

def IsTest (φ : Mat n → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ GLs n

section Mol

variable [MeasurableSpace (G n)] (μ : Measure (G n))

def Mol {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : Mat n → ℝ) (x : G n → V) (z : Mat n) : V :=
  ∫ u : G n, φ (z * (u⁻¹ : G n).val) • x u ∂μ

variable [BorelSpace (G n)] [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def lT (y : G n) : Lp V 2 μ →L[ℂ] Lp V 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun z : G n => y⁻¹ * z) (measurePreserving_mul_left μ y⁻¹)).toContinuousLinearMap

def lConv (φ : Mat n → ℝ) (x : Lp V 2 μ) : Lp V 2 μ := ∫ y : G n, φ y.val • lT μ V y x ∂μ

variable {V}

theorem lT_coe (y : G n) (x : Lp V 2 μ) : lT μ V y x =ᵐ[μ] fun z => x (y⁻¹ * z) :=
  Lp.coeFn_compMeasurePreserving x (measurePreserving_mul_left μ y⁻¹)

theorem rR_coe (hU : Unimod) (h : G n) (x : Lp V 2 μ) : rR μ V h x =ᵐ[μ] fun z => x (z * h) := by
  haveI := (hU n μ).1
  have hm : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
  have : rR μ V h x = Lp.compMeasurePreserving (fun y : G n => y * h) hm x := by
    simp only [rR, dif_pos hm]
    rfl
  rw [this]
  exact Lp.coeFn_compMeasurePreserving x hm

theorem cls_of_ae {f : Mat n → V} {x : Lp V 2 μ} (h : (fun y : G n => f y.val) =ᵐ[μ] x) :
    MemLp (fun y : G n => f y.val) 2 μ ∧ cls μ f = x := by
  have hm : MemLp (fun y : G n => f y.val) 2 μ := (memLp_congr_ae h).2 (Lp.memLp x)
  refine ⟨hm, ?_⟩
  simp only [cls, dif_pos hm]
  exact Lp.ext (hm.coeFn_toLp.trans h)

theorem coe_cls {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) :
    (cls μ f : G n → V) =ᵐ[μ] fun y => f y.val := by
  simp only [cls, dif_pos h]
  exact h.coeFn_toLp

end Mol

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_congr {f f' : Mat n → V} (h : ∀ z ∈ GLs n, f z = f' z) (X : Mat n) :
    ∀ z ∈ GLs n, Rd X f z = Rd X f' z := by
  intro z hz
  have : f =ᶠ[𝓝 z] f' := Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hz) h
  simp only [Rd, this.fderiv_eq]

theorem Rw_append (w w' : List (Bool × Fin n × Fin n)) (f : Mat n → V) :
    Rw (w ++ w') f = Rw w (Rw w' f) := by
  induction w with
  | nil => rfl
  | cons p w ih => simp only [List.cons_append, Rw, ih]

end Words

end GlobalTheory.CompanionTheory.PresSobA
end
end

