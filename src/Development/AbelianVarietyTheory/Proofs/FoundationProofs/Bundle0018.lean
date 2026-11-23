module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointsDistinctModMaximalIdeal
section
namespace GlobalTheory

open WeierstrassCurve WeierstrassCurve.Affine

namespace TorsionUnit

variable {K : Type} [NormedField K] [IsUltrametricDist K]

end TorsionUnit

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma short_negY_eq (A B x y : K) :
    ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).negY x y = -y := by
  simp [Affine.negY]

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma short_addX_eq (A B x₁ x₂ l : K) :
    ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).addX x₁ x₂ l = l ^ 2 - x₁ - x₂ := by
  simp [Affine.addX]

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_add_le_one_of_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_le_one_of_norm_sq_sub_le_one {l s : K} (h : ‖l ^ 2 - s‖ ≤ 1) (hs : ‖s‖ ≤ 1) :
    ‖l‖ ≤ 1 := by
  have hsq : ‖l ^ 2‖ ≤ 1 := by
    have := norm_add_le_one_of_le_one h hs
    rwa [sub_add_cancel] at this
  rw [norm_pow] at hsq
  exact (pow_le_one_iff_of_nonneg (norm_nonneg l) two_ne_zero).mp hsq

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_mul_le_one_of_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma short_equation_of_nonsingular {A B x y : K}
    (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + A * x + B := by
  have := h.1
  simp [Affine.equation_iff] at this
  linear_combination this

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_sub_le_one_of_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact norm_add_le_one_of_le_one ha (by rwa [norm_neg])

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : K)‖ ≤ 1 := by
  exact_mod_cast IsUltrametricDist.norm_natCast_le_one K n

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_y_eq_one_of_nsmul_eq_zero [DecidableEq K] {A B : K} {N : ℕ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (h2 : ‖(2 : K)‖ = 1) (hD : ‖4 * A ^ 3 + 27 * B ^ 2‖ = 1) (hN : Odd N)
    (hT : ∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y),
      N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1)
    {x y : K} (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y)
    (hP : N • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ‖y‖ = 1 := by
  have hx := hT _ _ h hP
  have h2ne : (2 : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h2
    exact zero_ne_one h2
  have hy : y ≠ ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).negY x y := by
    intro hyy
    have hneg : -Point.some x y h = Point.some x y h := by
      rw [Point.neg_some]
      congr 1
      exact hyy.symm
    obtain ⟨k, rfl⟩ := hN
    have hPP : Point.some x y h + Point.some x y h = 0 := by
      nth_rewrite 1 [← hneg]
      exact neg_add_cancel _
    rw [add_smul, one_smul, mul_comm, mul_smul, two_smul, hPP, smul_zero, zero_add] at hP
    simp at hP
  have hy0 : y ≠ 0 := by
    intro h0
    apply hy
    rw [short_negY_eq, h0, neg_zero]
  have hdbl := Point.add_of_Y_ne (h₁ := h) (h₂ := h) hy
  have h3 := hT _ _ _ (by rw [← hdbl, smul_add, hP, add_zero])
  rw [short_addX_eq] at h3
  set l := ((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine).slope x x y y with hl
  have hlrel : l * (2 * y) = 3 * x ^ 2 + A := by
    rw [hl, slope_of_Y_ne rfl hy, short_negY_eq, sub_neg_eq_add, ← two_mul,
      div_mul_cancel₀ _ (mul_ne_zero h2ne hy0)]
    simp
  have hlle : ‖l‖ ≤ 1 :=
    norm_le_one_of_norm_sq_sub_le_one (s := x + x) (by rw [← sub_sub]; exact h3)
      (norm_add_le_one_of_le_one hx hx)
  have hder : ‖3 * x ^ 2 + A‖ ≤ ‖y‖ := by
    rw [← hlrel, norm_mul, norm_mul, h2, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hlle
  have hx2 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  have hx3 : ‖x ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  have hf : ‖x ^ 3 + A * x + B‖ ≤ 1 :=
    norm_add_le_one_of_le_one (norm_add_le_one_of_le_one hx3 (norm_mul_le_one_of_le_one hA hx)) hB
  have hyeq := short_equation_of_nonsingular h
  have hyle : ‖y‖ ≤ 1 := by
    have : ‖y‖ ^ 2 ≤ 1 := by rw [← norm_pow, hyeq]; exact hf
    exact (pow_le_one_iff_of_nonneg (norm_nonneg y) two_ne_zero).mp this
  refine le_antisymm hyle (not_lt.mp fun hlt => ?_)
  have hflt : ‖x ^ 3 + A * x + B‖ < 1 := by
    rw [← hyeq, norm_pow]
    nlinarith [norm_nonneg y]
  have hderlt : ‖3 * x ^ 2 + A‖ < 1 := hder.trans_lt hlt
  have ha : ‖27 * B - 18 * A * x‖ ≤ 1 :=
    norm_sub_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 27) hB)
      (norm_mul_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 18) hA) hx)
  have hb : ‖6 * A * x ^ 2 - 9 * B * x + 4 * A ^ 2‖ ≤ 1 := by
    refine norm_add_le_one_of_le_one (norm_sub_le_one_of_le_one ?_ ?_) ?_
    · exact norm_mul_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 6) hA) hx2
    · exact norm_mul_le_one_of_le_one (norm_mul_le_one_of_le_one (norm_ofNat_le_one 9) hB) hx
    · refine norm_mul_le_one_of_le_one (norm_ofNat_le_one 4) ?_
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hA
  have hid : 4 * A ^ 3 + 27 * B ^ 2 = (27 * B - 18 * A * x) * (x ^ 3 + A * x + B) +
      (6 * A * x ^ 2 - 9 * B * x + 4 * A ^ 2) * (3 * x ^ 2 + A) := by ring
  have hlt1 : ‖4 * A ^ 3 + 27 * B ^ 2‖ < 1 := by
    rw [hid]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans_lt hflt
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans_lt hderlt
  rw [hD] at hlt1
  exact lt_irrefl _ hlt1

open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
private lemma norm_sub_y_le_norm_sub_x_of_torsion [DecidableEq K] {A B : K} {N : ℕ}
    (hT : ∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y),
      N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1)
    {x₁ y₁ x₂ y₂ : K} (h₁ : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x₁ y₁)
    (h₂ : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x₂ y₂)
    (hP : N • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0)
    (hQ : N • (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0) (hx : x₁ ≠ x₂) :
    ‖y₁ - y₂‖ ≤ ‖x₁ - x₂‖ := by
  have hsum := Point.add_of_X_ne (h₁ := h₁) (h₂ := h₂) hx
  have h3 := hT _ _ _ (by rw [← hsum, smul_add, hP, hQ, add_zero])
  rw [short_addX_eq, slope_of_X_ne hx] at h3
  have hl : ‖(y₁ - y₂) / (x₁ - x₂)‖ ≤ 1 :=
    norm_le_one_of_norm_sq_sub_le_one (s := x₁ + x₂) (by rw [← sub_sub]; exact h3)
      (norm_add_le_one_of_le_one (hT _ _ h₁ hP) (hT _ _ h₂ hQ))
  have hne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have : y₁ - y₂ = (y₁ - y₂) / (x₁ - x₂) * (x₁ - x₂) := by field_simp
  rw [this, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hl


open WeierstrassCurve WeierstrassCurve.Affine in
variable {K : Type} [NormedField K] [IsUltrametricDist K] in
theorem _root_.GlobalTheory.torsion_points_distinct_mod_maximal_ideal : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (A B : K) (N : ℕ), ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖(2 : K)‖ = 1 → ‖4 * A ^ 3 + 27 * B ^ 2‖ = 1 → Odd N → (∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y), N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1) → ∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y), N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x ^ 3 + A * x + B‖ = 1 ∧ ∀ (x' y' : K) (h' : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x' y'), N • (WeierstrassCurve.Affine.Point.some x' y' h') = 0 → x ≠ x' → ‖x - x'‖ = 1 := by
  intro K _ _ _ A B N hA hB h2 hD hN hT x y h hP
  have hy1 := norm_y_eq_one_of_nsmul_eq_zero hA hB h2 hD hN hT h hP
  refine ⟨?_, ?_⟩
  · rw [← short_equation_of_nonsingular h, norm_pow, hy1, one_pow]
  · intro x' y' h' hP' hx
    have hxx : ‖x - x'‖ ≤ 1 := norm_sub_le_one_of_le_one (hT _ _ h hP) (hT _ _ h' hP')
    refine le_antisymm hxx (not_lt.mp fun hlt => ?_)
    have hsub := norm_sub_y_le_norm_sub_x_of_torsion hT h h' hP hP' hx
    have hnegP : N • Point.some x' _
        (((⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.nonsingular_neg x' y').mpr h') = 0 := by
      rw [← Point.neg_some h', smul_neg, hP', neg_zero]
    have hadd := norm_sub_y_le_norm_sub_x_of_torsion hT h _ hP hnegP hx
    rw [short_negY_eq, sub_neg_eq_add] at hadd
    have h2y : ‖2 * y‖ < 1 := by
      have : 2 * y = (y - y') + (y + y') := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hsub.trans_lt hlt) (hadd.trans_lt hlt))
    rw [norm_mul, h2, hy1, one_mul] at h2y
    exact lt_irrefl _ h2y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateChartBallDistortion
section
open MeasureTheory Filter Topology Metric Set

namespace GlobalTheory

theorem translate_chart_ball_distortion
    (V M G : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup M]
    [NormedSpace ℝ M] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (e : V → G)
    (m : G → M) (ι : V →ₗᵢ[ℝ] M) (L : G → M →L[ℝ] M) (he : Continuous e) (he0 : e 0 = 1)
    (hd : HasStrictFDerivAt (fun x => m (e x)) ι.toContinuousLinearMap 0)
    (hL : ContinuousAt L 1) (hL1 : L 1 = ContinuousLinearMap.id ℝ M)
    (hm : ∀ g h, m (g * h) = L g (m h))
    (hopen : ∀ r : ℝ, 0 < r → e '' ball 0 r ∈ 𝓝 (1 : G)) (κ : ℝ) (hκ : 1 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ ball (0 : V) δ, ∀ r ∈ Ioo (0 : ℝ) δ,
      (fun g => e x * g) '' (e '' ball 0 r) ⊆ e '' ball x (κ * r) ∧
      e '' ball x r ⊆ (fun g => e x * g) '' (e '' ball 0 (κ * r)) := by
  set ε : ℝ := (κ - 1) / (2 * (3 + 2 * κ)) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  have hε1 : ε < 1 / 4 := by
    rw [hε, div_lt_iff₀ (by linarith)]
    linarith
  have hκε : (1 + ε) ^ 2 < κ * (1 - ε) ^ 2 := by
    have h3 : ε * (3 + 2 * κ) = (κ - 1) / 2 := by
      rw [hε]
      field_simp
    nlinarith [mul_pos (sub_pos.mpr hκ) (mul_pos hε0 hε0)]
  obtain ⟨η, hη0, hη⟩ := Metric.eventually_nhds_iff.mp (hd.isLittleO.bound hε0)
  have hD : ∀ a b : V, ‖a‖ < η → ‖b‖ < η →
      ‖m (e a) - m (e b) - ι (a - b)‖ ≤ ε * ‖a - b‖ := by
    intro a b ha hb
    have h := @hη (a, b) (by
      simp only [Prod.dist_eq, dist_zero_right]
      exact max_lt ha hb)
    simpa using h
  have hLc : ContinuousAt (fun x => L (e x)) 0 := hL.comp_of_eq he.continuousAt he0
  obtain ⟨η2, hη20, hη2⟩ := Metric.continuousAt_iff.mp hLc ε hε0
  have hLx : ∀ x : V, ‖x‖ < η2 → ∀ v : M, ‖L (e x) v - v‖ ≤ ε * ‖v‖ := by
    intro x hx v
    have h1 := hη2 (by rwa [dist_zero_right] : dist x 0 < η2)
    simp only [he0, hL1, dist_eq_norm] at h1
    have h2 := (L (e x) - ContinuousLinearMap.id ℝ M).le_opNorm v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right h1.le (norm_nonneg v))
  have hU : e '' ball 0 η ∈ 𝓝 (1 : G) := hopen η hη0
  have hφ : Continuous (fun p : V × V => e p.1 * e p.2) :=
    (he.comp continuous_fst).mul (he.comp continuous_snd)
  have hψ : Continuous (fun p : V × V => (e p.1)⁻¹ * e p.2) :=
    (he.comp continuous_fst).inv.mul (he.comp continuous_snd)
  have hφU : (fun p : V × V => e p.1 * e p.2) ⁻¹' (e '' ball 0 η) ∈ 𝓝 ((0 : V), (0 : V)) :=
    hφ.continuousAt.preimage_mem_nhds (by simpa [he0] using hU)
  have hψU : (fun p : V × V => (e p.1)⁻¹ * e p.2) ⁻¹' (e '' ball 0 η) ∈
      𝓝 ((0 : V), (0 : V)) :=
    hψ.continuousAt.preimage_mem_nhds (by simpa [he0] using hU)
  obtain ⟨η3, hη30, hη3⟩ := Metric.mem_nhds_iff.mp hφU
  obtain ⟨η4, hη40, hη4⟩ := Metric.mem_nhds_iff.mp hψU
  have hφ' : ∀ a b : V, ‖a‖ < η3 → ‖b‖ < η3 → ∃ z, ‖z‖ < η ∧ e z = e a * e b := by
    intro a b ha hb
    have hab : (a, b) ∈ ball ((0 : V), (0 : V)) η3 := by
      rw [mem_ball, Prod.dist_eq]
      simp only [dist_zero_right]
      exact max_lt ha hb
    obtain ⟨z, hz, hze⟩ := hη3 hab
    exact ⟨z, mem_ball_zero_iff.mp hz, hze⟩
  have hψ' : ∀ a b : V, ‖a‖ < η4 → ‖b‖ < η4 → ∃ z, ‖z‖ < η ∧ e z = (e a)⁻¹ * e b := by
    intro a b ha hb
    have hab : (a, b) ∈ ball ((0 : V), (0 : V)) η4 := by
      rw [mem_ball, Prod.dist_eq]
      simp only [dist_zero_right]
      exact max_lt ha hb
    obtain ⟨z, hz, hze⟩ := hη4 hab
    exact ⟨z, mem_ball_zero_iff.mp hz, hze⟩
  have h0η : ‖(0 : V)‖ < η := by simpa using hη0
  refine ⟨min (η / 2) (min η2 (min (η3 / 2) (η4 / 2))),
    lt_min (by linarith) (lt_min hη20 (lt_min (by linarith) (by linarith))), ?_⟩
  intro x hx r hr
  rw [mem_ball_zero_iff] at hx
  obtain ⟨hr0, hrδ⟩ := hr
  have b1 : ‖x‖ < η / 2 := lt_of_lt_of_le hx (min_le_left _ _)
  have b2 : ‖x‖ < η2 := lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_left _ _))
  have b3 : ‖x‖ < η3 / 2 := lt_of_lt_of_le hx
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have b4 : ‖x‖ < η4 / 2 := lt_of_lt_of_le hx
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have r1 : r < η / 2 := lt_of_lt_of_le hrδ (min_le_left _ _)
  have r3 : r < η3 / 2 := lt_of_lt_of_le hrδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have r4 : r < η4 / 2 := lt_of_lt_of_le hrδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hmx : ∀ y, m (e x * e y) - m (e x) = L (e x) (m (e y) - m (e 0)) := by
    intro y
    rw [map_sub, he0, ← hm, ← hm, mul_one]
  constructor
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [mem_ball_zero_iff] at hy
    obtain ⟨z, hz, hze⟩ := hφ' x y (by linarith) (by linarith)
    refine ⟨z, ?_, hze⟩
    rw [mem_ball, dist_eq_norm]
    have e1 := hD z x hz (by linarith)
    have e2 := hD y 0 (by linarith) h0η
    rw [sub_zero] at e2
    have e3 := hLx x b2 (m (e y) - m (e 0))
    rw [hze, hmx y] at e1
    have nι : ‖ι (z - x)‖ = ‖z - x‖ := ι.norm_map _
    have nιy : ‖ι y‖ = ‖y‖ := ι.norm_map _
    set v := m (e y) - m (e 0) with hv
    have t1 : ‖z - x‖ ≤ ‖L (e x) v‖ + ε * ‖z - x‖ := by
      have h := norm_sub_norm_le (ι (z - x)) (L (e x) v)
      have h' : ‖ι (z - x) - L (e x) v‖ = ‖L (e x) v - ι (z - x)‖ := norm_sub_rev _ _
      linarith
    have t2 : ‖L (e x) v‖ ≤ (1 + ε) * ‖v‖ := by
      have h := norm_sub_norm_le (L (e x) v) v
      linarith
    have t3 : ‖v‖ ≤ (1 + ε) * ‖y‖ := by
      have h := norm_sub_norm_le v (ι y)
      linarith
    have k1 : (1 - ε) * ‖z - x‖ ≤ (1 + ε) ^ 2 * ‖y‖ := by
      have := mul_le_mul_of_nonneg_left t3 (by linarith : (0 : ℝ) ≤ 1 + ε)
      linarith only [t1, t2, this]
    have k2 : (1 + ε) ^ 2 * ‖y‖ < (1 + ε) ^ 2 * r := mul_lt_mul_of_pos_left hy (by positivity)
    have k3 : (1 + ε) ^ 2 * r < κ * (1 - ε) ^ 2 * r := mul_lt_mul_of_pos_right hκε hr0
    have k4 : κ * (1 - ε) ^ 2 * r ≤ κ * (1 - ε) * r := by
      have h1 : (1 - ε) ^ 2 ≤ 1 - ε := by
        rw [sq]
        exact mul_le_of_le_one_left (by linarith) (by linarith)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by linarith)) hr0.le
    have k5 : (1 - ε) * ‖z - x‖ < (1 - ε) * (κ * r) := by linarith only [k1, k2, k3, k4]
    exact lt_of_mul_lt_mul_left k5 (by linarith)
  · rintro _ ⟨w, hw, rfl⟩
    rw [mem_ball, dist_eq_norm] at hw
    have hwx := norm_sub_norm_le w x
    obtain ⟨y, hyη, hye⟩ := hψ' x w (by linarith) (by linarith)
    have hexy : e w = e x * e y := by rw [hye, mul_inv_cancel_left]
    refine ⟨e y, ⟨y, ?_, rfl⟩, hexy.symm⟩
    rw [mem_ball_zero_iff]
    have e1 := hD w x (by linarith) (by linarith)
    have e2 := hD y 0 hyη h0η
    rw [sub_zero] at e2
    have e3 := hLx x b2 (m (e y) - m (e 0))
    rw [hexy, hmx y] at e1
    have nι : ‖ι (w - x)‖ = ‖w - x‖ := ι.norm_map _
    have nιy : ‖ι y‖ = ‖y‖ := ι.norm_map _
    set v := m (e y) - m (e 0) with hv
    have s1 : ‖L (e x) v‖ ≤ (1 + ε) * ‖w - x‖ := by
      have h := norm_sub_norm_le (L (e x) v) (ι (w - x))
      linarith
    have s2 : (1 - ε) * ‖v‖ ≤ ‖L (e x) v‖ := by
      have h := norm_sub_norm_le v (L (e x) v)
      have h' : ‖v - L (e x) v‖ = ‖L (e x) v - v‖ := norm_sub_rev _ _
      linarith
    have s3 : (1 - ε) * ‖y‖ ≤ ‖v‖ := by
      have h := norm_sub_norm_le (ι y) v
      have h' : ‖ι y - v‖ = ‖v - ι y‖ := norm_sub_rev _ _
      linarith
    have k1 : (1 - ε) ^ 2 * ‖y‖ ≤ (1 - ε) * ‖v‖ := by
      have := mul_le_mul_of_nonneg_left s3 (by linarith : (0 : ℝ) ≤ 1 - ε)
      linarith only [this]
    have k2 : (1 + ε) * ‖w - x‖ < (1 + ε) * r := mul_lt_mul_of_pos_left hw (by linarith)
    have k3 : (1 + ε) * r ≤ (1 + ε) ^ 2 * r := by
      linarith only [mul_pos hε0 hr0, mul_pos (mul_pos hε0 hε0) hr0]
    have k4 : (1 + ε) ^ 2 * r < κ * (1 - ε) ^ 2 * r := mul_lt_mul_of_pos_right hκε hr0
    have k5 : (1 - ε) ^ 2 * ‖y‖ < (1 - ε) ^ 2 * (κ * r) := by
      linarith only [k1, s2, s1, k2, k3, k4]
    exact lt_of_mul_lt_mul_left k5 (pow_pos (by linarith) 2).le

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationMapAlgEquivEqOfLeOneIffIsIntegral
section
open scoped NNReal TensorProduct

namespace GlobalTheory

theorem valuation_map_algEquiv_eq_of_le_one_iff_isIntegral (R Ω : Type) [CommRing R] [Nontrivial R]
    [Field Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω]
    (hinj : Function.Injective (algebraMap R Ω)) (v : Valuation Ω ℝ≥0)
    (hv : ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x) (g : Ω ≃ₐ[R] Ω) (x : Ω) : v (g x) = v x := by
  have hle : ∀ a b : Ω, v (g a) ≤ v (g b) ↔ v a ≤ v b := by
    intro a b
    by_cases hb : b = 0
    · subst hb
      simp
    · have hgb : g b ≠ 0 := by simpa using hb
      have hvb : 0 < v b := by simpa [pos_iff_ne_zero] using hb
      have hvgb : 0 < v (g b) := by simpa [pos_iff_ne_zero] using hgb
      have h1 : v (a / b) ≤ 1 ↔ v a ≤ v b := by rw [map_div₀, div_le_one hvb]
      have h2 : v (g (a / b)) ≤ 1 ↔ v (g a) ≤ v (g b) := by
        rw [map_div₀ g, map_div₀, div_le_one hvgb]
      rw [← h1, ← h2, hv, hv, isIntegral_algEquiv]
  have hlt : ∀ a b : Ω, v (g a) < v (g b) ↔ v a < v b := by
    intro a b
    rw [← not_le, ← not_le, hle]
  obtain ⟨k, l, hkl, heq⟩ : ∃ k l : ℕ, k < l ∧ (g ^ k) x = (g ^ l) x := by
    obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) x
    have hmap : p.map (algebraMap R Ω) ≠ 0 := by
      rwa [Ne, Polynomial.map_eq_zero_iff hinj]
    have hsub : Set.range (fun k : ℕ => (g ^ k) x) ⊆ p.rootSet Ω := by
      rintro _ ⟨k, rfl⟩
      rw [Polynomial.mem_rootSet']
      refine ⟨hmap, ?_⟩
      rw [Polynomial.aeval_algEquiv]
      simp [hpx]
    have hfin := (Polynomial.rootSet_finite p Ω).subset hsub
    have hni : ¬ Function.Injective (fun k : ℕ => (g ^ k) x) := fun hi =>
      Set.infinite_range_of_injective hi hfin
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a, b, h, hab⟩
    · exact ⟨b, a, h, hab.symm⟩
  have hstep : ∀ k : ℕ, (g ^ (k + 1)) x = g ((g ^ k) x) := by
    intro k
    rw [pow_succ', AlgEquiv.mul_apply]
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hs : ∀ n : ℕ, v ((g ^ (n + 1)) x) < v ((g ^ n) x) := by
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        rw [hstep (n + 1), hstep n, hlt]
        rw [hstep n] at ih
        simpa [hstep] using ih
    have hanti : StrictAnti (fun n : ℕ => v ((g ^ n) x)) := strictAnti_nat_of_succ_lt hs
    have := hanti hkl
    simp only [heq] at this
    exact lt_irrefl _ this
  · have hs : ∀ n : ℕ, v ((g ^ n) x) < v ((g ^ (n + 1)) x) := by
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        rw [hstep (n + 1), hstep n, hlt]
        rw [hstep n] at ih
        simpa [hstep] using ih
    have hmono : StrictMono (fun n : ℕ => v ((g ^ n) x)) := strictMono_nat_of_lt_succ hs
    have := hmono hkl
    simp only [heq] at this
    exact lt_irrefl _ this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationZetaSubOnePowTotient
section
namespace GlobalTheory

open Polynomial

theorem valuationSubring_pow_sub_one_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {x : Ω}
    (hx : A.valuation x ≤ 1) (k : ℕ) :
    A.valuation (x ^ k - 1) ≤ A.valuation (x - 1) := by
  have h : x ^ k - 1 = (∑ i ∈ Finset.range k, x ^ i) * (x - 1) := (geom_sum_mul x k).symm
  rw [h, map_mul]
  have hs : A.valuation (∑ i ∈ Finset.range k, x ^ i) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_pow]; exact pow_le_one' hx i
  exact mul_le_of_le_one_left' hs

theorem valuation_zeta_sub_one_pow_totient (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] (A : ValuationSubring Ω) (n : ℕ) (ζ : Ω) (hn : 1 ≤ n)
    (hζ : IsPrimitiveRoot ζ (l ^ n)) :
    A.valuation (ζ - 1) ^ (l ^ n).totient = A.valuation (l : Ω) := by
  have hN : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hv1 : ∀ {μ : Ω}, IsPrimitiveRoot μ (l ^ n) → A.valuation μ ≤ 1 := by
    intro μ hμ
    have h1 : A.valuation μ ^ (l ^ n) = 1 := by rw [← map_pow, hμ.pow_eq_one, map_one]
    exact (pow_eq_one_iff.1 h1 |>.resolve_right hN.ne').le
  have key : ∀ μ ∈ primitiveRoots (l ^ n) Ω, A.valuation (1 - μ) = A.valuation (ζ - 1) := by
    intro μ hμ
    rw [mem_primitiveRoots hN] at hμ
    rw [Valuation.map_sub_swap]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
    apply le_antisymm
    · rw [← hi]; exact valuationSubring_pow_sub_one_le A (hv1 hζ) i
    · rw [← hj]; exact valuationSubring_pow_sub_one_le A (hv1 hμ) j
  have hcyc := cyclotomic_eq_prod_X_sub_primitiveRoots hζ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : (l : Ω) = ∏ μ ∈ primitiveRoots (l ^ (k + 1)) Ω, (1 - μ) := by
    have := congrArg (eval 1) hcyc
    rw [eval_one_cyclotomic_prime_pow, eval_prod] at this
    simpa using this
  rw [h1, map_prod, Finset.prod_congr rfl key, Finset.prod_const, hζ.card_primitiveRoots]

end GlobalTheory
end

