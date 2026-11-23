module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0001
public import GroundTheory.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0017
public import GroundTheory.AutomorphicForms.DixmierMalliavinLineStage
public import GroundTheory.AutomorphicForms.Bundle0007
public import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection
public import GroundTheory.AutomorphicForms.UnitaryRepresentations.Integrated

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.CompactAbelianCharacters
section
set_option maxSynthPendingDepth 1

open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace GroundTheory.Automorphic.CompactAbelianFourier

noncomputable section

set_option linter.unusedSectionVars false

variable {C : Type*} [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
  [T2Space C]

section Metrizable

variable [SecondCountableTopology C] [MeasurableSpace C] [BorelSpace C]
  (μ : Measure C) [μ.IsHaarMeasure]

def transl (h : C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x => h * x) (measurePreserving_mul_left μ h)).toContinuousLinearMap

variable (ψ : C(C, ℝ))


end Metrizable

theorem exists_char_ne_one {g : C} (hg : g ≠ 1) : ∃ χ : C →ₜ* Circle, χ g ≠ 1 :=
  _root_.UpperTheory.Reformulated.B.CharactersSeparatePoints.exists_char_ne_one hg

theorem exists_char_ne {x y : C} (hxy : x ≠ y) : ∃ χ : C →ₜ* Circle, χ x ≠ χ y := by
  obtain ⟨χ, hχ⟩ := exists_char_ne_one (g := x * y⁻¹) (fun h => hxy (mul_inv_eq_one.1 h))
  refine ⟨χ, fun h => hχ ?_⟩
  rw [map_mul, map_inv, h, mul_inv_cancel]

def charCM (χ : C →ₜ* Circle) : C(C, ℂ) := ⟨fun x => (χ x : ℂ), continuous_subtype_val.comp χ.continuous⟩

theorem charCM_apply (χ : C →ₜ* Circle) (x : C) : charCM χ x = (χ x : ℂ) := rfl

theorem charCM_mul (χ χ' : C →ₜ* Circle) : charCM (χ * χ') = charCM χ * charCM χ' := by
  ext x
  simp [charCM_apply]

theorem charCM_one : charCM (1 : C →ₜ* Circle) = 1 := by
  ext x
  simp [charCM_apply]

theorem star_charCM (χ : C →ₜ* Circle) : star (charCM χ) = charCM χ⁻¹ := by
  ext x
  change conj ((χ x : Circle) : ℂ) = (((χ x)⁻¹ : Circle) : ℂ)
  rw [Circle.coe_inv_eq_conj]

def charAlgebra : StarSubalgebra ℂ C(C, ℂ) :=
  { (Submodule.span ℂ (Set.range (charCM (C := C)))).toSubalgebra
      (Submodule.subset_span ⟨1, charCM_one⟩)
      (fun a b ha hb => by
        induction ha using Submodule.span_induction with
        | mem x hx =>
          induction hb using Submodule.span_induction with
          | mem y hy =>
            obtain ⟨χ, rfl⟩ := hx
            obtain ⟨χ', rfl⟩ := hy
            exact Submodule.subset_span ⟨χ * χ', charCM_mul χ χ'⟩
          | zero => rw [mul_zero]; exact Submodule.zero_mem _
          | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
          | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
        | zero => rw [zero_mul]; exact Submodule.zero_mem _
        | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx) with
    star_mem' := fun {a} ha => by
      change a ∈ Submodule.span ℂ (Set.range (charCM (C := C))) at ha
      change star a ∈ Submodule.span ℂ (Set.range (charCM (C := C)))
      induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨χ, rfl⟩ := hx
        exact Submodule.subset_span ⟨χ⁻¹, (star_charCM χ).symm⟩
      | zero => rw [star_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx }

theorem charAlgebra_separatesPoints : (charAlgebra (C := C)).SeparatesPoints := by
  intro x y hxy
  obtain ⟨χ, hχ⟩ := exists_char_ne hxy
  exact ⟨charCM χ, ⟨charCM χ, Submodule.subset_span ⟨χ, rfl⟩, rfl⟩, fun h => hχ (Circle.coe_injective h)⟩

theorem span_charCM_dense :
    (Submodule.span ℂ (Set.range (charCM (C := C)))).topologicalClosure = ⊤ := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (charAlgebra_separatesPoints (C := C))
  rw [eq_top_iff]
  intro f _
  have hf : f ∈ (charAlgebra (C := C)).topologicalClosure := by rw [h]; trivial
  exact hf

section L2

variable [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure]

variable [IsProbabilityMeasure μ]

end L2

end

end GroundTheory.Automorphic.CompactAbelianFourier
end

-- bundled from GroundTheory.AutomorphicForms.DixmierMalliavinLineBounds
section
namespace GroundTheory.Automorphic

open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform

set_option linter.unusedSectionVars false

noncomputable section

namespace LineKernel

theorem tsupport_iteratedDeriv_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (m : ℕ) : tsupport (iteratedDeriv m f) ⊆ tsupport f := by
  induction m with
  | zero => simp
  | succ m ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

theorem iteratedDeriv_eq_of_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℕ → ℝ → E} (h : ∀ m, deriv (Φ m) = Φ (m + 1)) (m : ℕ) : iteratedDeriv m (Φ 0) = Φ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [iteratedDeriv_succ, ih, h]

theorem convolution_mul_eq_real (f g : ℝ → ℂ) : (f ⋆[mul ℂ ℂ] g) = (f ⋆[mul ℝ ℂ] g) := by
  funext x; simp only [convolution_def, mul_apply']

theorem iteratedDeriv_convolution {K g : ℝ → ℂ} (hK : LocallyIntegrable K) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (m : ℕ) :
    iteratedDeriv m (K ⋆[mul ℂ ℂ] g) = K ⋆[mul ℂ ℂ] iteratedDeriv m g := by
  have := iteratedDeriv_eq_of_deriv (Φ := fun m => K ⋆[mul ℂ ℂ] iteratedDeriv m g) (fun m => by
    funext x
    rw [convolution_mul_eq_real, convolution_mul_eq_real]
    rw [((hasCompactSupport_iteratedDeriv hgc m).hasDerivAt_convolution_right (mul ℝ ℂ) hK
      ((contDiff_iteratedDeriv_of_contDiff hg m).of_le (by simp)) x).deriv, ← iteratedDeriv_succ]) m
  simpa using this

theorem norm_convolution_le {K g : ℝ → ℂ} {B : ℝ} (hK : Integrable K) (hg : ∀ t, ‖g t‖ ≤ B)
    (x : ℝ) : ‖(K ⋆[mul ℂ ℂ] g) x‖ ≤ B * ∫ t, ‖K t‖ := by
  rw [convolution_mul, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun t => norm_nonneg _) (hK.norm.const_mul B)
    (Eventually.of_forall fun t => ?_))
  simp only [norm_mul]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hg _) (norm_nonneg _)

section Bounds

variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr

theorem integral_norm_KC_le_one (n : ℕ) : ∫ t, ‖KC a r n t‖ ≤ 1 := by
  have : (fun t => ‖KC a r n t‖) = Kc a r n := by
    funext t; simp [KC, Complex.norm_real, abs_of_nonneg (Kc_nonneg ha hr n t)]
  rw [this]; exact integral_Kc_le_one ha hr n

theorem contDiff_ρ (n : ℕ) : ContDiff ℝ ∞ (ρ a r n) := by
  cases n with
  | zero => exact contDiff_ηC a r 0
  | succ n =>
    simp only [ρ]
    exact ContDiff.sum fun p _ => contDiff_const.mul
      (contDiff_iteratedDeriv_of_contDiff (contDiff_conv_ηC ha hr n) p)

theorem support_ρ_subset (n : ℕ) : support (ρ a r n) ⊆ Icc 0 (Rs r n) := by
  cases n with
  | zero =>
    intro t ht
    have : t ∈ Icc (r 0) (2 * r 0) := by
      by_contra h; exact ht (by simp [ρ, ηC, rem_eq_zero (hr 0) h])
    exact ⟨(hr 0).le.trans this.1, by simpa [Rs] using this.2⟩
  | succ n =>
    have hs : tsupport (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) ⊆ Icc 0 (Rs r (n + 1)) := by
      refine closure_minimal ?_ isClosed_Icc
      refine (support_convolution_subset (mul ℂ ℂ)).trans ?_
      have h1 : support (KC a r n) ⊆ Icc 0 (Rs r n) := fun t ht =>
        support_Kc_subset ha hr n (by simpa [KC] using ht)
      have h2 : support (ηC a r (n + 1)) ⊆ Icc (r (n + 1)) (2 * r (n + 1)) := fun t ht =>
        support_rem_subset (hr (n + 1)) (by simpa [ηC] using ht)
      refine (Set.add_subset_add h1 h2).trans ((Set.Icc_add_Icc_subset _ _ _ _).trans
        (Icc_subset_Icc (by linarith [hr (n + 1)]) (le_of_eq ?_)))
      simp [Rs, Finset.sum_range_succ]
    intro t ht
    by_contra h
    apply ht
    simp only [ρ]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [image_eq_zero_of_notMem_tsupport (fun h' => h (hs (tsupport_iteratedDeriv_subset p h'))),
      mul_zero]

theorem norm_iteratedDeriv_ηC (j q : ℕ) (t : ℝ) :
    ‖iteratedDeriv q (ηC a r j) t‖ = ‖iteratedDeriv q (rem (a j) (r j)) t‖ := by
  have := iteratedDeriv_ofReal (contDiff_rem (a j) (r j)) q
  show ‖iteratedDeriv q (fun t => ((rem (a j) (r j) t : ℝ) : ℂ)) t‖ = _
  rw [this, Complex.norm_real]

theorem norm_iteratedDeriv_ρ_succ_le (n m : ℕ) {B : ℕ → ℝ}
    (hB : ∀ q t, ‖iteratedDeriv q (rem (a (n + 1)) (r (n + 1))) t‖ ≤ B q) (t : ℝ) :
    ‖iteratedDeriv m (ρ a r (n + 1)) t‖ ≤
      ∑ p ∈ Finset.range (n + 2), coef a (n + 1) p * B (p + m) := by
  have hKi := (integrable_KC ha hr n).locallyIntegrable
  have hηc := contDiff_ηC a r (n + 1)
  have hηs := hasCompactSupport_ηC ha hr (n + 1)
  set Φ : ℕ → ℝ → ℂ := fun m u => ∑ p ∈ Finset.range (n + 2),
    (coef a (n + 1) p : ℂ) * (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m) (ηC a r (n + 1))) u
    with hΦ
  have h0 : ρ a r (n + 1) = Φ 0 := by
    funext u
    simp only [ρ, hΦ, add_zero, iteratedDeriv_convolution hKi hηc hηs]
  have hd : ∀ m, deriv (Φ m) = Φ (m + 1) := by
    intro m; funext x
    have hsum := HasDerivAt.sum (u := Finset.range (n + 2))
      (A := fun p u => (coef a (n + 1) p : ℂ) *
        (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m) (ηC a r (n + 1))) u)
      (A' := fun p => (coef a (n + 1) p : ℂ) *
        (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m + 1) (ηC a r (n + 1))) x) (x := x)
      (fun p _ => by
        refine HasDerivAt.const_mul _ ?_
        rw [convolution_mul_eq_real, convolution_mul_eq_real, iteratedDeriv_succ]
        exact (hasCompactSupport_iteratedDeriv hηs (p + m)).hasDerivAt_convolution_right
          (mul ℝ ℂ) hKi ((contDiff_iteratedDeriv_of_contDiff hηc _).of_le (by simp)) x)
    have e : Φ m = ∑ p ∈ Finset.range (n + 2), fun u => (coef a (n + 1) p : ℂ) *
        (KC a r n ⋆[mul ℂ ℂ] iteratedDeriv (p + m) (ηC a r (n + 1))) u := by
      funext u; simp [hΦ, Finset.sum_apply]
    rw [e, hsum.deriv]
    simp only [hΦ, add_assoc]
  rw [h0, iteratedDeriv_eq_of_deriv hd m]
  simp only [hΦ]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (coef_nonneg ha _ _)]
  refine mul_le_mul_of_nonneg_left ?_ (coef_nonneg ha _ _)
  have hB' : ∀ u, ‖iteratedDeriv (p + m) (ηC a r (n + 1)) u‖ ≤ B (p + m) := fun u => by
    rw [norm_iteratedDeriv_ηC ha hr]; exact hB _ _
  refine (norm_convolution_le (integrable_KC ha hr n) hB' t).trans ?_
  have h1 := integral_norm_KC_le_one ha hr n
  have h2 : 0 ≤ B (p + m) := (norm_nonneg _).trans (hB (p + m) 0)
  have h3 : 0 ≤ ∫ t, ‖KC a r n t‖ := integral_nonneg fun t => norm_nonneg _
  nlinarith

theorem fourier_KC_zero (ξ : ℝ) : 𝓕 (KC a r 0) ξ = khat (a 0) (r 0) ξ := rfl

theorem fourier_KC_succ (n : ℕ) (ξ : ℝ) :
    𝓕 (KC a r (n + 1)) ξ = 𝓕 (KC a r n) ξ * khat (a (n + 1)) (r (n + 1)) ξ := by
  rw [KC_succ ha hr n, fourier_mul_convolution_eq (f₂ := kC a r (n + 1)) (integrable_KC ha hr n)
    (integrable_kern (ha (n + 1)).le (hr (n + 1))).ofReal]
  rfl

theorem norm_fourier_KC_le_one (n : ℕ) (ξ : ℝ) : ‖𝓕 (KC a r n) ξ‖ ≤ 1 := by
  induction n with
  | zero => rw [fourier_KC_zero ha hr]; exact norm_khat_le_one (ha 0) (hr 0) ξ
  | succ n ih =>
    rw [fourier_KC_succ ha hr, norm_mul]
    exact mul_le_one₀ ih (norm_nonneg _) (norm_khat_le_one (ha _) (hr _) ξ)

theorem norm_fourier_KC_succ_sub_le (n : ℕ) (ξ : ℝ) :
    ‖𝓕 (KC a r (n + 1)) ξ - 𝓕 (KC a r n) ξ‖ ≤
      4 * π * r (n + 1) * |ξ| + exp (-a (n + 1) * r (n + 1)) := by
  rw [fourier_KC_succ ha hr, ← mul_sub_one, norm_mul]
  calc ‖𝓕 (KC a r n) ξ‖ * ‖khat (a (n + 1)) (r (n + 1)) ξ - 1‖
      ≤ 1 * (4 * π * r (n + 1) * |ξ| + exp (-a (n + 1) * r (n + 1))) :=
        mul_le_mul (norm_fourier_KC_le_one ha hr n ξ) (norm_khat_sub_one_le (ha _) (hr _) ξ)
          (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem abs_pow_mul_norm_fourier_KC_le (n m : ℕ) (hmn : m ≤ n + 1) (ξ : ℝ) :
    |ξ| ^ m * ‖𝓕 (KC a r n) ξ‖ ≤ ∏ j ∈ Finset.range m, (a j / π) := by
  induction n generalizing m with
  | zero =>
    interval_cases m
    · simpa using norm_fourier_KC_le_one ha hr 0 ξ
    · simpa [fourier_KC_zero ha hr] using abs_mul_norm_khat_le (ha 0) (hr 0) ξ
  | succ n ih =>
    rw [fourier_KC_succ ha hr, norm_mul]
    rcases Nat.lt_or_ge m (n + 2) with h | h
    · calc |ξ| ^ m * (‖𝓕 (KC a r n) ξ‖ * ‖khat (a (n + 1)) (r (n + 1)) ξ‖)
          ≤ |ξ| ^ m * (‖𝓕 (KC a r n) ξ‖ * 1) := by
            gcongr; exact norm_khat_le_one (ha _) (hr _) ξ
        _ ≤ _ := by rw [mul_one]; exact ih m (by omega)
    · obtain rfl : m = n + 2 := le_antisymm hmn h
      rw [Finset.prod_range_succ, pow_succ]
      calc |ξ| ^ (n + 1) * |ξ| * (‖𝓕 (KC a r n) ξ‖ * ‖khat (a (n + 1)) (r (n + 1)) ξ‖)
          = (|ξ| ^ (n + 1) * ‖𝓕 (KC a r n) ξ‖) * (|ξ| * ‖khat (a (n + 1)) (r (n + 1)) ξ‖) := by
            ring
        _ ≤ (∏ j ∈ Finset.range (n + 1), (a j / π)) * (a (n + 1) / π) :=
            mul_le_mul (ih (n + 1) le_rfl) (abs_mul_norm_khat_le (ha _) (hr _) ξ)
              (by positivity) (Finset.prod_nonneg fun j _ => div_nonneg (ha j).le pi_pos.le)

end Bounds

theorem coef_mono {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) (n p : ℕ) : coef a n p ≤ coef a (n + 1) p := by
  cases p with
  | zero => simp [coef]
  | succ p => simp only [coef]; linarith [div_nonneg (coef_nonneg ha n p) (ha n).le]

theorem coef_le_of {a β : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hβ0 : β 0 = 1) (hβp : ∀ p, 0 ≤ β p)
    (hβ : ∀ n p, 1 ≤ p → p ≤ n + 1 → (a n)⁻¹ * β (p - 1) ≤ (1 / 2) ^ (n + 1) * β p)
    (n p : ℕ) : coef a n p ≤ β p := by
  have key : ∀ n p, 1 ≤ p → coef a n p ≤ β p * (1 - (1 / 2) ^ n) := by
    intro n
    induction n with
    | zero =>
      intro p hp
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp [coef]
    | succ n ih =>
      intro p hp
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [coef]
      have h1 := ih (q + 1) (by omega)
      have h2 : coef a n q / a n ≤ (1 / 2) ^ (n + 1) * β (q + 1) := by
        rcases Nat.lt_or_ge n q with hq | hq
        · rw [coef_eq_zero a hq, zero_div]
          have := hβ n (q + 1) (by omega)
          have hb : 0 ≤ β (q + 1) := hβp _
          positivity
        · have hc : coef a n q ≤ β q := by
            rcases Nat.eq_zero_or_pos q with rfl | hq0
            · rw [coef_zero_right, hβ0]
            · have := ih q hq0
              have hbq : 0 ≤ β q := hβp q
              nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]
          have := hβ n (q + 1) (by omega) (by omega)
          simp only [Nat.add_sub_cancel] at this
          calc coef a n q / a n = (a n)⁻¹ * coef a n q := by ring
            _ ≤ (a n)⁻¹ * β q := mul_le_mul_of_nonneg_left hc (inv_nonneg.2 (ha n).le)
            _ ≤ _ := this
      calc coef a n (q + 1) + coef a n q / a n
          ≤ β (q + 1) * (1 - (1 / 2) ^ n) + (1 / 2) ^ (n + 1) * β (q + 1) := add_le_add h1 h2
        _ = β (q + 1) * (1 - (1 / 2) ^ (n + 1)) := by ring
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [coef_zero_right, hβ0]
  · have := key n p hp
    nlinarith [hβp p, pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

end LineKernel

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.HaarCosets
section
noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [IsFiniteMeasureOnCompacts μ]

theorem integral_eq_smul_finsum_coset (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    {f : G → E} (hf : HasCompactSupport f) (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    ∫ g, f g ∂μ = μ.real (K : Set G) • ∑ᶠ x : G ⧸ (K : Subgroup G), f x.out := by
  set S := (finite_image_mk_tsupport K hf).toFinset with hS
  have hmeas : ∀ g : G, MeasurableSet (g • (K : Set G)) := fun g =>
    (K.isOpen.smul g).measurableSet
  have hfin : ∀ g : G, μ (g • (K : Set G)) ≠ ∞ := fun g =>
    (hKc.smul g).measure_lt_top.ne
  have hvol : ∀ g : G, μ.real (g • (K : Set G)) = μ.real (K : Set G) := fun g => by
    simp [Measure.real, measure_smul]
  have hdec := eq_sum_indicator_coset K hf hK
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · calc ∫ g, f g ∂μ
        = ∫ g, ∑ x ∈ S, (x.out • (K : Set G)).indicator (fun _ => f x.out) g ∂μ :=
          integral_congr_ae (Eventually.of_forall fun g => by
            rw [congrFun hdec g, Finset.sum_apply])
      _ = ∑ x ∈ S, ∫ g, (x.out • (K : Set G)).indicator (fun _ => f x.out) g ∂μ :=
          integral_finsetSum _ fun x _ =>
            (integrable_indicator_iff (hmeas _)).2 (integrableOn_const (hfin _))
      _ = μ.real (K : Set G) • ∑ x ∈ S, f x.out := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [integral_indicator_const _ (hmeas _), hvol]
  · intro x hx
    rw [hS, Set.Finite.coe_toFinset]
    exact ⟨x.out, subset_tsupport f hx, QuotientGroup.out_eq' x⟩

end Integral

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.RealGroupsKAK
section
namespace GroundTheory.Automorphic

open Matrix Polynomial
open scoped MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_KAK (g : GL n 𝕜) :
    ∃ k₁ k₂ : unitaryGroup n 𝕜, ∃ a : n → ℝ, (∀ i, 0 < a i) ∧
      (g : Matrix n n 𝕜) = (k₁ : Matrix n n 𝕜) * diagonal (fun i => (a i : 𝕜)) * k₂ := by
  have hp : (polarPos g).PosDef := polarPos_posDef g
  have hH : (polarPos g).IsHermitian := hp.isHermitian
  refine ⟨⟨polarUnitary g, polarUnitary_mem g⟩ * hH.eigenvectorUnitary, star hH.eigenvectorUnitary,
    hH.eigenvalues, hp.eigenvalues_pos, ?_⟩
  have hs := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  calc (g : Matrix n n 𝕜) = polarUnitary g * polarPos g := (polarUnitary_mul_polarPos g).symm
    _ = polarUnitary g * ((hH.eigenvectorUnitary : Matrix n n 𝕜) *
          diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star (hH.eigenvectorUnitary : Matrix n n 𝕜)) := by
        rw [← hs]
    _ = _ := by simp [Matrix.mul_assoc, Function.comp_def]

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.UnitaryRepresentations
section
namespace GroundTheory.Automorphic

namespace UnitaryRep

open scoped InnerProductSpace
open ContinuousLinearMap Submodule

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

variable {π : UnitaryRep G H}

lemma IsInvariant.iSup {ι : Sort*} {V : ι → Submodule ℂ H} (h : ∀ i, π.IsInvariant (V i)) :
    π.IsInvariant (⨆ i, V i) := by
  intro g v hv
  exact Submodule.iSup_induction V (motive := fun x => π g x ∈ ⨆ i, V i) hv
    (fun i x hx => Submodule.mem_iSup_of_mem i (h i g x hx)) (by simp)
    (fun x y hx hy => by simpa using add_mem hx hy)


section decomposition

variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]

end decomposition

end UnitaryRep

end GroundTheory.Automorphic
end

