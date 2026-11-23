module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticOrderPrincipal
section
namespace GlobalTheory.CompanionTheory.QuadraticUnit

open Polynomial IsLocalRing

theorem norm_isUnit {R : Type} [CommRing R] [HenselianLocalRing R] (D : R) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (a b : R)
    (hab : IsUnit a ∨ IsUnit b) : IsUnit (a * a - D * (b * b)) := by
  have hmax : ∀ x : R, x ∈ maximalIdeal R ↔ ¬ IsUnit x := fun x => by
    rw [mem_maximalIdeal, mem_nonunits_iff]
  by_contra hnu
  have hm : a * a - D * (b * b) ∈ maximalIdeal R := (hmax _).2 hnu
  have hb : IsUnit b := by
    rcases hab with ha | hb
    · by_contra hb
      have hbm : b ∈ maximalIdeal R := (hmax b).2 hb
      have haa : a * a ∈ maximalIdeal R := by
        have he : a * a = (a * a - D * (b * b)) + D * (b * b) := by ring
        rw [he]
        exact add_mem hm (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hbm))
      exact (hmax _).1 haa (ha.mul ha)
    · exact hb
  obtain ⟨w, hw⟩ : ∃ w : R, b * w = 1 := ⟨_, hb.mul_val_inv⟩
  set c := a * w with hc
  have hcD : c * c - D ∈ maximalIdeal R := by
    have he : c * c - D = (a * a - D * (b * b)) * (w * w) := by
      have hw2 : D = D * ((b * w) * (b * w)) := by rw [hw]; ring
      rw [hc]
      nth_rewrite 1 [hw2]
      ring
    rw [he]
    exact Ideal.mul_mem_right _ _ hm
  have hcc : IsUnit (c * c) := by
    by_contra hcc
    have hDm : D ∈ maximalIdeal R := by
      have he : D = c * c - (c * c - D) := by ring
      rw [he]
      exact sub_mem ((hmax _).2 hcc) hcD
    exact (hmax _).1 hDm hD
  have hcu : IsUnit c := isUnit_of_mul_isUnit_left hcc
  obtain ⟨e, he, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C D) (monic_X_pow_sub_C D two_ne_zero) c
    (by simpa [sq] using hcD) (by simpa [derivative_X_pow, one_add_one_eq_two] using h2.mul hcu)
  apply hns
  refine ⟨e, ?_⟩
  have := he.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at this
  linear_combination -this

theorem isUnit_add_mul {R O : Type} [CommRing R] [HenselianLocalRing R] [CommRing O]
    (ι : R →+* O) (δ : O) (D : R) (hδ : δ * δ = ι D) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (a b : R)
    (hab : IsUnit a ∨ IsUnit b) : IsUnit (ι a + ι b * δ) := by
  have hn := (norm_isUnit D hD h2 hns a b hab).map ι
  have he : (ι a + ι b * δ) * (ι a - ι b * δ) = ι (a * a - D * (b * b)) := by
    rw [map_sub, map_mul, map_mul, map_mul, ← hδ]
    ring
  rw [← he] at hn
  exact isUnit_of_mul_isUnit_left hn

theorem exists_eq_mul_isUnit {R O : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CommRing O] (ι : R →+* O) (δ : O) (D : R) (hδ : δ * δ = ι D)
    (hspan : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (y : O) :
    ∃ (g : R) (u : O), IsUnit u ∧ y = ι g * u := by
  obtain ⟨p, q, rfl⟩ := hspan y
  rcases ValuationRing.dvd_total p q with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · refine ⟨p, 1 + ι r * δ, ?_, by rw [map_mul]; ring⟩
    simpa using isUnit_add_mul ι δ D hδ hD h2 hns 1 r (Or.inl isUnit_one)
  · refine ⟨q, ι r + δ, ?_, by rw [map_mul]; ring⟩
    simpa using isUnit_add_mul ι δ D hδ hD h2 hns r 1 (Or.inr isUnit_one)

theorem isPrincipalIdealRing_of_nonsquare_unit :
    ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
      [CommRing O] (ι : R →+* O) (δ : O) (D : R), δ * δ = ι D →
      (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) →
      IsUnit D → IsUnit (2 : R) → (¬ ∃ e : R, D = e * e) → IsPrincipalIdealRing O := by
  intro R O _ _ _ _ _ ι δ D hδ hspan _ hD h2 hns
  refine ⟨fun I => ⟨?_⟩⟩
  obtain ⟨g₀, hg₀⟩ := (IsPrincipalIdealRing.principal (Ideal.comap ι I)).principal
  have hg₀I : ι g₀ ∈ I := by
    have hmem : g₀ ∈ Ideal.comap ι I := by
      rw [hg₀]
      exact Submodule.mem_span_singleton_self g₀
    exact Ideal.mem_comap.1 hmem
  refine ⟨ι g₀, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).2 hg₀I)⟩
  intro y hy
  obtain ⟨g, u, hu, rfl⟩ := exists_eq_mul_isUnit ι δ D hδ hspan hD h2 hns y
  have hg : g ∈ Ideal.comap ι I := by
    rw [Ideal.mem_comap]
    have he : ι g = ι g * u * ↑hu.unit⁻¹ := by rw [mul_assoc, hu.mul_val_inv, mul_one]
    rw [he]
    exact I.mul_mem_right _ hy
  rw [hg₀] at hg
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hg
  refine Ideal.mem_span_singleton.2 ⟨ι r * u, ?_⟩
  rw [← hr, smul_eq_mul, map_mul]
  ring

end GlobalTheory.CompanionTheory.QuadraticUnit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VandermondeSeparation
section
namespace GlobalTheory.CompanionTheory.ExpSums


open Matrix in
theorem vandermonde_separation (r : ℕ) (α : Fin r → ℂ) (hα : Function.Injective α) :
    ∃ C : ℝ, ∀ (c : Fin r → ℂ) (i : Fin r),
      ‖c i‖ ≤ C * ∑ s : Fin r, ‖∑ k, c k * α k ^ (s : ℕ)‖ := by
  classical
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin r) (Fin r) ℂ, V = Matrix.vandermonde α := ⟨_, rfl⟩
  have hdet : IsUnit V.det := by
    rw [isUnit_iff_ne_zero, hV]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hα
  refine ⟨∑ s : Fin r, ∑ j : Fin r, ‖V⁻¹ s j‖, ?_⟩
  intro c i
  have hsum : ∀ s : Fin r, Matrix.vecMul c V s = ∑ k, c k * α k ^ (s : ℕ) := by
    intro s
    simp [Matrix.vecMul, dotProduct, hV, Matrix.vandermonde_apply]
  have hc : c = Matrix.vecMul (Matrix.vecMul c V) V⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
  have hC : ∀ s : Fin r, ‖V⁻¹ s i‖ ≤ ∑ s : Fin r, ∑ j : Fin r, ‖V⁻¹ s j‖ := fun s =>
    (Finset.single_le_sum (f := fun j => ‖V⁻¹ s j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ i)).trans
    (Finset.single_le_sum (f := fun s => ∑ j, ‖V⁻¹ s j‖)
      (fun s _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ s))
  calc ‖c i‖ = ‖Matrix.vecMul (Matrix.vecMul c V) V⁻¹ i‖ := by rw [← hc]
    _ = ‖∑ s, Matrix.vecMul c V s * V⁻¹ s i‖ := rfl
    _ ≤ ∑ s, ‖Matrix.vecMul c V s * V⁻¹ s i‖ := norm_sum_le _ _
    _ = ∑ s, ‖Matrix.vecMul c V s‖ * ‖V⁻¹ s i‖ := by simp_rw [norm_mul]
    _ ≤ ∑ s, ‖Matrix.vecMul c V s‖ * ∑ s : Fin r, ∑ j : Fin r, ‖V⁻¹ s j‖ :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hC s) (norm_nonneg _)
    _ = (∑ s : Fin r, ∑ j : Fin r, ‖V⁻¹ s j‖) * ∑ s : Fin r, ‖∑ k, c k * α k ^ (s : ℕ)‖ := by
      rw [← Finset.sum_mul, mul_comm]
      congr 1
      exact Finset.sum_congr rfl fun s _ => by rw [hsum]

end GlobalTheory.CompanionTheory.ExpSums
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedAntitoneLastNonpos
section
namespace GlobalTheory.CompanionTheory.Inequalities

theorem weighted_antitone_last_nonpos : ∀ (h : ℕ) (d e : Fin h → ℝ), 2 ≤ h → (∀ i, 0 < d i) →
    Antitone e → ∑ i, d i * e i = 0 →
    ∃ j : Fin h, 0 < j.val ∧ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i ≤ 0 := by
  intro h d e hh hd he hs
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 2 := ⟨h - 2, by omega⟩
  refine ⟨Fin.last (n + 1), by simp, ?_⟩
  have hf : Finset.univ.filter (fun i : Fin (n + 2) => Fin.last (n + 1) ≤ i)
      = {Fin.last (n + 1)} := by
    ext i
    simp [Fin.last_le_iff]
  rw [hf, Finset.sum_singleton]
  have hle : (∑ i, d i) * e (Fin.last (n + 1)) ≤ 0 := by
    rw [Finset.sum_mul, ← hs]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (he (Fin.le_last i)) (hd i).le
  have hpos : 0 < ∑ i, d i :=
    Finset.sum_pos (fun i _ => hd i) ⟨Fin.last _, Finset.mem_univ _⟩
  have hel : e (Fin.last (n + 1)) ≤ 0 := by
    by_contra hc
    exact absurd (mul_pos hpos (not_le.mp hc)) (not_lt.mpr hle)
  exact mul_nonpos_of_nonneg_of_nonpos (hd _).le hel

end GlobalTheory.CompanionTheory.Inequalities
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WirtingerCombinationNeZero
section
namespace GlobalTheory.CompanionTheory.Unitary

theorem wirtinger_combination_ne_zero : ∀ (χ : ℂ → ℂ), Continuous χ → (∀ z w, χ (z + w) = χ z * χ w) →
    (∀ z, ‖χ z‖ = 1) → (∃ z, χ z ≠ 1) → ∀ (D : ℂ → ℂ),
    (∀ z, HasDerivAt (fun t : ℝ => χ (t * z)) (D z) 0) →
    ∀ β : ℂ, β ≠ 0 → D β - Complex.I * D (β * Complex.I) ≠ 0 := by
  intro χ _ hmul hnorm hnt D hD β hβ
  have χ0 : χ 0 = 1 := by
    have h1 := hmul 0 0
    rw [add_zero] at h1
    have hne : χ 0 ≠ 0 := by
      intro h
      have h2 := hnorm 0
      rw [h, norm_zero] at h2
      exact zero_ne_one h2
    exact mul_left_cancel₀ hne (h1.symm.trans (mul_one (χ 0)).symm)
  have hf0 : ∀ z, χ (((0 : ℝ) : ℂ) * z) = 1 := by
    intro z
    simp [χ0]
  have hre : ∀ w, (D w).re = 0 := by
    intro w
    have h1 := (hD w).mul (hD w).star
    have hconst : ((fun t : ℝ => χ (t * w)) * fun t : ℝ => star (χ (t * w))) = fun _ => (1 : ℂ) := by
      funext t
      simp only [Pi.mul_apply]
      rw [← starRingEnd_apply, RCLike.mul_conj, hnorm]
      simp
    rw [hconst] at h1
    have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
    rw [hf0] at h2
    simp only [star_one, mul_one, one_mul] at h2
    have h3 := congrArg Complex.re h2
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h3
    linarith
  have hadd : ∀ z w, D (z + w) = D z + D w := by
    intro z w
    have h1 := (hD z).mul (hD w)
    have hfun : ((fun t : ℝ => χ (t * z)) * fun t : ℝ => χ (t * w)) = fun t : ℝ => χ (t * (z + w)) := by
      funext t
      simp only [Pi.mul_apply]
      rw [mul_add, hmul]
    rw [hfun, hf0, hf0, mul_one, one_mul] at h1
    exact (hD (z + w)).unique h1
  have hsmul : ∀ (r : ℝ) (z : ℂ), D (r * z) = r * D z := by
    intro r z
    have hr : HasDerivAt (fun t : ℝ => r * t) r 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul r
    have hz : HasDerivAt (fun t : ℝ => χ (t * z)) (D z) ((fun t : ℝ => r * t) 0) := by
      simp only [mul_zero]
      exact hD z
    have h1 := HasDerivAt.scomp (h := fun t : ℝ => r * t) (0 : ℝ) hz hr
    have hfun : ((fun t : ℝ => χ (t * z)) ∘ fun t : ℝ => r * t) = fun t : ℝ => χ (t * (r * z)) := by
      funext t
      simp only [Function.comp]
      congr 1
      push_cast
      ring
    rw [hfun] at h1
    rw [(hD (r * z)).unique h1, Complex.real_smul]
  have hzero : (∀ z, D z = 0) → False := by
    intro h0
    obtain ⟨z, hz⟩ := hnt
    apply hz
    have hder : ∀ s : ℝ, HasDerivAt (fun t : ℝ => χ (t * z)) 0 s := by
      intro s
      have h1 : HasDerivAt (fun t : ℝ => χ (((t - s : ℝ) : ℂ) * z)) (D z) s :=
        HasDerivAt.comp_sub_const (f := fun t : ℝ => χ (t * z)) s s (by rw [sub_self]; exact hD z)
      have h2 := h1.const_mul (χ (s * z))
      have hfun : (fun t : ℝ => χ (s * z) * χ (((t - s : ℝ) : ℂ) * z)) = fun t : ℝ => χ (t * z) := by
        funext t
        rw [← hmul]
        congr 1
        push_cast
        ring
      rw [hfun, h0, mul_zero] at h2
      exact h2
    have hc := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt) (fun s => (hder s).deriv) 1 0
    simp only [Complex.ofReal_one, one_mul] at hc
    rw [hc, hf0]
  intro hcomb
  have ha : D β = Complex.I * D (β * Complex.I) := sub_eq_zero.mp hcomb
  have hb0 : D (β * Complex.I) = 0 := by
    apply Complex.ext
    · exact hre _
    · have h1 := congrArg Complex.re ha
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, hre] at h1
      simp only [Complex.zero_im]
      linarith
  have ha0 : D β = 0 := by rw [ha, hb0, mul_zero]
  apply hzero
  intro z
  have hz : z = ((z / β).re : ℂ) * β + ((z / β).im : ℂ) * (β * Complex.I) := by
    have e : z = (z / β) * β := by field_simp
    conv_lhs => rw [e, ← Complex.re_add_im (z / β)]
    ring
  rw [hz, hadd, hsmul, hsmul, ha0, hb0, mul_zero, mul_zero, add_zero]

end GlobalTheory.CompanionTheory.Unitary
end

