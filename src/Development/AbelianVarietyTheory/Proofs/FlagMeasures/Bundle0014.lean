module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfAdjointEqAlgebraMapOfCommuteIrreducible
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem selfAdjoint_eq_algebraMap_of_commute_irreducible {G H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : G → (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ u ∈ S, π g u ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ g, Commute A (π g)) :
    ∃ r : ℝ, A = algebraMap ℝ (H →L[ℂ] H) r := by
  classical
  rcases subsingleton_or_nontrivial H with hH | hH
  · refine ⟨0, ?_⟩
    ext u
    simp [Subsingleton.elim u 0]
  obtain ⟨r, hr⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) A hA
  have hsub : ∀ s ∈ spectrum ℝ A, s = r := by
    intro s hs
    by_contra hne
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ spectrum ℝ A, ∃ b ∈ spectrum ℝ A, a < b := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨s, hs, r, hr, h⟩
      · exact ⟨r, hr, s, hs, h⟩
    set c : ℝ := (a + b) / 2 with hc_def
    set f : ℝ → ℝ := fun x => max (c - x) 0 with hf_def
    set k : ℝ → ℝ := fun x => max (x - c) 0 with hk_def
    have hfk : (fun x => k x * f x) = (0 : ℝ → ℝ) := by
      funext x
      simp only [Pi.zero_apply, hf_def, hk_def]
      rcases le_total x c with h | h
      · rw [max_eq_right (by linarith : x - c ≤ 0), zero_mul]
      · rw [max_eq_right (by linarith : c - x ≤ 0), mul_zero]
    have hprod : cfc k A * cfc f A = 0 := by
      rw [← cfc_mul k f A, hfk, cfc_zero]
    have hF : cfc f A ≠ 0 := by
      intro h0
      have := (eqOn_of_cfc_eq_cfc (f := f) (g := 0) (a := A) (h0.trans (cfc_zero ℝ A).symm)) ha
      simp only [Pi.zero_apply, hf_def] at this
      have : c - a ≤ 0 := by
        rw [← this]; exact le_max_left _ _
      linarith
    have hK : cfc k A ≠ 0 := by
      intro h0
      have := (eqOn_of_cfc_eq_cfc (f := k) (g := 0) (a := A) (h0.trans (cfc_zero ℝ A).symm)) hb
      simp only [Pi.zero_apply, hk_def] at this
      have : b - c ≤ 0 := by
        rw [← this]; exact le_max_left _ _
      linarith
    have hcomm : ∀ g, Commute (cfc k A) (π g) := fun g => (hc g).cfc_real k
    let S : Submodule ℂ H := LinearMap.ker (cfc k A).toLinearMap
    have hS : S = ⊥ ∨ S = ⊤ := by
      refine hirr S ?_ ?_
      · exact (cfc k A).isClosed_ker
      · intro g u hu
        have hu' : cfc k A u = 0 := hu
        show cfc k A (π g u) = 0
        have := congrArg (fun T : H →L[ℂ] H => T u) (hcomm g).eq
        simp only [ContinuousLinearMap.mul_apply] at this
        rw [this, hu', map_zero]
    rcases hS with hS | hS
    · apply hF
      ext v
      have hv : cfc f A v ∈ S := by
        show cfc k A (cfc f A v) = 0
        rw [← ContinuousLinearMap.mul_apply, hprod, ContinuousLinearMap.zero_apply]
      rw [hS, Submodule.mem_bot] at hv
      simpa using hv
    · apply hK
      ext v
      have hv : v ∈ S := hS ▸ Submodule.mem_top
      have hv' : cfc k A v = 0 := hv
      rw [ContinuousLinearMap.zero_apply]
      exact hv'
  refine ⟨r, ?_⟩
  calc A = cfc (fun x : ℝ => x) A := (cfc_id' ℝ A).symm
    _ = cfc (fun _ : ℝ => r) A := cfc_congr (fun s hs => hsub s hs)
    _ = algebraMap ℝ (H →L[ℂ] H) r := cfc_const r A

theorem schur_unitary_irreducible (G H : Type) [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : G →* (H →L[ℂ] H))
    (hπ : ∀ g u, ‖π g u‖ = ‖u‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ u ∈ S, π g u ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (T : H →L[ℂ] H) (hT : ∀ g, T * π g = π g * T) : ∃ c : ℂ, T = c • 1 := by
  classical
  have hinner : ∀ g (u v : H), ⟪π g u, π g v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro g u v
    let L : H →ₗᵢ[ℂ] H := ⟨(π g).toLinearMap, hπ g⟩
    exact L.inner_map_map u v
  have hinv : ∀ g (v : H), π g (π g⁻¹ v) = v := by
    intro g v
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hadj : ∀ g, ContinuousLinearMap.adjoint (π g) = π g⁻¹ := by
    intro g
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro u v
    rw [← hinner g (π g⁻¹ u) v, hinv]
  have hstar : ∀ g, star (π g) = π g⁻¹ := hadj
  have hcT : ∀ g, Commute T (π g) := fun g => hT g
  have hcS : ∀ g, Commute (star T) (π g) := by
    intro g
    have h1 := (hcT g⁻¹).star_star
    rw [hstar, inv_inv] at h1
    exact h1
  have hre : ∀ g, Commute (realPart T : H →L[ℂ] H) (π g) := by
    intro g
    rw [realPart_apply_coe]
    exact ((hcT g).add_left (hcS g)).smul_left _
  have him : ∀ g, Commute (imaginaryPart T : H →L[ℂ] H) (π g) := by
    intro g
    rw [imaginaryPart_apply_coe]
    exact (((hcT g).sub_left (hcS g)).smul_left _).smul_left _
  obtain ⟨a, ha⟩ := selfAdjoint_eq_algebraMap_of_commute_irreducible (⇑π) hirr _ (realPart T).2 hre
  obtain ⟨b, hb⟩ := selfAdjoint_eq_algebraMap_of_commute_irreducible (⇑π) hirr _ (imaginaryPart T).2 him
  refine ⟨(a : ℂ) + Complex.I * (b : ℂ), ?_⟩
  rw [← realPart_add_I_smul_imaginaryPart T, ha, hb, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, add_smul, mul_smul, ← Complex.coe_smul, ← Complex.coe_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SesqEqZeroOfDiagEqZero
section
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {σ : G →* (H →L[ℂ] H)} {d : ℝ} in
private lemma integrable_matrixCoeff_mul_star
    (hmeas : ∀ x y : H, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ)
    (hsq : ∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ) (x y x' y' : H) :
    Integrable (fun g => ⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) μ := by
  refine Integrable.mono' ((hsq x y).add (hsq x' y'))
    ((hmeas x y).mul (hmeas x' y').star) (Filter.Eventually.of_forall fun g => ?_)
  simp only [norm_mul, norm_star, Pi.add_apply]
  nlinarith [sq_nonneg (‖⟪y, σ g x⟫_ℂ‖ - ‖⟪y', σ g x'⟫_ℂ‖),
    mul_nonneg (norm_nonneg ⟪y, σ g x⟫_ℂ) (norm_nonneg ⟪y', σ g x'⟫_ℂ)]

open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {σ : G →* (H →L[ℂ] H)} {d : ℝ} in
private lemma integral_matrixCoeff_mul_star_self
    (hsq : ∀ x y : H, ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) (x y : H) :
    ∫ g, ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x⟫_ℂ ∂μ = ⟪x, x⟫_ℂ * ⟪y, y⟫_ℂ / d := by
  have h : (fun g => ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x⟫_ℂ) =
      fun g => ((‖⟪y, σ g x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, integral_complex_ofReal, hsq x y, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]
  first
    | (push_cast; rfl)
    | simp

open scoped ComplexConjugate in
private lemma mul_conj_eq_polarization (a b : ℂ) :
    a * conj b = 1 / 4 * ((a + b) * conj (a + b) - (a - b) * conj (a - b)
      + Complex.I * ((a + Complex.I * b) * conj (a + Complex.I * b))
      - Complex.I * ((a - Complex.I * b) * conj (a - Complex.I * b))) := by
  simp only [map_add (f := _), map_sub, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
private lemma inner_swap_eq_polarization (x x' : H) :
    ⟪x', x⟫_ℂ = 1 / 4 * (⟪x + x', x + x'⟫_ℂ - ⟪x - x', x - x'⟫_ℂ
      + Complex.I * ⟪x + Complex.I • x', x + Complex.I • x'⟫_ℂ
      - Complex.I * ⟪x - Complex.I • x', x - Complex.I • x'⟫_ℂ) := by
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_add_right,
    inner_sub_right, inner_smul_right, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {σ : G →* (H →L[ℂ] H)} {d : ℝ} in
private lemma integral_matrixCoeff_mul_star_same_left
    (hmeas : ∀ x y : H, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ)
    (hsq : ∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) (x x' y : H) :
    ∫ g, ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x'⟫_ℂ ∂μ = ⟪x', x⟫_ℂ * ⟪y, y⟫_ℂ / d := by
  have hint := integrable_matrixCoeff_mul_star hmeas (fun x y => (hsq x y).1)
  have hdiag := integral_matrixCoeff_mul_star_self (fun x y => (hsq x y).2)
  have hpt : ∀ g, ⟪y, σ g x⟫_ℂ * star ⟪y, σ g x'⟫_ℂ =
      (1 / 4 : ℂ) * (⟪y, σ g (x + x')⟫_ℂ * star ⟪y, σ g (x + x')⟫_ℂ
        - ⟪y, σ g (x - x')⟫_ℂ * star ⟪y, σ g (x - x')⟫_ℂ
        + Complex.I * (⟪y, σ g (x + Complex.I • x')⟫_ℂ * star ⟪y, σ g (x + Complex.I • x')⟫_ℂ)
        - Complex.I * (⟪y, σ g (x - Complex.I • x')⟫_ℂ * star ⟪y, σ g (x - Complex.I • x')⟫_ℂ)) := by
    intro g
    rw [Complex.star_def, mul_conj_eq_polarization ⟪y, σ g x⟫_ℂ ⟪y, σ g x'⟫_ℂ]
    simp only [map_add (f := _), map_sub, map_smul, inner_add_right, inner_sub_right, inner_smul_right,
      Complex.star_def]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    hdiag, hdiag, hdiag, hdiag, inner_swap_eq_polarization x x']
  · ring
  all_goals first
    | exact hint _ _ _ _
    | exact (hint _ _ _ _).const_mul _
    | exact (hint _ _ _ _).sub (hint _ _ _ _)
    | exact ((hint _ _ _ _).sub (hint _ _ _ _)).add ((hint _ _ _ _).const_mul _)

open scoped ComplexConjugate in
private lemma mul_conj_eq_polarization_four (a a' b b' : ℂ) :
    a * conj b' = 1 / 4 * ((a + a') * conj (b + b') - (a - a') * conj (b - b')
      - Complex.I * ((a - Complex.I * a') * conj (b - Complex.I * b'))
      + Complex.I * ((a + Complex.I * a') * conj (b + Complex.I * b'))) := by
  simp only [map_add (f := _), map_sub, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

open MeasureTheory in
open scoped InnerProductSpace in
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
private lemma inner_eq_polarization (w w' : H) :
    ⟪w, w'⟫_ℂ = 1 / 4 * (⟪w + w', w + w'⟫_ℂ - ⟪w - w', w - w'⟫_ℂ
      - Complex.I * ⟪w + Complex.I • w', w + Complex.I • w'⟫_ℂ
      + Complex.I * ⟪w - Complex.I • w', w - Complex.I • w'⟫_ℂ) := by
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_add_right,
    inner_sub_right, inner_smul_right, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring


open MeasureTheory in
open scoped InnerProductSpace in
theorem _root_.GlobalTheory.polarised_schur_relations :
    ∀ (G : Type) [Group G] [MeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (d : ℝ), (∀ x y : H, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ) → (∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧ ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) → ∀ v w v' w' : H, Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧ ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  intro G _ _ μ H _ _ _ σ d hmeas hsq v w v' w'
  have hint := integrable_matrixCoeff_mul_star hmeas (fun x y => (hsq x y).1)
  have hone := integral_matrixCoeff_mul_star_same_left hmeas hsq
  refine ⟨hint v w v' w', ?_⟩
  have hpt : ∀ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ =
      (1 / 4 : ℂ) * (⟪w + w', σ g v⟫_ℂ * star ⟪w + w', σ g v'⟫_ℂ
        - ⟪w - w', σ g v⟫_ℂ * star ⟪w - w', σ g v'⟫_ℂ
        - Complex.I * (⟪w + Complex.I • w', σ g v⟫_ℂ * star ⟪w + Complex.I • w', σ g v'⟫_ℂ)
        + Complex.I * (⟪w - Complex.I • w', σ g v⟫_ℂ * star ⟪w - Complex.I • w', σ g v'⟫_ℂ)) := by
    intro g
    rw [Complex.star_def, mul_conj_eq_polarization_four ⟪w, σ g v⟫_ℂ ⟪w', σ g v⟫_ℂ
      ⟪w, σ g v'⟫_ℂ ⟪w', σ g v'⟫_ℂ]
    simp only [inner_add_left, inner_sub_left, inner_smul_left, Complex.conj_I, Complex.star_def,
      neg_mul, ← sub_eq_add_neg, sub_neg_eq_add]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
    hone, hone, hone, hone, inner_eq_polarization w w']
  · ring
  all_goals first
    | exact hint _ _ _ _
    | exact (hint _ _ _ _).const_mul _
    | exact (hint _ _ _ _).sub (hint _ _ _ _)
    | exact ((hint _ _ _ _).sub (hint _ _ _ _)).sub ((hint _ _ _ _).const_mul _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ShellSumElementaryInequalities
section
open Matrix Finset Real

namespace GlobalTheory

theorem exp_neg_mul_two_pow_le_geometric (T : ℝ) (hT : 1 ≤ T) (i : ℕ) :
    Real.exp (-T * 2 ^ i) ≤ Real.exp (-T) * (1 / 2 : ℝ) ^ i := by
  have hb : (1 : ℝ) + i ≤ 2 ^ i := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) i
    norm_num at h
    linarith
  have he : Real.exp (-1) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) two_pos]
    linarith
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hexp : -T * 2 ^ i ≤ -T + (i : ℝ) * (-1) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ T by linarith) (sub_nonneg.mpr hb),
      mul_nonneg (sub_nonneg.mpr hT) hi]
  calc Real.exp (-T * 2 ^ i) ≤ Real.exp (-T + (i : ℝ) * (-1)) := Real.exp_le_exp.mpr hexp
    _ = Real.exp (-T) * Real.exp (-1) ^ i := by rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ Real.exp (-T) * (1 / 2 : ℝ) ^ i :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le he i) (Real.exp_pos _).le

theorem shell_sum_elementary_inequalities :
    (∀ (s ep c : ℝ), 0 < ep → ep ≤ s → 0 < c → ep ≤ 1 / c → ep * s ≤ min (s ^ 2) (s / c)) ∧ (∀ T : ℝ, 1 ≤ T → Summable (fun i : ℕ => Real.exp (-T * 2 ^ i)) ∧ ∑' i : ℕ, Real.exp (-T * 2 ^ i) ≤ 2 * Real.exp (-T)) ∧ ∀ (al be : ℝ) (f : ℕ), 0 ≤ al → al ≤ 2 → 0 ≤ be → be ≤ 1 → (al + be) ^ f - al ^ f ≤ f * be * 3 ^ f := by
  refine ⟨?_, ?_, ?_⟩
  · intro s ep c hep hs hc hc'
    have hs0 : 0 ≤ s := le_trans hep.le hs
    refine le_min ?_ ?_
    · rw [sq]
      exact mul_le_mul_of_nonneg_right hs hs0
    · calc ep * s ≤ (1 / c) * s := mul_le_mul_of_nonneg_right hc' hs0
        _ = s / c := by ring
  · intro T hT
    have hg : Summable (fun i : ℕ => Real.exp (-T) * (1 / 2 : ℝ) ^ i) :=
      summable_geometric_two.mul_left _
    have hs : Summable (fun i : ℕ => Real.exp (-T * 2 ^ i)) :=
      Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le)
        (fun i => exp_neg_mul_two_pow_le_geometric T hT i) hg
    refine ⟨hs, ?_⟩
    calc ∑' i : ℕ, Real.exp (-T * 2 ^ i) ≤ ∑' i : ℕ, Real.exp (-T) * (1 / 2 : ℝ) ^ i :=
          Summable.tsum_le_tsum (fun i => exp_neg_mul_two_pow_le_geometric T hT i) hs hg
      _ = 2 * Real.exp (-T) := by rw [tsum_mul_left, tsum_geometric_two, mul_comm]
  · intro al be f h0 h2 hb0 hb1
    induction f with
    | zero => simp
    | succ n ih =>
      have hX : 0 ≤ (al + be) ^ n - al ^ n :=
        sub_nonneg.mpr (pow_le_pow_left₀ h0 (by linarith) n)
      have ha : al ^ n ≤ 3 ^ n := pow_le_pow_left₀ h0 (by linarith) n
      have h1 : (al + be) * ((al + be) ^ n - al ^ n) ≤ 3 * ((n : ℝ) * be * 3 ^ n) :=
        mul_le_mul (by linarith) ih hX (by norm_num)
      have h3 : be * al ^ n ≤ be * 3 ^ n := mul_le_mul_of_nonneg_left ha hb0
      have h4 : 0 ≤ be * 3 ^ n := mul_nonneg hb0 (pow_nonneg (by norm_num) n)
      calc (al + be) ^ (n + 1) - al ^ (n + 1)
          = (al + be) * ((al + be) ^ n - al ^ n) + be * al ^ n := by ring
        _ ≤ 3 * ((n : ℝ) * be * 3 ^ n) + be * 3 ^ n := by linarith
        _ ≤ ((n + 1 : ℕ) : ℝ) * be * 3 ^ (n + 1) := by
          push_cast
          rw [pow_succ]
          nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteAndIsInvInvariantOfContinuousIntegrab
section
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

theorem sigmaFinite_and_isInvInvariant_of_continuous_integrable :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
      [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : G → ℂ),
      Continuous f → f 1 ≠ 0 → Integrable f μ → SigmaFinite μ ∧ μ.IsInvInvariant := by
  intro G _ _ _ _ _ _ μ _ _ f hfc hf1 hfi

  have hf1' : ‖f 1‖ₑ ≠ 0 := enorm_ne_zero.2 hf1
  have hc0 : ‖f 1‖ₑ / 2 ≠ 0 := by simp [hf1']
  have hcT : ‖f 1‖ₑ / 2 ≠ ⊤ := (ENNReal.div_lt_top enorm_ne_top two_ne_zero).ne

  have hUo : IsOpen {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} := isOpen_lt continuous_const hfc.enorm
  have h1U : (1 : G) ∈ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} :=
    ENNReal.half_lt_self hf1' enorm_ne_top

  have hUfin : μ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} < ⊤ := by
    calc μ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ≤ μ {x : G | ‖f 1‖ₑ / 2 ≤ ‖f x‖ₑ} :=
          measure_mono (Set.setOf_subset_setOf.2 fun _ hx => hx.le)
      _ ≤ (∫⁻ x, ‖f x‖ₑ ∂μ) / (‖f 1‖ₑ / 2) :=
          meas_ge_le_lintegral_div hfi.aestronglyMeasurable.enorm hc0 hcT
      _ < ⊤ := ENNReal.div_lt_top hfi.2.ne hc0

  have hσ : SigmaFinite μ := by
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun g : G => (fun y => g⁻¹ * y) ⁻¹' {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ})
      (fun g => hUo.preimage (continuous_const.mul continuous_id))
    refine Measure.sigmaFinite_of_countable
      (hTc.image fun g : G => (fun y => g⁻¹ * y) ⁻¹' {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}) ?_ ?_
    · rintro _ ⟨g, -, rfl⟩
      rw [measure_preimage_mul]
      exact hUfin
    · rw [Set.sUnion_image, hT]
      refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, ?_⟩
      show x⁻¹ * x ∈ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}
      rw [inv_mul_cancel]
      exact h1U

  have key : μ.inv = μ := by
    open Pointwise in
    have hVo : IsOpen ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) := hUo.inter hUo.inv
    open Pointwise in
    have hV0 : μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) ≠ 0 :=
      (hVo.measure_pos μ ⟨1, h1U, by simpa using h1U⟩).ne'
    open Pointwise in
    have hVT : μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) ≠ ⊤ :=
      ((measure_mono Set.inter_subset_left).trans_lt hUfin).ne
    open Pointwise in
    have hVinv : μ.inv ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) = μ ({x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ} ∩ {x : G | ‖f 1‖ₑ / 2 < ‖f x‖ₑ}⁻¹) := by
      rw [Measure.inv_apply, Set.inter_inv, inv_inv, Set.inter_comm]
    rw [measure_eq_div_smul μ.inv μ hV0 hVT, hVinv, ENNReal.div_self hV0 hVT, one_smul]
  exact ⟨hσ, ⟨key⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizeIntegralsAndCardCompositions
section
open MeasureTheory Finset

namespace GlobalTheory

theorem setIntegral_cube_prod (a : ℕ) (S : Set ℝ) (f : Fin a → ℝ → ℝ) :
    ∫ τ in Set.pi Set.univ (fun _ : Fin a => S), ∏ i, f i (τ i) = ∏ i, ∫ t in S, f i t := by
  have hμ : (volume : Measure (Fin a → ℝ)).restrict (Set.pi Set.univ (fun _ : Fin a => S)) =
      Measure.pi (fun _ : Fin a => (volume : Measure ℝ).restrict S) := by
    rw [volume_pi]
    exact Measure.restrict_pi_pi (fun _ : Fin a => (volume : Measure ℝ)) (fun _ => S)
  rw [hμ]
  exact integral_fintype_prod_eq_prod (ι := Fin a) f

theorem setIntegral_Icc_const_div (c lo : ℝ) (h0 : 0 < lo) (h1 : lo ≤ 1 / 2) :
    ∫ t in Set.Icc lo (1 / 2), c / t = c * Real.log (1 / (2 * lo)) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1]
  have hfun : (fun t : ℝ => c / t) = fun t => c * t⁻¹ := by
    funext t; rw [div_eq_mul_inv]
  rw [hfun, intervalIntegral.integral_const_mul, integral_inv_of_pos h0 hhalf]
  congr 2
  field_simp

private lemma setIntegral_Ioo_pow_mul_div_eq (c m : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c) :
    ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) =
      (c : ℝ) * ((1 / 2 : ℝ) ^ (c * m) / ((c * m : ℕ) : ℝ)) := by
  obtain ⟨k, hk⟩ : ∃ k, c * m = k + 1 := ⟨c * m - 1, by have := Nat.mul_le_mul hc hm; omega⟩
  have hcongr : Set.EqOn (fun t : ℝ => t ^ (c * m) * ((c : ℝ) / t)) (fun t => (c : ℝ) * t ^ k)
      (Set.Ioo (0 : ℝ) (1 / 2)) := by
    intro t ht
    have htne : t ≠ 0 := ne_of_gt ht.1
    simp only
    rw [hk, pow_succ]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const_mul,
    integral_pow, hk]
  push_cast
  ring

theorem setIntegral_Ioo_pow_mul_div (c m : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c) :
    0 ≤ ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) ∧
    ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) ≤ 1 := by
  rw [setIntegral_Ioo_pow_mul_div_eq c m hm hc]
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have hmpos : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (c * m) := by positivity
  have hpow1 : (1 / 2 : ℝ) ^ (c * m) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hcm : ((c * m : ℕ) : ℝ) = (c : ℝ) * m := by push_cast; ring
  rw [hcm]
  have hden : (0 : ℝ) < (c : ℝ) * m := by positivity
  refine ⟨by positivity, ?_⟩
  rw [mul_div_assoc', div_le_one hden]
  calc (c : ℝ) * (1 / 2 : ℝ) ^ (c * m) ≤ (c : ℝ) * 1 := by gcongr
    _ ≤ (c : ℝ) * m := by gcongr

theorem sum_card_composition_lt (q : ℕ) :
    ∑ j ∈ Finset.Icc 1 q, Fintype.card (Composition j) < 2 ^ q := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), composition_card, Nat.add_sub_cancel, pow_succ]
    omega

theorem sizeIntegrals_and_card_compositions :
    (∀ (a : ℕ) (c : Fin a → ℝ) (lo : ℝ), 0 < lo → lo ≤ 1 / 2 → (∀ i, 0 ≤ c i) → ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Icc lo (1 / 2)), ∏ i, c i / τ i = ∏ i, c i * Real.log (1 / (2 * lo))) ∧ (∀ (a : ℕ) (c : Fin a → ℕ) (m : ℕ), 1 ≤ m → (∀ i, 1 ≤ c i) → ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Ioo (0 : ℝ) (1 / 2)), ∏ i, τ i ^ (c i * m) * ((c i : ℝ) / τ i) ≤ 1) ∧ ∀ q : ℕ, ∑ j ∈ Finset.Icc 1 q, Fintype.card (Composition j) < 2 ^ q := by
  refine ⟨fun a c lo h0 h1 _ => ?_, fun a c m hm hc => ?_, sum_card_composition_lt⟩
  · refine (setIntegral_cube_prod a (Set.Icc lo (1 / 2)) (fun i t => c i / t)).trans ?_
    exact Finset.prod_congr rfl fun i _ => setIntegral_Icc_const_div (c i) lo h0 h1
  · refine (setIntegral_cube_prod a (Set.Ioo (0 : ℝ) (1 / 2))
      (fun i t => t ^ (c i * m) * ((c i : ℝ) / t))).trans_le ?_
    exact Finset.prod_le_one₀ (fun i _ => (setIntegral_Ioo_pow_mul_div (c i) m hm (hc i)).1)
      fun i _ => (setIntegral_Ioo_pow_mul_div (c i) m hm (hc i)).2

end GlobalTheory
end

