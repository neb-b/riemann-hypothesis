module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.DifferentiableOnDoublingIterate
section
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def doublingIterate (h : E → ℂ) : ℕ → E → ℂ
  | 0 => fun z => h ((2 : ℂ)⁻¹ • z)
  | n + 1 => fun z =>
      3 * doublingIterate h n ((2 : ℂ)⁻¹ • z) + doublingIterate h n (-((2 : ℂ)⁻¹ • z))

private theorem norm_half_smul (z : E) : ‖(2 : ℂ)⁻¹ • z‖ = ‖z‖ / 2 := by
  rw [norm_smul, norm_inv]
  simp [div_eq_inv_mul]

private theorem half_mem_ball {r : ℝ} {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    (2 : ℂ)⁻¹ • z ∈ Metric.ball (0 : E) r := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_half_smul]
  linarith [norm_nonneg z]

private theorem neg_mem_ball' {r : ℝ} {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    -z ∈ Metric.ball (0 : E) r := by
  rw [mem_ball_zero_iff] at hz ⊢
  rwa [norm_neg]

theorem differentiableOn_doublingIterate {h : E → ℂ} {r : ℝ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 r)) (n : ℕ) :
    DifferentiableOn ℂ (doublingIterate h n) (Metric.ball 0 r) := by
  induction n with
  | zero => exact hh.comp (by fun_prop) fun z hz => half_mem_ball hz
  | succ n ih =>
    have h1 : DifferentiableOn ℂ (fun z : E => doublingIterate h n ((2 : ℂ)⁻¹ • z))
        (Metric.ball 0 r) := ih.comp (by fun_prop) fun z hz => half_mem_ball hz
    have h2 : DifferentiableOn ℂ (fun z : E => doublingIterate h n (-((2 : ℂ)⁻¹ • z)))
        (Metric.ball 0 r) := ih.comp (by fun_prop) fun z hz => neg_mem_ball' (half_mem_ball hz)
    exact (h1.const_mul 3).add h2

theorem norm_doublingIterate_le {h : E → ℂ} {r C : ℝ} (hC : 0 ≤ C)
    (hh : ∀ z ∈ Metric.ball (0 : E) r, ‖h z‖ ≤ C * ‖z‖ ^ 3) (n : ℕ) :
    ∀ z ∈ Metric.ball (0 : E) r, ‖doublingIterate h n z‖ ≤ (1 / 2) ^ n * (C * ‖z‖ ^ 3) := by
  induction n with
  | zero =>
    intro z hz
    have h1 := hh _ (half_mem_ball hz)
    rw [norm_half_smul] at h1
    have h2 : 0 ≤ C * ‖z‖ ^ 3 := by positivity
    change ‖h ((2 : ℂ)⁻¹ • z)‖ ≤ _
    nlinarith
  | succ n ih =>
    intro z hz
    have h1 := ih _ (half_mem_ball hz)
    have h2 := ih _ (neg_mem_ball' (half_mem_ball hz))
    rw [norm_neg] at h2
    rw [norm_half_smul] at h1 h2
    change ‖3 * doublingIterate h n ((2 : ℂ)⁻¹ • z)
      + doublingIterate h n (-((2 : ℂ)⁻¹ • z))‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h3 : ‖(3 : ℂ)‖ = 3 := by simp
    rw [h3]
    calc _ ≤ 3 * ((1 / 2) ^ n * (C * (‖z‖ / 2) ^ 3)) + (1 / 2) ^ n * (C * (‖z‖ / 2) ^ 3) := by
          gcongr
      _ = _ := by ring

theorem exists_doubling_solution [FiniteDimensional ℂ E] (h : E → ℂ) (ha : AnalyticAt ℂ h 0)
    (hO : h =O[𝓝 0] (fun z => ‖z‖ ^ 3)) :
    ∃ k : E → ℂ, AnalyticAt ℂ k 0 ∧ k =O[𝓝 0] (fun z => ‖z‖ ^ 3) ∧
      ∀ᶠ z in 𝓝 0, k ((2 : ℂ) • z) - 3 * k z - k (-z) = h z := by
  obtain ⟨C, hC, hO⟩ := hO.exists_nonneg
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hO.bound.and ha.eventually_analyticAt)
  have hd : DifferentiableOn ℂ h (Metric.ball 0 r) :=
    fun z hz => (hball z hz).2.differentiableAt.differentiableWithinAt
  have hb : ∀ z ∈ Metric.ball (0 : E) r, ‖h z‖ ≤ C * ‖z‖ ^ 3 := fun z hz => by
    simpa using (hball z hz).1
  have hB := norm_doublingIterate_le hC hb
  have hgeom : ∀ c : ℝ, HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * c) (2 * c) :=
    fun c => hasSum_geometric_two.mul_right c
  have hS : ∀ z ∈ Metric.ball (0 : E) r, Summable fun n => doublingIterate h n z :=
    fun z hz => Summable.of_norm_bounded (hgeom _).summable fun n => hB n z hz
  refine ⟨fun z => ∑' n, doublingIterate h n z, ?_, ?_, ?_⟩
  · refine SCV.analyticAt_of_differentiableOn (s := Metric.ball 0 r)
      (SCV.differentiableOn_tsum_of_locally_normal Metric.isOpen_ball
        (differentiableOn_doublingIterate hd) fun x hx =>
          ⟨Metric.ball 0 r, Metric.isOpen_ball.mem_nhds hx, _, (hgeom (C * r ^ 3)).summable,
            fun n z hz => (hB n z hz).trans ?_⟩) (Metric.ball_mem_nhds 0 hr)
    have := (mem_ball_zero_iff.mp hz).le
    gcongr
  · refine Asymptotics.IsBigO.of_bound (2 * C) ?_
    filter_upwards [Metric.ball_mem_nhds 0 hr] with z hz
    refine (tsum_of_norm_bounded (hgeom _) fun n => hB n z hz).trans_eq ?_
    simp [mul_assoc]
  · filter_upwards [Metric.ball_mem_nhds (0 : E) (half_pos hr)] with z hz
    rw [mem_ball_zero_iff] at hz
    have hz1 : z ∈ Metric.ball (0 : E) r := by
      rw [mem_ball_zero_iff]
      linarith
    have hz2 : (2 : ℂ) • z ∈ Metric.ball (0 : E) r := by
      rw [mem_ball_zero_iff, norm_smul]
      have : ‖(2 : ℂ)‖ = 2 := by simp
      rw [this]
      linarith
    have e : (2 : ℂ)⁻¹ • (2 : ℂ) • z = z := inv_smul_smul₀ two_ne_zero z
    rw [(hS _ hz2).tsum_eq_zero_add]
    simp only [doublingIterate, e]
    rw [((hS z hz1).mul_left 3).tsum_add (hS _ (neg_mem_ball' hz1)), tsum_mul_left]
    ring

end

theorem exists_doubling_solution_pi :
    ∀ (g : ℕ) (h : (Fin g → ℂ) → ℂ), AnalyticAt ℂ h 0 → h =O[𝓝 0] (fun z => ‖z‖ ^ 3) →
      ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k =O[𝓝 0] (fun z => ‖z‖ ^ 3) ∧
        ∀ᶠ z in 𝓝 0, k ((2 : ℂ) • z) - 3 * k z - k (-z) = h z :=
  fun _ h ha hO => exists_doubling_solution h ha hO

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsLinearOfMulPeriod
section
open Complex Filter Topology

namespace GlobalTheory.ArtinKernel

theorem exists_glue {g : ℕ} {J : Type*} (D : J → Set (Fin g → ℂ))
    (G : J → (Fin g → ℂ) → ℂ) (hD : ∀ j, IsOpen (D j)) (hcov : ∀ z, ∃ j, z ∈ D j)
    (hG : ∀ j, DifferentiableOn ℂ (G j) (D j))
    (hc : ∀ j j' z, z ∈ D j → z ∈ D j' → G j z = G j' z) :
    ∃ F : (Fin g → ℂ) → ℂ, Differentiable ℂ F ∧ ∀ j z, z ∈ D j → F z = G j z := by
  choose k hk using hcov
  refine ⟨fun z => G (k z) z, fun z => ?_, fun j z hz => hc _ _ _ (hk z) hz⟩
  have hU : D (k z) ∈ 𝓝 z := (hD (k z)).mem_nhds (hk z)
  have hev : (fun w => G (k w) w) =ᶠ[𝓝 z] G (k z) := by
    filter_upwards [hU] with w hw
    exact hc _ _ _ (hk w) hw
  exact ((hG (k z)).differentiableAt hU).congr_of_eventuallyEq hev

theorem differentiable_fderiv {g : ℕ} {F : (Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (fderiv ℂ F) := differentiableOn_univ.mp (GlobalTheory.SCV.differentiableOn_fderiv isOpen_univ hF.differentiableOn)

theorem exists_linear_of_add_period {g : ℕ} {F : (Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {S : Set (Fin g → ℂ)} (hS : Submodule.span ℝ S = ⊤) (b : S → ℂ)
    (hb : ∀ (l : S) z, F (z + l) = F z + b l) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : S, b l = lam l := by
  have hD : Differentiable ℂ (fderiv ℂ F) := differentiable_fderiv hF
  have hper : ∀ z, ∀ l ∈ S, fderiv ℂ F (z + l) = fderiv ℂ F z := by
    intro z l hl
    have h1 : (fun w => F (w + l)) = fun w => F w + b ⟨l, hl⟩ := funext fun w => hb ⟨l, hl⟩ w
    rw [← fderiv_comp_add_right (f := F) l, h1, fderiv_add_const]
  have hconst : ∀ z, fderiv ℂ F z = fderiv ℂ F 0 := fun z =>
    GlobalTheory.entire_apply_eq_of_periodic_of_span_real hD hS hper z 0
  set L := fderiv ℂ F 0 with hL
  have hlin : ∀ z, F z = F 0 + L z := by
    intro z
    have hd : Differentiable ℂ (fun w => F w - L w) := hF.sub L.differentiable
    have h0 : ∀ w, fderiv ℂ (fun w => F w - L w) w = 0 := by
      intro w
      rw [fderiv_fun_sub (hF w) L.differentiableAt, L.fderiv, hconst w, sub_self]
    have := is_const_of_fderiv_eq_zero hd h0 z 0
    rw [map_zero, sub_zero] at this
    linear_combination this
  refine ⟨L.toLinearMap, fun l => ?_⟩
  have := hb l 0
  rw [zero_add, hlin l.1] at this
  simp only [ContinuousLinearMap.coe_coe]
  linear_combination -this

theorem exists_linear_of_mul_period {g : ℕ} {F : (Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F)
    (h0 : ∀ z, F z ≠ 0) {S : Set (Fin g → ℂ)} (hS : Submodule.span ℝ S = ⊤) (b : S → ℂ)
    (hb : ∀ (l : S) z, F (z + l) = b l * F z) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : S, b l = cexp (lam l) := by
  have hb0 : ∀ l : S, b l ≠ 0 := by
    intro l hl
    have := hb l 0
    rw [hl, zero_mul, zero_add] at this
    exact h0 _ this
  have hdF : ∀ (l : S) z, fderiv ℂ F (z + l) = b l • fderiv ℂ F z := by
    intro l z
    have h1 : (fun w => F (w + l)) = fun w => b l * F w := funext fun w => hb l w
    rw [← fderiv_comp_add_right (f := F) (l : Fin g → ℂ), h1, fderiv_const_mul (hF z)]
  set H : (Fin g → ℂ) → ((Fin g → ℂ) →L[ℂ] ℂ) := fun z => (F z)⁻¹ • fderiv ℂ F z with hH
  have hHd : Differentiable ℂ H := (hF.inv h0).smul (differentiable_fderiv hF)
  have hper : ∀ z, ∀ l ∈ S, H (z + l) = H z := by
    intro z l hl
    simp only [hH]
    rw [hb ⟨l, hl⟩ z, hdF ⟨l, hl⟩ z, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (hb0 _), mul_one]
  have hconst : ∀ z, H z = H 0 := fun z =>
    GlobalTheory.entire_apply_eq_of_periodic_of_span_real hHd hS hper z 0
  set L := H 0 with hL
  have hDF : ∀ w, fderiv ℂ F w = F w • L := by
    intro w
    rw [← hconst w, hH, smul_smul, mul_inv_cancel₀ (h0 w), one_smul]
  have hK : ∀ w, fderiv ℂ (fun z => F z * cexp (-L z)) w = 0 := by
    intro w
    have h2 : HasFDerivAt (fun z => F z * cexp (-L z))
        (F w • (cexp (-L w) • -L) + cexp (-L w) • fderiv ℂ F w) w :=
      (hF w).hasFDerivAt.mul L.hasFDerivAt.neg.cexp
    rw [h2.fderiv, hDF w]
    ext v
    simp only [add_apply, smul_apply, neg_apply, zero_apply, smul_eq_mul]
    ring
  have hKd : Differentiable ℂ (fun z => F z * cexp (-L z)) :=
    hF.mul (L.differentiable.neg.cexp)
  refine ⟨L.toLinearMap, fun l => ?_⟩
  have e1 := is_const_of_fderiv_eq_zero hKd hK (l : Fin g → ℂ) 0
  have e2 := hb l 0
  rw [zero_add] at e2
  rw [e2, map_zero, neg_zero, Complex.exp_zero, mul_one, mul_right_comm] at e1
  have e3 : b l * cexp (-L l) = 1 := by
    have := mul_right_cancel₀ (h0 0) (e1.trans (one_mul _).symm)
    exact this
  rw [Complex.exp_neg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)] at e3
  simpa only [ContinuousLinearMap.coe_coe] using e3

section Artin

variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]

theorem exists_residue : ∃ ρ : R →ₐ[ℂ] ℂ, ∀ r, ρ r = 0 → r ∈ IsLocalRing.maximalIdeal R := by
  have hsurj := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := ℂ) (K := R ⧸ IsLocalRing.maximalIdeal R))
  let e : ℂ ≃ₐ[ℂ] R ⧸ IsLocalRing.maximalIdeal R := AlgEquiv.ofBijective (Algebra.ofId ℂ _) hsurj
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ _), fun r hr => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h1 : e.symm (Ideal.Quotient.mk _ r) = 0 := hr
  have h2 := congrArg e h1
  rwa [AlgEquiv.apply_symm_apply, map_zero] at h2

theorem subsingleton_primeSpectrum : Subsingleton (PrimeSpectrum R) := by
  have : IsArtinianRing R := IsArtinianRing.of_finite ℂ R
  refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
  rw [IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime p.asIdeal),
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime q.asIdeal)]

theorem exists_functional {ι : Type*} (δ : ι → R) (hδ : ∃ i, δ i ≠ 0) :
    ∃ lam : R →ₗ[ℂ] ℂ, (∃ i, lam (δ i) ≠ 0) ∧
      ∀ i, ∀ r ∈ IsLocalRing.maximalIdeal R, lam (r * δ i) = 0 := by
  classical
  set m := IsLocalRing.maximalIdeal R
  set N : Submodule ℂ R := Submodule.span ℂ {x | ∃ r ∈ m, ∃ i, x = r * δ i} with hN
  have hex : ∃ i, δ i ∉ N := by
    by_contra! hall
    set J : Ideal R := Ideal.span (Set.range δ) with hJ
    have hNJ : ∀ x ∈ N, x ∈ m • J := by
      intro x hx
      refine Submodule.span_induction (p := fun x _ => x ∈ m • J) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨r, hr, i, rfl⟩
        exact Submodule.smul_mem_smul hr (Ideal.subset_span ⟨i, rfl⟩)
      · exact zero_mem _
      · intro x y _ _ hx hy
        exact add_mem hx hy
      · intro c x _ hx
        exact Submodule.smul_of_tower_mem _ c hx
    have hle : J ≤ m • J := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hNJ _ (hall i)
    have : IsArtinianRing R := IsArtinianRing.of_finite ℂ R
    have hJ0 : J = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m J
      (IsNoetherian.noetherian J) hle
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
    obtain ⟨i, hi⟩ := hδ
    apply hi
    have : δ i ∈ J := Ideal.subset_span ⟨i, rfl⟩
    rw [hJ0] at this
    exact (Submodule.mem_bot R).mp this
  obtain ⟨i, hi⟩ := hex
  obtain ⟨lam, hlam, hker⟩ := Submodule.exists_le_ker_of_notMem hi
  refine ⟨lam, ⟨i, hlam⟩, fun j r hr => ?_⟩
  exact hker (Submodule.subset_span ⟨r, hr, j, rfl⟩)


omit [IsLocalRing R] in
theorem differentiableOn_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E} {F G : E → R}
    (hF : ∀ lam : R →ₗ[ℂ] ℂ, DifferentiableOn ℂ (fun z => lam (F z)) S)
    (hG : ∀ lam : R →ₗ[ℂ] ℂ, DifferentiableOn ℂ (fun z => lam (G z)) S) (lam : R →ₗ[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z => lam (F z * G z)) S := by
  classical
  set b := Module.Free.chooseBasis ℂ R
  have key : (fun z => lam (F z * G z)) = fun z =>
      ∑ j, ∑ i, b.coord i (F z) * b.coord j (G z) * lam (b i * b j) := by
    funext z
    conv_lhs => rw [← b.sum_repr (F z), ← b.sum_repr (G z)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul,
      smul_eq_mul, Module.Basis.coord_apply]
  rw [key]
  refine DifferentiableOn.fun_sum fun j _ => DifferentiableOn.fun_sum fun i _ => ?_
  exact ((hF (b.coord i)).mul (hG (b.coord j))).mul_const _

end Artin

end GlobalTheory.ArtinKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsLocalFrameCompatibleCube
section
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem exists_localFrame_compatible_cube :
    (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∀ (i₀ : ι), 0 ∈ W i₀ → ∀ F : (Fin 3 → Fin g → ℂ) → ℂ, F = T (fun _ => i₀) → (∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → (∀ (g : ℕ) (F : (Fin 3 → Fin g → ℂ) → ℂ), AnalyticAt ℂ F 0 → F 0 ≠ 0 → ((∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k 0 = 0 ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x = F 0 * ∏ I : Finset (Fin 3), cexp (k (∑ a ∈ I, x a)) ^ ((-1 : ℤ) ^ (3 - I.card))) → (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∃ (r : ℝ) (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r)) ∧ (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) := by
  intro H1 H2 g ι W c hW hcov hcd hc0 hcoc T hTd hT0 hTc Λ hΛd hΛs hWp hcp hTp
  obtain ⟨i₀, hi₀⟩ := hcov 0
  obtain ⟨F, hF⟩ : ∃ F, F = T (fun _ => i₀) := ⟨_, rfl⟩
  let U : Set (Fin 3 → Fin g → ℂ) := {x | ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W i₀}
  have hUo : IsOpen U := by
    have e : U = ⋂ I : Finset (Fin 3), (fun x : Fin 3 → Fin g → ℂ => ∑ a ∈ I, x a) ⁻¹' W i₀ := by
      ext x
      simp [U]
    rw [e]
    exact isOpen_iInter_of_finite fun I =>
      (hW i₀).preimage (continuous_finsetSum I fun a _ => continuous_apply a)
  have hU0 : (0 : Fin 3 → Fin g → ℂ) ∈ U := fun I => by simpa using hi₀
  have hUn : U ∈ 𝓝 (0 : Fin 3 → Fin g → ℂ) := hUo.mem_nhds hU0
  have hFa : AnalyticAt ℂ F 0 := hF ▸ GlobalTheory.SCV.analyticAt_of_differentiableOn (hTd _) hUn
  have hF0 : F 0 ≠ 0 := hF ▸ hT0 _ 0 hU0
  have hcube := H1 g W c hW hcov hcd hc0 hcoc T hTd hT0 hTc Λ hΛd hΛs hWp hcp hTp i₀ hi₀ F hF
  obtain ⟨k, hka, -, hkF⟩ := H2 g F hFa hF0 hcube
  obtain ⟨ε, hε, hkε⟩ : ∃ ε > 0, ∀ z ∈ Metric.ball (0 : Fin g → ℂ) ε, DifferentiableAt ℂ k z :=
    Metric.eventually_nhds_iff_ball.1 (hka.eventually_analyticAt.mono fun z hz => hz.differentiableAt)
  obtain ⟨δ, hδ, hδW⟩ := Metric.isOpen_iff.1 (hW i₀) 0 hi₀
  have hrW : ∀ z ∈ Metric.ball (0 : Fin g → ℂ) (min ε δ), z ∈ W i₀ := fun z hz =>
    hδW (Metric.ball_subset_ball (min_le_right _ _) hz)
  refine ⟨min ε δ, fun i z => c i i₀ z * cexp (k z), F 0, lt_min hε hδ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    show DifferentiableOn ℂ (fun z => c i i₀ z * cexp (k z)) _
    refine DifferentiableOn.mul ((hcd i i₀).mono ?_) ?_
    · rintro z ⟨hz1, hz2⟩
      exact ⟨hz1, hrW z hz2⟩
    · intro z hz
      exact (hkε z (Metric.ball_subset_ball (min_le_left _ _) hz.2)).cexp.differentiableWithinAt
  · intro i z hz hzr
    exact mul_ne_zero (hc0 i i₀ z hz (hrW z hzr)) (Complex.exp_ne_zero _)
  · intro i j z hzi hzj hzr
    show c i i₀ z * cexp (k z) = c i j z * (c j i₀ z * cexp (k z))
    rw [← mul_assoc, hcoc i j i₀ z hzi hzj (hrW z hzr)]
  · filter_upwards [hkF, hUn] with x hx hxU
    intro j hj
    rw [hTc j (fun _ => i₀) x hj hxU, ← hF, hx]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    ring

end GlobalTheory
end

