module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AbsCoeffProdXLeOne
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem abs_coeff_prod_X_le_one {σ : Type} {n : ℕ} (w : Fin n → σ) (m : σ →₀ ℕ) :
    |(∏ j, X (w j) : MvPolynomial σ ℝ).coeff m| ≤ 1 := by
  classical
  have h : (∏ j, X (w j) : MvPolynomial σ ℝ) = monomial (∑ j, Finsupp.single (w j) 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [h, coeff_monomial]
  split_ifs <;> simp

theorem formPoly_sub_bound : ∀ (σ : Type) [Fintype σ] (n : ℕ) (a b : (Fin n → σ) → ℝ) (M : ℝ),
    (∀ w, |a w - b w| ≤ M) →
    (∀ m, |(formPoly n a).coeff m - (formPoly n b).coeff m| ≤ (Fintype.card σ : ℝ) ^ n * M) ∧
    ∀ c : σ → ℝ, |eval c (formPoly n a) - eval c (formPoly n b)| ≤ (∑ x, |c x|) ^ n * M := by
  intro σ _ n a b M h
  constructor
  · intro m
    simp only [formPoly, coeff_sum, coeff_C_mul]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : Fin n → σ, |a w * (∏ j, X (w j) : MvPolynomial σ ℝ).coeff m
            - b w * (∏ j, X (w j) : MvPolynomial σ ℝ).coeff m|
        ≤ ∑ _w : Fin n → σ, M := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [← sub_mul, abs_mul]
          calc _ ≤ |a w - b w| * 1 :=
                mul_le_mul_of_nonneg_left (abs_coeff_prod_X_le_one w m) (abs_nonneg _)
            _ ≤ M := by rw [mul_one]; exact h w
      _ = (Fintype.card σ : ℝ) ^ n * M := by
          simp
  · intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [formPoly, map_sum, map_mul, eval_C, map_prod, eval_X]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : Fin n → σ, |a w * ∏ j, c (w j) - b w * ∏ j, c (w j)|
        ≤ ∑ w : Fin n → σ, (∏ j, |c (w j)|) * M := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [← sub_mul, abs_mul, Finset.abs_prod, mul_comm]
          exact mul_le_mul_of_nonneg_left (h w) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      _ = (∑ x, |c x|) ^ n * M := by
          rw [← Finset.sum_mul, Fintype.sum_pow]

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticDoublingMapLocalInverseStatement
section
open Set Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_doubling_map_local_inverse : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b₀ : B) (d : B × V → V), AnalyticAt ℂ d (b₀, 0) → d (b₀, 0) = 0 → HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V) (b₀, 0) → ∃ h : B × V → V, AnalyticAt ℂ h (b₀, 0) ∧ h (b₀, 0) = 0 ∧ (∀ᶠ p : B × V in 𝓝 (b₀, 0), d (p.1, h p) = p.2) ∧ (∀ᶠ p : B × V in 𝓝 (b₀, 0), h (p.1, d p) = p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse | exact GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse | (intros; apply GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticGroupLawBoundedCommutatorStatement
section
open Set Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_group_law_bounded_commutator : ∀ {B V W : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (b₀ : B) (G : B × V × V → W) (R : ℝ), 0 < R → DifferentiableOn ℂ G (ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R) → (∀ p ∈ ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R, ‖G p‖ ≤ 1) → (∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, G (b, s, 0) = 0 ∧ G (b, 0, s) = 0) → ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, ∀ t ∈ ball (0 : V) R, ‖G (b, s, t)‖ ≤ ‖s‖ * ‖t‖ / R ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes | exact GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes | (intros; apply GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DenseCoordinateTorus
section
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem dense_forall_coord_ne_zero : ∀ n : ℕ, Dense {z : Fin n → ℂ | ∀ i, z i ≠ 0} := by
  intro n
  have h : {z : Fin n → ℂ | ∀ i, z i ≠ 0} = Set.pi Set.univ (fun _ => ({0}ᶜ : Set ℂ)) := by
    ext z
    simp
  rw [h]
  exact dense_pi Set.univ (fun _ _ => dense_compl_singleton 0)

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DominatedConvergenceExhaustionStatement
section
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominated_convergence_exhaustion : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (l : Filter ℝ) [l.NeBot] [l.IsCountablyGenerated] (E : ℕ → Set α) (L : α → ℝ) (ρ Γ : ℝ → α → ℝ) (ρ0 Γ0 : α → ℝ) (a : ℝ) (b : ℕ → ℝ), (∀ n, MeasurableSet (E n)) → Monotone E → (∀ n, μ (E n) < ⊤) → (∀ᵐ y ∂μ, ∃ n, y ∈ E n) → (∀ᵐ y ∂μ, 0 ≤ L y) → 0 ≤ a → Tendsto b atTop (𝓝 0) → (∀ n, TendstoUniformlyOn ρ ρ0 l (E n)) → (∀ n, TendstoUniformlyOn Γ Γ0 l (E n)) → (∀ n, ∃ M : ℝ, ∀ y ∈ E n, |ρ0 y| ≤ M ∧ |Γ0 y| ≤ M) → (∀ᶠ t in l, AEStronglyMeasurable (ρ t) μ ∧ AEStronglyMeasurable (Γ t) μ ∧ (∀ᵐ y ∂μ, 0 ≤ ρ t y) ∧ (∀ᵐ y ∂μ, y ∉ E 0 → |Γ t y| ≤ a * L y) ∧ ∀ n, IntegrableOn (fun y => L y * ρ t y) (E n)ᶜ μ ∧ ∫ y in (E n)ᶜ, L y * ρ t y ∂μ ≤ b n) → Integrable (fun y => Γ0 y * ρ0 y) μ ∧ (∀ᶠ t in l, Integrable (fun y => Γ t y * ρ t y) μ) ∧ Tendsto (fun t => ∫ y, Γ t y * ρ t y ∂μ) l (𝓝 (∫ y, Γ0 y * ρ0 y ∂μ)) := by
  first | exact @GlobalTheory.CompanionTheory.Conv.tendsto_integral_of_exhaustion | exact GlobalTheory.CompanionTheory.Conv.tendsto_integral_of_exhaustion | (intros; apply GlobalTheory.CompanionTheory.Conv.tendsto_integral_of_exhaustion <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DoublingLimitLocalLogarithm
section
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

theorem koenigs_step {B V : Type} [NormedAddCommGroup B] [NormedAddCommGroup V]
    [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (ρ C : ℝ) (hC : 0 ≤ C)
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖)
    (hquad : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2)
    {b : B} (hb : b ∈ ball b₀ ρ) {s : V} (hs : s ∈ ball (0 : V) ρ) (k : ℕ) :
    dist ((2 : ℂ) ^ k • iter h k (b, s)) ((2 : ℂ) ^ (k + 1) • iter h (k + 1) (b, s))
      ≤ C * ‖s‖ ^ 2 * (18 / 25) ^ k := by
  rw [dist_eq_norm, iter_succ, pow_succ, mul_smul, ← smul_sub, norm_smul, norm_sub_rev]
  have hx := iter_mem_ball b₀ h ρ hcontr hb hs k
  have hxn := norm_iter_le b₀ h ρ hcontr hb hs k
  have h2 : ‖(2 : ℂ) ^ k‖ = (2 : ℝ) ^ k := by simp
  rw [h2]
  calc (2 : ℝ) ^ k * ‖(2 : ℂ) • h (b, iter h k (b, s)) - iter h k (b, s)‖
      ≤ (2 : ℝ) ^ k * (C * ‖iter h k (b, s)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hquad b hb _ hx) (by positivity)
    _ ≤ (2 : ℝ) ^ k * (C * ((3 / 5) ^ k * ‖s‖) ^ 2) := by gcongr
    _ = C * ‖s‖ ^ 2 * (18 / 25) ^ k := by
        have e : (18 / 25 : ℝ) ^ k = 2 ^ k * ((3 / 5) ^ k) ^ 2 := by
          rw [← pow_mul, mul_comm k 2, pow_mul, ← mul_pow]
          norm_num
        rw [e]
        ring

theorem koenigs_limit : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b₀ : B) (h : B × V → V)
    (ρ C : ℝ), 0 < ρ → 0 ≤ C →
    (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) →
    (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2) →
    ∃ L : B × V → V,
      TendstoUniformlyOn (fun (k : ℕ) (p : B × V) => (2 : ℂ) ^ k • iter h k p) L atTop
        (ball b₀ ρ ×ˢ ball (0 : V) ρ) ∧
      ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖L (b, s) - s‖ ≤ 4 * C * ‖s‖ ^ 2 := by
  intro B V _ _ _ _ _ b₀ h ρ C hρ hC hcontr hquad
  set F : ℕ → B × V → V := fun k p => (2 : ℂ) ^ k • iter h k p with hF
  have hstep : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, ∀ k : ℕ,
      dist (F k p) (F (k + 1) p) ≤ C * ‖p.2‖ ^ 2 * (18 / 25) ^ k := by
    rintro ⟨b, s⟩ ⟨hb, hs⟩ k
    exact koenigs_step b₀ h ρ C hC hcontr hquad hb hs k
  have hr : (18 / 25 : ℝ) < 1 := by norm_num
  have hcauchy : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, CauchySeq (fun k => F k p) :=
    fun p hp => cauchySeq_of_le_geometric _ _ hr (hstep p hp)
  let L : B × V → V := fun p => limUnder atTop (fun k => F k p)
  have hlim : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, Tendsto (fun k => F k p) atTop (𝓝 (L p)) :=
    fun p hp => (hcauchy p hp).tendsto_limUnder
  have hdist : ∀ p ∈ ball b₀ ρ ×ˢ ball (0 : V) ρ, ∀ n : ℕ,
      dist (F n p) (L p) ≤ C * ‖p.2‖ ^ 2 * (18 / 25) ^ n / (7 / 25) := by
    intro p hp n
    have h1 := dist_le_of_le_geometric_of_tendsto _ _ hr (hstep p hp) (hlim p hp) n
    rwa [show (1 - 18 / 25 : ℝ) = 7 / 25 by norm_num] at h1
  refine ⟨L, ?_, ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hg : Tendsto (fun n : ℕ => C * ρ ^ 2 * (18 / 25 : ℝ) ^ n / (7 / 25)) atTop (𝓝 0) := by
      have h1 := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 18 / 25) hr).const_mul
        (C * ρ ^ 2)).div_const (7 / 25 : ℝ)
      simpa using h1
    filter_upwards [hg.eventually (gt_mem_nhds hε)] with n hn
    rintro ⟨b, s⟩ hp
    rw [dist_comm]
    refine lt_of_le_of_lt ((hdist _ hp n).trans ?_) hn
    have hs : ‖s‖ < ρ := by simpa using hp.2
    have hsle : ‖s‖ ≤ ρ := hs.le
    have hsq : ‖s‖ ^ 2 ≤ ρ ^ 2 := by gcongr
    show C * ‖s‖ ^ 2 * (18 / 25) ^ n / (7 / 25) ≤ C * ρ ^ 2 * (18 / 25) ^ n / (7 / 25)
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hsq hC
  · intro b hb s hs
    have h0 := hdist (b, s) ⟨hb, hs⟩ 0
    have e0 : F 0 (b, s) = s := by simp [hF]
    rw [e0, dist_comm, dist_eq_norm] at h0
    calc ‖L (b, s) - s‖ ≤ C * ‖s‖ ^ 2 * (18 / 25) ^ 0 / (7 / 25) := h0
      _ ≤ 4 * C * ‖s‖ ^ 2 := by
        rw [pow_zero, mul_one, div_le_iff₀ (by norm_num)]
        nlinarith [mul_nonneg hC (sq_nonneg ‖s‖)]

end GlobalTheory.CompanionTheory.Ar.Flat.LocalLog
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EqNegSumIicDifferencesStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_neg_sum_Iic_differences : ∀ (N : ℕ) (M : Type) [AddCommGroup M] (f : Fin N → M) (i : Fin N), f i = -∑ k ∈ Finset.Iic i, (if h : (k : ℕ) = 0 then -f k else f ⟨(k : ℕ) - 1, by have := k.2; omega⟩ - f k) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.Telescope.fin_iic_telescope | exact GlobalTheory.CompanionTheory.Metric.Telescope.fin_iic_telescope | (intros; apply GlobalTheory.CompanionTheory.Metric.Telescope.fin_iic_telescope <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EtaleAwayOfIsEtaleAtOffSubmonoid
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gap_eq_weight_sub_next {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    gap lam p = lam p - if h : (p.2 : ℕ) + 1 < N then lam (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0 := by
  unfold gap gapX
  split_ifs <;> simp

theorem gap_comp_swap {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a b : Fin N) (hb : (b : ℕ) = a + 1)
    (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    gap (lam ∘ Equiv.swap (τ, a) (τ, b)) p = gap lam p + gap lam (τ, a) * (xiCoef τ a p : ℝ) := by
  have hab : (a : ℕ) + 1 < N := hb ▸ b.2
  have hbe : (⟨(a : ℕ) + 1, hab⟩ : Fin N) = b := Fin.ext hb.symm
  have hu : gap lam (τ, a) = lam (τ, a) - lam (τ, b) := by
    rw [gap_eq_weight_sub_next]; simp only [hab, dif_pos, hbe]
  have hsw : ∀ q : Ψ × Fin N, (lam ∘ Equiv.swap (τ, a) (τ, b)) q =
      lam q + (if q.1 = τ then (if (q.2 : ℕ) = a + 1 then 1 else 0) - (if (q.2 : ℕ) = a then 1 else 0) else 0)
        * (lam (τ, a) - lam (τ, b)) := by
    rintro ⟨σ, i⟩
    by_cases h1 : (σ, i) = (τ, a)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      simp
    by_cases h2 : (σ, i) = (τ, b)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      simp [hb]
    rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
    by_cases hσ : σ = τ
    · subst hσ
      have e1 : (i : ℕ) ≠ a := fun h => h1 (by rw [Fin.ext h])
      have e2 : (i : ℕ) ≠ a + 1 := fun h => h2 (by rw [Fin.ext (h.trans hb.symm)])
      simp [e1, e2]
    · simp [hσ]
  obtain ⟨σ, i⟩ := p
  rw [hu, gap_eq_weight_sub_next, gap_eq_weight_sub_next]
  simp only [hsw, xiCoef, Fin.ext_iff]
  have hi := i.2
  split_ifs <;> first | omega | (push_cast; ring)

theorem gap_swap_decomp : ∀ (Ψ : Type) [DecidableEq Ψ] (N : ℕ) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ∀ lam : Ψ × Fin N → ℝ, let u := gap lam (τ, a); let c := fun p => gap lam p + u / 2 * (xiCoef τ a p : ℝ); c (τ, a) = 0 ∧ (∀ p, gap lam p = c p - u / 2 * (xiCoef τ a p : ℝ)) ∧ ∀ p, gap (lam ∘ Equiv.swap (τ, a) (τ, b)) p = c p + u / 2 * (xiCoef τ a p : ℝ) := by
  intro Ψ _ N τ a b hb lam u c
  refine ⟨?_, fun p => ?_, fun p => ?_⟩
  · simp only [c, u, xiCoef]
    simp
  · simp only [c]; ring
  · rw [gap_comp_swap τ a b hb]
    simp only [c, u]; ring

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EtaleLocalizationAtPrimeTensorOfEtaleAway
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial GroundTheory.Heights₂.Heights

theorem mem_antisymSpace_of_pointwise :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (R : MvPolynomial (Ψ × Fin N) ℝ),
      R.IsHomogeneous (antisymDegree Ψ N + 1) →
      (∀ (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) →
        ∀ lam : Ψ × Fin N → ℝ, eval lam R + eval (lam ∘ Equiv.swap (τ, a) (τ, b)) R = 0) →
      R ∈ antisymSpace Ψ N j := by
  intro Ψ _ _ N j R hR h
  refine ⟨(mem_homogeneousSubmodule _ _).2 hR, ?_⟩
  rintro σ ⟨τ, a, b, hab, hblock, rfl⟩
  refine MvPolynomial.funext fun lam => ?_
  rw [eval_rename, map_neg]
  exact eq_neg_of_add_eq_zero_right (h τ a b hab hblock lam)

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBasisSubsetOfSaturatedSubmodule
section
namespace GlobalTheory.CompanionTheory.Ar.Lattice

theorem exists_basis_span_eq_of_saturated (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ]
    [Module.Finite ℤ Λ] (N : Submodule ℤ Λ)
    (hN : ∀ (v : Λ) (n : ℤ), n ≠ 0 → n • v ∈ N → v ∈ N) :
    ∃ (k n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n),
      Function.Injective f ∧ Submodule.span ℤ (Set.range fun i => b (f i)) = N :=
  _root_.UpperTheory.Reformulated.B.Yha6.main Λ N hN

end GlobalTheory.CompanionTheory.Ar.Lattice
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHolomorphicNormalFrame
section
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem xiPot_logSin_change_of_frame : ∀ (G g : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → IsUnit g.det → (gᴴ * G * g).PosDef ∧ (∀ a : ℂ, g 0 0 + g 0 1 * a ≠ 0 → xiPot (gᴴ * G * g) a = xiPot G ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)) - 2 * Real.log ‖g 0 0 + g 0 1 * a‖ + Real.log ‖g.det‖) ∧ ∀ a₀ a₁ : ℂ, g 0 0 + g 0 1 * a₀ ≠ 0 → g 0 0 + g 0 1 * a₁ ≠ 0 → logSin (gᴴ * G * g) a₀ a₁ = logSin G ((g 1 0 + g 1 1 * a₀) / (g 0 0 + g 0 1 * a₀)) ((g 1 0 + g 1 1 * a₁) / (g 0 0 + g 0 1 * a₁)) := by
  intro G g hG hg
  have herm2_conj_lemma : ∀ (u w : Fin 2 → ℂ), herm2 (gᴴ * G * g) u w = herm2 G (g *ᵥ u) (g *ᵥ w) := by
    intro u w
    unfold herm2
    rw [← Matrix.mulVec_mulVec w (gᴴ * G) g, ← Matrix.mulVec_mulVec (g *ᵥ w) gᴴ G,
      Matrix.dotProduct_mulVec (star u) gᴴ, Matrix.star_mulVec g u]
  have herm2_smul_lemma_2 : ∀ (s t : ℂ) (u w : Fin 2 → ℂ),
      herm2 G (s • u) (t • w) = star s * t * herm2 G u w := by
    intro s t u w
    have hsu : star (s • u) = star s • star u := by
      ext i
      simp [star_mul']
    unfold herm2
    rw [Matrix.mulVec_smul, hsu, dotProduct_smul, smul_dotProduct]
    simp only [smul_eq_mul]
    ring
  have ratio_lemma_3 : ∀ (x y p q r : ℝ), x ≠ 0 → y ≠ 0 →
      (x * y * r) ^ 2 / (x ^ 2 * p * (y ^ 2 * q)) = r ^ 2 / (p * q) := by
    intro x y p q r hx hy
    rw [show (x * y * r) ^ 2 = r ^ 2 * (x ^ 2 * y ^ 2) by ring,
      show x ^ 2 * p * (y ^ 2 * q) = (p * q) * (x ^ 2 * y ^ 2) by ring]
    exact mul_div_mul_right _ _ (mul_ne_zero (pow_ne_zero 2 hx) (pow_ne_zero 2 hy))
  have hdet : g.det ≠ 0 := hg.ne_zero
  have hv : ∀ b : ℂ, (![1, b] : Fin 2 → ℂ) ≠ 0 := by
    intro b h
    have h0 := congrFun h 0
    simp at h0
  have hre : ∀ b : ℂ, 0 < (herm2 G ![1, b] ![1, b]).re := fun b =>
    (Complex.pos_iff.1 (hG.dotProduct_mulVec_pos (hv b))).1
  have hdG : 0 < G.det.re := (Complex.pos_iff.1 hG.det_pos).1
  have hcc : ∀ c : ℂ, star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    intro c
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  have hre_mul : ∀ c z : ℂ, (star c * c * z).re = ‖c‖ ^ 2 * z.re := by
    intro c z
    rw [hcc, Complex.re_ofReal_mul]
  have hc : ∀ a : ℂ, g 0 0 + g 0 1 * a ≠ 0 → g *ᵥ ![1, a] =
      (g 0 0 + g 0 1 * a) • ![1, (g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)] := by
    intro a ha
    have ha' : g 0 0 + a * g 0 1 ≠ 0 := by rwa [mul_comm a]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
  refine ⟨hG.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det g).mpr hg)), ?_, ?_⟩
  · intro a ha
    unfold xiPot
    rw [herm2_conj_lemma, hc a ha, herm2_smul_lemma_2, hre_mul, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_conjTranspose,
      show star g.det * G.det * g.det = star g.det * g.det * G.det by ring, hre_mul,
      Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)) (hre _).ne',
      Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr hdet)) hdG.ne', Real.log_pow, Real.log_pow]
    push_cast
    ring
  · intro a₀ a₁ h₀ h₁
    unfold logSin
    rw [herm2_conj_lemma, herm2_conj_lemma, herm2_conj_lemma, hc a₀ h₀, hc a₁ h₁, herm2_smul_lemma_2,
      herm2_smul_lemma_2, herm2_smul_lemma_2, hre_mul, hre_mul, norm_mul, norm_mul, norm_star,
      ratio_lemma_3 _ _ _ _ _ (norm_ne_zero_iff.mpr h₀) (norm_ne_zero_iff.mpr h₁)]

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FcHoloDetDifferentiableAt
section
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fcHolo_det_differentiableAt {E n : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype n] [DecidableEq n] (M : E → Matrix n n ℂ) (x : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun b => M b i j) x) :
    DifferentiableAt ℂ (fun b => (M b).det) x := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  have key : ∀ s : Finset n, DifferentiableAt ℂ (fun b => ∏ i ∈ s, M b (σ i) i) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h _ _).fun_mul ih
  exact key _

end GlobalTheory.CompanionTheory.Ar.Flat
end

