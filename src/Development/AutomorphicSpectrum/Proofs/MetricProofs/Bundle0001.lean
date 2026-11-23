module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticDoublingMapLocalInverse
section
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Metric.FamilyInverse

theorem exists_analytic_family_inverse {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [CompleteSpace B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (b₀ : B) (d : B × V → V) (han : AnalyticAt ℂ d (b₀, 0)) (h0 : d (b₀, 0) = 0)
    (hd : HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V) (b₀, 0)) :
    ∃ h : B × V → V, AnalyticAt ℂ h (b₀, 0) ∧ h (b₀, 0) = 0 ∧
      (∀ᶠ p : B × V in 𝓝 (b₀, 0), d (p.1, h p) = p.2) ∧
      (∀ᶠ p : B × V in 𝓝 (b₀, 0), h (p.1, d p) = p.2) := by
  let Φ : B × V → B × V := fun p => (p.1, d p)
  let L : (B × V) →L[ℂ] (B × V) :=
    (ContinuousLinearMap.fst ℂ B V).prod ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V)
  let L' : (B × V) →L[ℂ] (B × V) :=
    (ContinuousLinearMap.fst ℂ B V).prod ((2⁻¹ : ℂ) • ContinuousLinearMap.snd ℂ B V)
  let Le : (B × V) ≃L[ℂ] (B × V) :=
    ContinuousLinearEquiv.equivOfInverse L L'
      (fun p => by simp [L, L', smul_smul]) (fun p => by simp [L, L', smul_smul])
  have hLe : (Le : (B × V) →L[ℂ] (B × V)) = L := rfl
  have hΦan : AnalyticAt ℂ Φ (b₀, 0) := analyticAt_fst.prod han
  have hΦd : HasFDerivAt Φ L (b₀, 0) := hasFDerivAt_fst.prodMk hd
  have hs : HasStrictFDerivAt Φ (Le : (B × V) →L[ℂ] (B × V)) (b₀, 0) := by
    have := hΦan.hasStrictFDerivAt
    rwa [hΦd.fderiv, ← hLe] at this
  have hfix : Φ (b₀, 0) = (b₀, 0) := by simp [Φ, h0]
  let P := hs.toOpenPartialHomeomorph Φ
  have hPc : (P : B × V → B × V) = Φ := hs.toOpenPartialHomeomorph_coe
  have hPan : AnalyticAt ℂ P.symm (P (b₀, 0)) :=
    P.analyticAt_symm' (i := Le) hs.mem_toOpenPartialHomeomorph_source
      (by rw [hPc]; exact hΦan) (by rw [hPc, hΦd.fderiv, hLe])
  have hΨan : AnalyticAt ℂ P.symm (b₀, 0) := by
    have : P (b₀, 0) = (b₀, 0) := by rw [hPc]; exact hfix
    rwa [this] at hPan
  have hright : ∀ᶠ q in 𝓝 (b₀, 0), Φ (P.symm q) = q := by
    have := hs.eventually_right_inverse
    rw [hfix] at this
    exact this
  have hleft : ∀ᶠ p in 𝓝 (b₀, 0), P.symm (Φ p) = p := hs.eventually_left_inverse
  have hΨ0 : P.symm (b₀, 0) = (b₀, 0) := by
    have := hs.localInverse_apply_image
    rw [hfix] at this
    exact this
  refine ⟨fun q => (P.symm q).2, analyticAt_snd.comp hΨan, by simp [hΨ0], ?_, ?_⟩
  · filter_upwards [hright] with q hq
    have e1 := congrArg Prod.fst hq
    have e2 := congrArg Prod.snd hq
    have h1 : (P.symm q).1 = q.1 := e1
    have h2 : d (P.symm q) = q.2 := e2
    have h3 : (q.1, (P.symm q).2) = P.symm q := by rw [← h1]
    rw [h3, h2]
  · filter_upwards [hleft] with p hp
    have e := congrArg Prod.snd hp
    exact e

end GlobalTheory.CompanionTheory.Metric.FamilyInverse
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticGroupLawBoundedCommutator
section
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Metric

theorem norm_le_mul_norm_div_of_bounded_on_ball {V W : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {ψ : V → W} {R M : ℝ}
    (hd : DifferentiableOn ℂ ψ (ball (0 : V) R)) (h0 : ψ 0 = 0)
    (hM : ∀ x ∈ ball (0 : V) R, ‖ψ x‖ ≤ M) {x : V} (hx : x ∈ ball (0 : V) R) :
    ‖ψ x‖ ≤ M * ‖x‖ / R := by
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball (R₂ := M) hd (by
    intro y hy
    rw [mem_closedBall, h0, dist_zero_right]
    exact hM y hy) hx
  rw [h0, dist_zero_right, dist_zero_right] at h
  calc ‖ψ x‖ ≤ M / R * ‖x‖ := h
    _ = M * ‖x‖ / R := by ring

theorem norm_le_of_vanishing_on_axes {B V W : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (b₀ : B) (G : B × V × V → W) (R : ℝ) (hR : 0 < R)
    (hG : DifferentiableOn ℂ G (ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R))
    (hb : ∀ p ∈ ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R, ‖G p‖ ≤ 1)
    (hz : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, G (b, s, 0) = 0 ∧ G (b, 0, s) = 0) :
    ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, ∀ t ∈ ball (0 : V) R,
      ‖G (b, s, t)‖ ≤ ‖s‖ * ‖t‖ / R ^ 2 := by
  intro b hbm s hs t ht

  have h1 : ∀ s ∈ ball (0 : V) R, ∀ t ∈ ball (0 : V) R, ‖G (b, s, t)‖ ≤ ‖s‖ / R := by
    intro s hs t ht
    have hd : DifferentiableOn ℂ (fun s' => G (b, s', t)) (ball (0 : V) R) :=
      hG.comp ((differentiableOn_const b).prodMk (differentiableOn_id.prodMk (differentiableOn_const t)))
        (by intro s' hs'; exact ⟨hbm, hs', ht⟩)
    have h := norm_le_mul_norm_div_of_bounded_on_ball hd (hz b hbm t ht).2
      (fun s' hs' => hb _ ⟨hbm, hs', ht⟩) hs
    rwa [one_mul] at h

  have hd : DifferentiableOn ℂ (fun t' => G (b, s, t')) (ball (0 : V) R) :=
    hG.comp ((differentiableOn_const b).prodMk ((differentiableOn_const s).prodMk differentiableOn_id))
      (by intro t' ht'; exact ⟨hbm, hs, ht'⟩)
  have h := norm_le_mul_norm_div_of_bounded_on_ball hd (hz b hbm s hs).1
    (fun t' ht' => h1 s hs t' ht') ht
  calc ‖G (b, s, t)‖ ≤ ‖s‖ / R * ‖t‖ / R := h
    _ = ‖s‖ * ‖t‖ / R ^ 2 := by ring

end GlobalTheory.CompanionTheory.Metric
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DominatedConvergenceExhaustion
section
open MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.Conv

lemma fatou_real {α : Type} [MeasurableSpace α] {ν : Measure α} {g : ℕ → α → ℝ} {g0 : α → ℝ}
    {c : ℝ} (hi : ∀ k, Integrable (g k) ν) (hnn : ∀ k, ∀ᵐ y ∂ν, 0 ≤ g k y)
    (hlim : ∀ᵐ y ∂ν, Tendsto (fun k => g k y) atTop (𝓝 (g0 y)))
    (hc : ∀ k, ∫ y, g k y ∂ν ≤ c) :
    Integrable g0 ν ∧ ∫ y, g0 y ∂ν ≤ c := by
  have hm : AEStronglyMeasurable g0 ν :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hi k).aestronglyMeasurable) hlim
  have hnn0 : ∀ᵐ y ∂ν, 0 ≤ g0 y := by
    filter_upwards [ae_all_iff.2 hnn, hlim] with y h1 h2
    exact ge_of_tendsto' h2 h1
  have hc0 : 0 ≤ c := (integral_nonneg_of_ae (hnn 0)).trans (hc 0)
  have hk : ∀ k, ∫⁻ y, ENNReal.ofReal (g k y) ∂ν ≤ ENNReal.ofReal c := fun k => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi k) (hnn k)]
    exact ENNReal.ofReal_le_ofReal (hc k)
  have hle : ∫⁻ y, ENNReal.ofReal (g0 y) ∂ν ≤ ENNReal.ofReal c := by
    calc ∫⁻ y, ENNReal.ofReal (g0 y) ∂ν
        = ∫⁻ y, liminf (fun k => ENNReal.ofReal (g k y)) atTop ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hlim] with y hy
          exact ((ENNReal.continuous_ofReal.tendsto _).comp hy).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ y, ENNReal.ofReal (g k y) ∂ν) atTop :=
          lintegral_liminf_le' (fun k => (hi k).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal c := liminf_le_of_frequently_le' (Frequently.of_forall hk)
  have hint : Integrable g0 ν :=
    ⟨hm, (hasFiniteIntegral_iff_ofReal hnn0).2 (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  have := hle
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn0] at this
  exact (ENNReal.ofReal_le_ofReal_iff hc0).1 this

lemma tail_bound {α : Type} [MeasurableSpace α] {μ : Measure α} {S E0 : Set α}
    (hS : MeasurableSet S) (hSE : S ⊆ E0ᶜ) {L ρ Γ : α → ℝ} {a c : ℝ} (ha : 0 ≤ a)
    (hρm : AEStronglyMeasurable ρ μ) (hΓm : AEStronglyMeasurable Γ μ)
    (hρ : ∀ᵐ y ∂μ, 0 ≤ ρ y) (hΓ : ∀ᵐ y ∂μ, y ∉ E0 → |Γ y| ≤ a * L y)
    (hi : IntegrableOn (fun y => L y * ρ y) S μ) (hc : ∫ y in S, L y * ρ y ∂μ ≤ c) :
    IntegrableOn (fun y => Γ y * ρ y) S μ ∧ |∫ y in S, Γ y * ρ y ∂μ| ≤ a * c := by
  have hb : ∀ᵐ y ∂μ.restrict S, ‖Γ y * ρ y‖ ≤ a * (L y * ρ y) := by
    rw [ae_restrict_iff' hS]
    filter_upwards [hρ, hΓ] with y h1 h2 hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (h2 (hSE hy)) h1
  have hi' : Integrable (fun y => a * (L y * ρ y)) (μ.restrict S) := Integrable.const_mul hi a
  refine ⟨Integrable.mono' hi' (hΓm.mul hρm).restrict hb, ?_⟩
  calc |∫ y in S, Γ y * ρ y ∂μ| = ‖∫ y in S, Γ y * ρ y ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y in S, a * (L y * ρ y) ∂μ := norm_integral_le_of_norm_le hi' hb
    _ = a * ∫ y in S, L y * ρ y ∂μ := integral_const_mul _ _
    _ ≤ a * c := mul_le_mul_of_nonneg_left hc ha

theorem tendsto_integral_of_exhaustion {α : Type} [MeasurableSpace α] (μ : Measure α)
    (l : Filter ℝ) [l.NeBot] [l.IsCountablyGenerated] (E : ℕ → Set α) (L : α → ℝ)
    (ρ Γ : ℝ → α → ℝ) (ρ0 Γ0 : α → ℝ) (a : ℝ) (b : ℕ → ℝ)
    (hEm : ∀ n, MeasurableSet (E n)) (hmono : Monotone E) (hfin : ∀ n, μ (E n) < ⊤)
    (hcov : ∀ᵐ y ∂μ, ∃ n, y ∈ E n) (hL : ∀ᵐ y ∂μ, 0 ≤ L y) (ha : 0 ≤ a)
    (hb : Tendsto b atTop (𝓝 0))
    (hρ : ∀ n, TendstoUniformlyOn ρ ρ0 l (E n)) (hΓ : ∀ n, TendstoUniformlyOn Γ Γ0 l (E n))
    (hM : ∀ n, ∃ M : ℝ, ∀ y ∈ E n, |ρ0 y| ≤ M ∧ |Γ0 y| ≤ M)
    (hev : ∀ᶠ t in l, AEStronglyMeasurable (ρ t) μ ∧ AEStronglyMeasurable (Γ t) μ ∧
      (∀ᵐ y ∂μ, 0 ≤ ρ t y) ∧ (∀ᵐ y ∂μ, y ∉ E 0 → |Γ t y| ≤ a * L y) ∧
      ∀ n, IntegrableOn (fun y => L y * ρ t y) (E n)ᶜ μ ∧ ∫ y in (E n)ᶜ, L y * ρ t y ∂μ ≤ b n) :
    Integrable (fun y => Γ0 y * ρ0 y) μ ∧ (∀ᶠ t in l, Integrable (fun y => Γ t y * ρ t y) μ) ∧
      Tendsto (fun t => ∫ y, Γ t y * ρ t y ∂μ) l (𝓝 (∫ y, Γ0 y * ρ0 y ∂μ)) := by
  obtain ⟨u, hu⟩ := exists_seq_tendsto l
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hu.eventually hev)
  have hv : Tendsto (fun k => u (k + K)) atTop l := (tendsto_add_atTop_iff_nat K).2 hu
  have hG := fun k => hK (k + K) (Nat.le_add_left K k)
  have hpt : ∀ᵐ y ∂μ, Tendsto (fun k => ρ (u (k + K)) y) atTop (𝓝 (ρ0 y)) ∧
      Tendsto (fun k => Γ (u (k + K)) y) atTop (𝓝 (Γ0 y)) := by
    filter_upwards [hcov] with y hy
    obtain ⟨n, hn⟩ := hy
    exact ⟨((hρ n).tendsto_at hn).comp hv, ((hΓ n).tendsto_at hn).comp hv⟩
  have hρ0m : AEStronglyMeasurable ρ0 μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hG k).1) (hpt.mono fun _ h => h.1)
  have hΓ0m : AEStronglyMeasurable Γ0 μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hG k).2.1) (hpt.mono fun _ h => h.2)
  have hρ0nn : ∀ᵐ y ∂μ, 0 ≤ ρ0 y := by
    filter_upwards [ae_all_iff.2 (fun k => (hG k).2.2.1), hpt] with y h1 h2
    exact ge_of_tendsto' h2.1 h1
  have hΓ0b : ∀ᵐ y ∂μ, y ∉ E 0 → |Γ0 y| ≤ a * L y := by
    filter_upwards [ae_all_iff.2 (fun k => (hG k).2.2.2.1), hpt] with y h1 h2 hy
    exact le_of_tendsto' h2.2.abs (fun k => h1 k hy)
  have htail0 : ∀ n, IntegrableOn (fun y => L y * ρ0 y) (E n)ᶜ μ ∧
      ∫ y in (E n)ᶜ, L y * ρ0 y ∂μ ≤ b n := fun n =>
    fatou_real (g := fun k y => L y * ρ (u (k + K)) y)
      (fun k => ((hG k).2.2.2.2 n).1)
      (fun k => ae_restrict_of_ae (by
        filter_upwards [hL, (hG k).2.2.1] with y h1 h2
        exact mul_nonneg h1 h2))
      (ae_restrict_of_ae (by
        filter_upwards [hpt] with y h
        exact h.1.const_mul (L y)))
      (fun k => ((hG k).2.2.2.2 n).2)
  have hsub : ∀ n, (E n)ᶜ ⊆ (E 0)ᶜ := fun n =>
    Set.compl_subset_compl.2 (hmono (Nat.zero_le n))
  have htailLim : ∀ n, IntegrableOn (fun y => Γ0 y * ρ0 y) (E n)ᶜ μ ∧
      |∫ y in (E n)ᶜ, Γ0 y * ρ0 y ∂μ| ≤ a * b n := fun n =>
    tail_bound (hEm n).compl (hsub n) ha hρ0m hΓ0m hρ0nn hΓ0b (htail0 n).1 (htail0 n).2
  have htailT : ∀ᶠ t in l, ∀ n, IntegrableOn (fun y => Γ t y * ρ t y) (E n)ᶜ μ ∧
      |∫ y in (E n)ᶜ, Γ t y * ρ t y ∂μ| ≤ a * b n := hev.mono fun t h n =>
    tail_bound (hEm n).compl (hsub n) ha h.1 h.2.1 h.2.2.1 h.2.2.2.1
      (h.2.2.2.2 n).1 (h.2.2.2.2 n).2
  have hB : ∀ n, ∃ C : ℝ, (∀ y ∈ E n, |Γ0 y * ρ0 y| ≤ C) ∧
      ∀ᶠ t in l, ∀ y ∈ E n, |Γ t y * ρ t y| ≤ C := by
    intro n
    obtain ⟨M, hM'⟩ := hM n
    have hC : (0 : ℝ) ≤ |M| + 1 := by positivity
    have key : ∀ x z : ℝ, |x| ≤ |M| + 1 → |z| ≤ |M| + 1 → |x * z| ≤ (|M| + 1) * (|M| + 1) := by
      intro x z h1 h2
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hC
    have near : ∀ x z : ℝ, |z| ≤ M → dist z x < 1 → |x| ≤ |M| + 1 := by
      intro x z h1 h2
      rw [Real.dist_eq] at h2
      have h3 := abs_sub_abs_le_abs_sub x z
      rw [abs_sub_comm x z] at h3
      have h4 := le_abs_self M
      linarith
    refine ⟨(|M| + 1) * (|M| + 1), fun y hy => ?_, ?_⟩
    · have h4 := le_abs_self M
      exact key _ _ (by linarith [(hM' y hy).2]) (by linarith [(hM' y hy).1])
    · filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hρ n) 1 one_pos,
        Metric.tendstoUniformlyOn_iff.1 (hΓ n) 1 one_pos] with t h1 h2 y hy
      exact key _ _ (near _ _ (hM' y hy).2 (h2 y hy)) (near _ _ (hM' y hy).1 (h1 y hy))
  have hhead0 : ∀ n, IntegrableOn (fun y => Γ0 y * ρ0 y) (E n) μ := by
    intro n
    obtain ⟨C, hC, -⟩ := hB n
    exact Measure.integrableOn_of_bounded (hfin n).ne (hΓ0m.mul hρ0m) (M := C)
      (ae_restrict_of_forall_mem (hEm n) hC)
  have hheadT : ∀ n, ∀ᶠ t in l, IntegrableOn (fun y => Γ t y * ρ t y) (E n) μ := by
    intro n
    obtain ⟨C, -, hC⟩ := hB n
    filter_upwards [hev, hC] with t h1 h2
    exact Measure.integrableOn_of_bounded (hfin n).ne (h1.2.1.mul h1.1) (M := C)
      (ae_restrict_of_forall_mem (hEm n) h2)
  have hU : ∀ f : α → ℝ, IntegrableOn f (E 0) μ → IntegrableOn f (E 0)ᶜ μ → Integrable f μ := by
    intro f h1 h2
    have := h1.union h2
    rwa [Set.union_compl_self, integrableOn_univ] at this
  have hI0 : Integrable (fun y => Γ0 y * ρ0 y) μ := hU _ (hhead0 0) (htailLim 0).1
  have hIT : ∀ᶠ t in l, Integrable (fun y => Γ t y * ρ t y) μ := by
    filter_upwards [htailT, hheadT 0] with t h1 h2
    exact hU _ h2 (h1 0).1
  refine ⟨hI0, hIT, ?_⟩
  have hconv : ∀ n, Tendsto (fun t => ∫ y in E n, Γ t y * ρ t y ∂μ) l
      (𝓝 (∫ y in E n, Γ0 y * ρ0 y ∂μ)) := by
    intro n
    obtain ⟨C, -, hC⟩ := hB n
    haveI : IsFiniteMeasure (μ.restrict (E n)) := ⟨by simpa using hfin n⟩
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_
      (integrable_const C) ?_
    · exact hev.mono fun t h => (h.2.1.mul h.1).restrict
    · exact hC.mono fun t h => ae_restrict_of_forall_mem (hEm n) h
    · exact ae_restrict_of_forall_mem (hEm n) fun y hy =>
        ((hΓ n).tendsto_at hy).mul ((hρ n).tendsto_at hy)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hbn : Tendsto (fun n => a * |b n|) atTop (𝓝 0) := by
    simpa using hb.abs.const_mul a
  obtain ⟨n, hn⟩ := (hbn.eventually (Iio_mem_nhds hε3)).exists
  have hn' : a * |b n| < ε / 3 := hn
  have hab : a * b n ≤ a * |b n| := mul_le_mul_of_nonneg_left (le_abs_self _) ha
  filter_upwards [Metric.tendsto_nhds.1 (hconv n) (ε / 3) hε3, htailT, hIT] with t h1 h2 h3
  have e1 : ∫ y in E n, Γ t y * ρ t y ∂μ + ∫ y in (E n)ᶜ, Γ t y * ρ t y ∂μ =
      ∫ y, Γ t y * ρ t y ∂μ := integral_add_compl (hEm n) h3
  have e2 : ∫ y in E n, Γ0 y * ρ0 y ∂μ + ∫ y in (E n)ᶜ, Γ0 y * ρ0 y ∂μ =
      ∫ y, Γ0 y * ρ0 y ∂μ := integral_add_compl (hEm n) hI0
  have A := (h2 n).2
  have B := (htailLim n).2
  rw [Real.dist_eq] at h1 ⊢
  rw [← e1, ← e2]
  rw [abs_lt] at h1 ⊢
  rw [abs_le] at A B
  constructor <;> linarith [h1.1, h1.2, A.1, A.2, B.1, B.2]

end GlobalTheory.CompanionTheory.Conv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EqNegSumIicDifferences
section
open Matrix

namespace GlobalTheory.CompanionTheory.Metric.Telescope

theorem fin_iic_telescope : ∀ (N : ℕ) (M : Type) [AddCommGroup M] (f : Fin N → M) (i : Fin N),
    f i = -∑ k ∈ Finset.Iic i, (if h : (k : ℕ) = 0 then -f k else
      f ⟨(k : ℕ) - 1, by have := k.2; omega⟩ - f k) := by
  intro N M _ f i
  obtain ⟨n, hn⟩ := i
  induction n with
  | zero =>
    have hset : Finset.Iic (⟨0, hn⟩ : Fin N) = {⟨0, hn⟩} := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    rw [hset, Finset.sum_singleton, dite_eq_left rfl, neg_neg]
  | succ n ih =>
    have hn' : n < N := by omega
    have hset : Finset.Iic (⟨n + 1, hn⟩ : Fin N) = insert ⟨n + 1, hn⟩ (Finset.Iic ⟨n, hn'⟩) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    have hnot : (⟨n + 1, hn⟩ : Fin N) ∉ Finset.Iic ⟨n, hn'⟩ := by
      simp only [Finset.mem_Iic, Fin.le_iff_val_le_val, not_le]
      omega
    have hs := (neg_eq_iff_eq_neg.mpr (ih hn')).symm
    rw [hset, Finset.sum_insert hnot, dite_eq_right (by simp), hs]
    have e : ∀ p, f ⟨(⟨n + 1, hn⟩ : Fin N).val - 1, p⟩ = f ⟨n, hn'⟩ :=
      fun p => congrArg f (Fin.ext (by simp))
    rw [e]
    abel

end GlobalTheory.CompanionTheory.Metric.Telescope
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def nS (a : ℂ) (i : Fin 3) : ℝ := (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)

def wS (a : ℂ) : ℝ := ((1 + ‖a‖ ^ 2) ^ 2)⁻¹

def blk {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.of fun p q : Fin (d + 1) =>
    Fin.cases (Fin.cases e (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => B p' q') q) p

def lin3 (n : Fin 3 → ℝ) : MvPolynomial (Fin 3) ℝ := ∑ i, X i * C (n i)

def lin4 (n : Fin 3 → ℝ) : MvPolynomial (Option (Fin 3)) ℝ := rename some (lin3 n)

def rowW (u : Fin 2 → ℝ) (v : ℝ) : MvPolynomial (Option (Fin 2)) ℝ :=
  C (u 0) * X (some 0) + C (u 1) * X (some 1) + C v * X none

def evalW (n₀ n₁ : Fin 3 → ℝ) : MvPolynomial (Option (Fin 2)) ℝ →ₐ[ℝ] MvPolynomial (Option (Fin 3)) ℝ :=
  aeval fun j => Option.elim j (X none) ![lin4 n₀, lin4 n₁]

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsFundamentalDomainOfRelIndexNeZero
section
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_isFundamentalDomain_of_relIndex_ne_zero :
    ∀ (G X : Type) [Group G] [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X]
      (μ : Measure X) [SMulInvariantMeasure G X μ] (Γ₀ Γ : Subgroup G) [Countable Γ] (s : Set X),
      Γ₀ ≤ Γ → Γ₀.relIndex Γ ≠ 0 → IsFundamentalDomain Γ s μ →
      ∃ t : Set X, IsFundamentalDomain Γ₀ t μ ∧ μ t = (Γ₀.relIndex Γ : ℝ≥0∞) * μ s := by
  intro G X _ _ _ _ μ _ Γ₀ Γ _ s hle hidx hs
  classical
  set H : Subgroup Γ := Γ₀.subgroupOf Γ with hH
  have : H.FiniteIndex := ⟨hidx⟩
  let _ : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  let ρ : Γ ⧸ H → Γ := fun q => q.out
  have hout : ∀ q : Γ ⧸ H, ((ρ q : Γ) : Γ ⧸ H) = q := fun q => QuotientGroup.out_eq' q
  have hρ : ∀ γ : Γ, (ρ (γ : Γ ⧸ H))⁻¹ * γ ∈ H := fun γ => QuotientGroup.eq.mp (hout _)
  let ι : Γ₀ → Γ := fun g => ⟨g, hle g.2⟩
  have key : ∀ (g : Γ₀) (γ : Γ), g • (γ • s) = (ι g * γ) • s := by
    intro g γ
    rw [mul_smul]
    rfl
  let t : Set X := ⋃ q : Γ ⧸ H, (ρ q)⁻¹ • s
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) fun q : Γ ⧸ H => (ρ q)⁻¹ • s) := by
    intro q q' hqq'
    apply hs.aedisjoint
    intro heq
    apply hqq'
    have h1 : ρ q = ρ q' := inv_injective heq
    rw [← hout q, ← hout q', h1]
  refine ⟨t, ⟨NullMeasurableSet.iUnion fun q => hs.nullMeasurableSet_smul _, ?_, ?_⟩, ?_⟩
  · filter_upwards [hs.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    refine ⟨⟨(((ρ (γ : Γ ⧸ H))⁻¹ * γ : Γ) : G), Subgroup.mem_subgroupOf.mp (hρ γ)⟩, ?_⟩
    refine Set.mem_iUnion.2 ⟨(γ : Γ ⧸ H), ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    convert hγ using 1
    simp [Subgroup.smul_def, smul_smul]
  · intro g g' hgg'
    show AEDisjoint μ (g • t) (g' • t)
    simp only [t, Set.smul_set_iUnion]
    rw [AEDisjoint.iUnion_left_iff]
    intro q
    rw [AEDisjoint.iUnion_right_iff]
    intro q'
    rw [key, key]
    apply hs.aedisjoint
    intro heq
    apply hgg'
    have h1 : (ρ q')⁻¹ * ρ q = (ι g')⁻¹ * ι g := by
      calc (ρ q')⁻¹ * ρ q = (ι g')⁻¹ * (ι g' * (ρ q')⁻¹) * ρ q := by group
        _ = (ι g')⁻¹ * (ι g * (ρ q)⁻¹) * ρ q := by rw [heq]
        _ = (ι g')⁻¹ * ι g := by group
    have h2 : (ι g')⁻¹ * ι g ∈ H := by
      rw [Subgroup.mem_subgroupOf]
      simpa [ι] using Γ₀.mul_mem (Γ₀.inv_mem g'.2) g.2
    have h3 : q' = q := by
      rw [← hout q', ← hout q]
      exact QuotientGroup.eq.mpr (h1 ▸ h2)
    subst h3
    have h4 : ι g = ι g' := mul_right_cancel heq
    have h5 : ((ι g : Γ) : G) = ((ι g' : Γ) : G) := by rw [h4]
    exact Subtype.ext h5
  · rw [measure_iUnion₀ hdisj (fun q => hs.nullMeasurableSet_smul _)]
    have hm : ∀ q, μ ((ρ q)⁻¹ • s) = μ s := fun q => by
      show μ (((ρ q)⁻¹ : Γ) • s) = μ s
      rw [show ((ρ q)⁻¹ : Γ) • s = (((ρ q)⁻¹ : Γ) : G) • s from rfl]
      exact measure_smul μ _ _
    simp only [hm, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [← Nat.card_eq_fintype_card]
    rfl

end GlobalTheory.CompanionTheory.Ar.Cmp
end

