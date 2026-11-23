module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0201
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0211
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0195
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0215

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyEstimateOfLengthFunction
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.WaveSpd.LocEnergy

variable {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def cw (ℓ : Mat n → ℝ) (χ : ℝ → ℝ) (C r s : ℝ) (y : Mat n) : ℝ := χ (ℓ y + C * s - r)

theorem sm_cw {ℓ : Mat n → ℝ} {χ : ℝ → ℝ} (C r : ℝ) (hℓ : ContDiffOn ℝ ∞ ℓ (GLs n))
    (hχ : ContDiff ℝ ∞ χ) : Sm (cw ℓ χ C r) := by
  have h1 : ContDiffOn ℝ ∞ (fun q : ℝ × Mat n => ℓ q.2 + C * q.1 - r) (Set.univ ×ˢ GLs n) := by
    have h2 : ContDiffOn ℝ ∞ (fun q : ℝ × Mat n => ℓ q.2) (Set.univ ×ˢ GLs n) :=
      hℓ.comp contDiff_snd.contDiffOn (fun q hq => hq.2)
    have h3 : ContDiffOn ℝ ∞ (fun q : ℝ × Mat n => C * q.1) (Set.univ ×ˢ GLs n) :=
      (contDiff_const.mul contDiff_fst).contDiffOn
    exact (h2.add h3).sub contDiffOn_const
  exact hχ.comp_contDiffOn h1

theorem sm_mul {f g : ℝ → Mat n → ℝ} (hf : Sm f) (hg : Sm g) : Sm fun s y => f s y * g s y :=
  ContDiffOn.mul hf hg

theorem hasDerivAt_chi {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (a : ℝ) : HasDerivAt χ (deriv χ a) a :=
  ((hχ.differentiable (by simp)) a).hasDerivAt

theorem hasDerivAt_cw {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (ℓ : Mat n → ℝ) (C r s : ℝ) (y : Mat n) :
    HasDerivAt (fun s' => cw ℓ χ C r s' y) (deriv χ (ℓ y + C * s - r) * C) s := by
  have h1 : HasDerivAt (fun s' : ℝ => ℓ y + C * s' - r) C s := by
    simpa using (((hasDerivAt_id s).const_mul C).const_add (ℓ y)).sub_const r
  exact (hasDerivAt_chi hχ _).comp s h1

theorem dt_rho {ℓ : Mat n → ℝ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {u : ℝ → Mat n → W} (hu : Sm u)
    (C r s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    dt (fun s y => cw ℓ χ C r s y * dens u s y) s y =
      deriv χ (ℓ y + C * s - r) * C * dens u s y + cw ℓ χ C r s y *
        (2 * ⟪dt (dt u) s y, dt u s y⟫_ℝ
          + (1 / 2) * ∑ p : Ix n, ⟪Rr (hm p) (dt u s) y, Rt (hm p) u s y⟫_ℝ
          + 2 * ⟪dt u s y, u s y⟫_ℝ) :=
  ((hasDerivAt_cw hχ ℓ C r s y).mul (GlobalTheory.T.energy_density_time_derivative u hu s y hy)).deriv

theorem rr_cw_inner {ℓ : Mat n → ℝ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (C r s : ℝ)
    {f g : Mat n → W} {y : Mat n} (hℓ : DifferentiableAt ℝ ℓ y) (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (X : Mat n) :
    Rr X (fun y' => cw ℓ χ C r s y' * ⟪f y', g y'⟫_ℝ) y =
      deriv χ (ℓ y + C * s - r) * fderiv ℝ ℓ y (y * X) * ⟪f y, g y⟫_ℝ +
        cw ℓ χ C r s y * (⟪Rr X f y, g y⟫_ℝ + ⟪f y, Rr X g y⟫_ℝ) := by
  have h1 : HasFDerivAt (fun y' => cw ℓ χ C r s y')
      (deriv χ (ℓ y + C * s - r) • fderiv ℝ ℓ y) y :=
    (hasDerivAt_chi hχ _).comp_hasFDerivAt y ((hℓ.hasFDerivAt.add_const (C * s)).sub_const r)
  have h2 : HasFDerivAt (fun t => ⟪f t, g t⟫_ℝ) (fderiv ℝ (fun t => ⟪f t, g t⟫_ℝ) y) y :=
    (hf.inner ℝ hg).hasFDerivAt
  have h3 : HasFDerivAt (fun y' => cw ℓ χ C r s y' * ⟪f y', g y'⟫_ℝ) _ y := h1.mul h2
  have h4 : fderiv ℝ (fun t => ⟪f t, g t⟫_ℝ) y (y * X) =
      ⟪f y, Rr X g y⟫_ℝ + ⟪Rr X f y, g y⟫_ℝ := fderiv_inner_apply ℝ hf hg (y * X)
  have h5 : fderiv ℝ (fun y' => cw ℓ χ C r s y' * ⟪f y', g y'⟫_ℝ) y (y * X) =
      cw ℓ χ C r s y * fderiv ℝ (fun t => ⟪f t, g t⟫_ℝ) y (y * X) +
        ⟪f y, g y⟫_ℝ * (deriv χ (ℓ y + C * s - r) * fderiv ℝ ℓ y (y * X)) := by
    rw [h3.fderiv]
    rfl
  show fderiv ℝ (fun y' => cw ℓ χ C r s y' * ⟪f y', g y'⟫_ℝ) y (y * X) = _
  rw [h5, h4]
  ring

theorem diffAt_of_sm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {y : Mat n} (hy : y ∈ GLs n) : DifferentiableAt ℝ f y :=
  (hf.contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)

theorem pt_bound {ℓ : Mat n → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ (GLs n)) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ' : ∀ x, deriv χ x ≤ 0) (hχ0 : ∀ x, 0 ≤ χ x)
    {u : ℝ → Mat n → W} (hu : Sm u) (A : W →L[ℝ] W)
    (hwave : ∀ s, ∀ y ∈ GLs n, dt (dt u) s y =
      (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y))
    {C₁ C : ℝ} (r : ℝ) (hC₁ : 0 ≤ C₁) (hC : C₁ * (1 + Fintype.card (Ix n)) ≤ C)
    (hL : ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ ℓ y (y * hm p)| ≤ C₁)
    (s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    dt (fun s y => cw ℓ χ C r s y * dens u s y) s y -
        (1 / 2) * ∑ p : Ix n,
          Rr (hm p) (fun y' => cw ℓ χ C r s y' * ⟪Rt (hm p) u s y', dt u s y'⟫_ℝ) y ≤
      (‖A‖ + 1) * (cw ℓ χ C r s y * dens u s y) := by
  have hdu := (_root_.GlobalTheory.CompanionTheory.WaveSpd.sm_calculus u hu).1
  have hRt := (_root_.GlobalTheory.CompanionTheory.WaveSpd.sm_calculus u hu).2.1
  have hℓd := diffAt_of_sm hℓ hy
  have hw : DifferentiableAt ℝ (dt u s) y := diffAt_of_sm ((_root_.GlobalTheory.CompanionTheory.WaveSpd.sm_calculus _ hdu).2.2.1 s) hy
  have hY : ∀ p : Ix n, DifferentiableAt ℝ (Rt (hm p) u s) y :=
    fun p => diffAt_of_sm ((_root_.GlobalTheory.CompanionTheory.WaveSpd.sm_calculus _ (hRt _)).2.2.1 s) hy
  have hpt := _root_.GlobalTheory.CompanionTheory.WaveSpd.pointwise_energy_ineq (dt u s y) (u s y) (fun p : Ix n => Rt (hm p) u s y)
    (fun p => fderiv ℝ ℓ y (y * hm p)) A C₁ C (deriv χ (ℓ y + C * s - r)) (cw ℓ χ C r s y)
    hC₁ hC (hχ' _) (hχ0 _) (fun p => hL y hy p)
  have hD : ‖dt u s y‖ ^ 2 + (1 / 4) * ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 + ‖u s y‖ ^ 2
      = dens u s y := rfl
  rw [hD] at hpt
  have e1 : ⟪(1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y), dt u s y⟫_ℝ
      = (1 / 4) * ∑ p : Ix n, ⟪Rr (hm p) (Rt (hm p) u s) y, dt u s y⟫_ℝ
        + ⟪A (u s y), dt u s y⟫_ℝ := by
    rw [inner_add_left, real_inner_smul_left, sum_inner]
  have e2 : ∑ p : Ix n,
      Rr (hm p) (fun y' => cw ℓ χ C r s y' * ⟪Rt (hm p) u s y', dt u s y'⟫_ℝ) y =
      ∑ p : Ix n, deriv χ (ℓ y + C * s - r) * fderiv ℝ ℓ y (y * hm p) *
          ⟪Rt (hm p) u s y, dt u s y⟫_ℝ +
        cw ℓ χ C r s y * (∑ p : Ix n, ⟪Rr (hm p) (Rt (hm p) u s) y, dt u s y⟫_ℝ +
          ∑ p : Ix n, ⟪Rr (hm p) (dt u s) y, Rt (hm p) u s y⟫_ℝ) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rr_cw_inner hχ C r s hℓd (hY p) hw (hm p), real_inner_comm (Rt (hm p) u s y)]
  rw [dt_rho hχ hu C r s hy, hwave s y hy, e1, e2]
  refine le_trans (le_of_eq ?_) hpt
  ring

theorem integrable_of_val [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] {f : Mat n → ℝ} (hf : ContinuousOn f (GLs n)) {K : Set (G n)}
    (hK : IsCompact K) (h : ∀ y : G n, y ∉ K → f y.val = 0) :
    Integrable (fun y : G n => f y.val) μ :=
  (hf.comp_continuous Units.continuous_val val_mem_GLs).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hK h)

theorem energy_diff_ineq : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (ℓ : Mat n → ℝ), ContDiffOn ℝ ∞ ℓ (GLs n) → (∀ R : ℝ, IsCompact {y : G n | ℓ y.val ≤ R}) → ∀ (C₁ : ℝ), 0 ≤ C₁ → (∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ ℓ y (y * hm p)| ≤ C₁) → (∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < ℓ y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0) → ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → (∀ x, deriv χ x ≤ 0) → (∀ x, 0 ≤ χ x) → (∀ x, 1 ≤ x → χ x = 0) → ∀ (u : ℝ → Mat n → W), Sm u → ∀ (A : W →L[ℝ] W), (∀ s, ∀ y ∈ GLs n, dt (dt u) s y = (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y)) → ∀ (C : ℝ), C₁ * (1 + Fintype.card (Ix n)) ≤ C → ∀ (r : ℝ), ∃ K : ℝ, ∀ s, ∃ e' : ℝ, HasDerivAt (fun s' => ∫ y : G n, χ (ℓ y.val + C * s' - r) * dens u s' y.val ∂μ) e' s ∧ e' ≤ K * ∫ y : G n, χ (ℓ y.val + C * s - r) * dens u s y.val ∂μ := by
  intro n W _ _ _ _ μ _ ℓ hℓ hcpt C₁ hC₁ hL hIBP χ hχ hχ' hχ0 hχ1 u hu A hwave C hC r
  refine ⟨‖A‖ + 1, fun s => ?_⟩
  have hC0 : 0 ≤ C := le_trans (mul_nonneg hC₁ (by positivity)) hC
  have hdu := (_root_.GlobalTheory.CompanionTheory.WaveSpd.sm_calculus u hu).1
  have hcw := sm_cw C r hℓ hχ
  let ρ : ℝ → Mat n → ℝ := fun s y => cw ℓ χ C r s y * dens u s y
  have hρ : Sm ρ := sm_mul hcw (GlobalTheory.T.energy_density_smooth u hu).1
  let Ψ : Ix n → ℝ → Mat n → ℝ :=
    fun p s y => cw ℓ χ C r s y * ⟪Rt (hm p) u s y, dt u s y⟫_ℝ
  have hΨ : ∀ p, Sm (Ψ p) := fun p => sm_mul hcw ((GlobalTheory.T.energy_density_smooth u hu).2 _ _ hdu)
  obtain ⟨R, hR⟩ : ∃ R, R = r + 1 + C * (|s| + 1) := ⟨_, rfl⟩
  have hK : IsCompact {y : G n | ℓ y.val ≤ R} := hcpt R
  have hvan : ∀ s' ∈ Metric.ball s 1, ∀ y : G n, y ∉ {y : G n | ℓ y.val ≤ R} →
      ρ s' y.val = 0 := by
    intro s' hs' y hy
    have hy' : R < ℓ y.val := not_le.1 hy
    have h0 : 0 ≤ |s| + 1 + s' := by
      have h1 := neg_abs_le s
      have h2 := (abs_lt.1 (Real.dist_eq s' s ▸ Metric.mem_ball.1 hs')).1
      linarith
    have h3 := mul_nonneg hC0 h0
    have h4 : 1 ≤ ℓ y.val + C * s' - r := by rw [hR] at hy'; nlinarith
    simp only [ρ, cw, hχ1 _ h4, zero_mul]
  have hder := GlobalTheory.T.deriv_integral_compact_support μ ρ hρ _ hK s 1 one_pos hvan
  refine ⟨_, hder, ?_⟩
  have hdtvan : ∀ y : G n, y ∉ {y : G n | ℓ y.val ≤ R} → dt ρ s y.val = 0 := by
    intro y hy
    have h1 : (fun r' => ρ r' y.val) =ᶠ[nhds s] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds s one_pos] with s' hs' using hvan s' hs' y hy
    show deriv (fun r' => ρ r' y.val) s = 0
    rw [h1.deriv_eq]; simp
  have I_dt := integrable_of_val μ
    ((_root_.GlobalTheory.CompanionTheory.WaveSpd.sm_calculus _ (_root_.GlobalTheory.CompanionTheory.WaveSpd.sm_calculus _ hρ).1).2.2.1 s).continuousOn hK hdtvan
  have I_ρ := integrable_of_val μ ((_root_.GlobalTheory.CompanionTheory.WaveSpd.sm_calculus _ hρ).2.2.1 s).continuousOn hK
    (hvan s (Metric.mem_ball_self one_pos))
  have hRs : r + 1 - C * s ≤ R := by
    have h1 := neg_abs_le s
    have h2 : 0 ≤ C * (|s| + 1 + s) := mul_nonneg hC0 (by linarith)
    rw [hR]; nlinarith
  have hrrvan : ∀ (p : Ix n) (y : G n), y ∉ {y : G n | ℓ y.val ≤ R} →
      Rr (hm p) (Ψ p s) y.val = 0 := by
    intro p y hy
    have hy' : R < ℓ y.val := not_le.1 hy
    have hcont : ContinuousAt ℓ y.val := (diffAt_of_sm hℓ (val_mem_GLs y)).continuousAt
    have h1 : Ψ p s =ᶠ[nhds y.val] fun _ => 0 := by
      filter_upwards [hcont.eventually (lt_mem_nhds hy')] with z hz
      have h4 : 1 ≤ ℓ z + C * s - r := by linarith
      simp only [Ψ, cw, hχ1 _ h4, zero_mul]
    show fderiv ℝ (Ψ p s) y.val _ = 0
    rw [h1.fderiv_eq]; simp
  have I_rr : ∀ p : Ix n, Integrable (fun y : G n => Rr (hm p) (Ψ p s) y.val) μ := fun p =>
    integrable_of_val μ
      ((_root_.GlobalTheory.CompanionTheory.WaveSpd.sm_calculus _ ((_root_.GlobalTheory.CompanionTheory.WaveSpd.sm_calculus _ (hΨ p)).2.1 (hm p))).2.2.1 s).continuousOn hK
      (hrrvan p)
  have hZ : ∀ p : Ix n, ∫ y : G n, Rr (hm p) (Ψ p s) y.val ∂μ = 0 := fun p =>
    hIBP (Ψ p s) ((_root_.GlobalTheory.CompanionTheory.WaveSpd.sm_calculus _ (hΨ p)).2.2.1 s)
      ⟨r + 1 - C * s, fun y _ hy => by
        have h4 : 1 ≤ ℓ y + C * s - r := by linarith
        simp only [Ψ, cw, hχ1 _ h4, zero_mul]⟩ (hm p)
  have I_sum : Integrable (fun y : G n => (1 / 2 : ℝ) * ∑ p : Ix n, Rr (hm p) (Ψ p s) y.val) μ :=
    (integrable_finsetSum _ fun p _ => I_rr p).const_mul _
  calc ∫ y : G n, dt ρ s y.val ∂μ
      = ∫ y : G n, (dt ρ s y.val - (1 / 2 : ℝ) * ∑ p : Ix n, Rr (hm p) (Ψ p s) y.val) ∂μ := by
        rw [integral_sub I_dt I_sum, integral_const_mul,
          integral_finsetSum _ fun p _ => I_rr p]
        simp [hZ]
    _ ≤ ∫ y : G n, (‖A‖ + 1) * ρ s y.val ∂μ :=
        integral_mono (I_dt.sub I_sum) (I_ρ.const_mul _) fun y =>
          pt_bound hℓ hχ hχ' hχ0 hu A hwave r hC₁ hC hL s (val_mem_GLs y)
    _ = (‖A‖ + 1) * ∫ y : G n, ρ s y.val ∂μ := integral_const_mul _ _

end GlobalTheory.CompanionTheory.WaveSpd.LocEnergy
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPowMulMemInteger
section
open PositivityTheory.JacquetShalikaLocal MeasureTheory
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

section Lat

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]


open GroundTheory.Automorphic.GLnLocal in
theorem exists_pow_mul_mem_integer (a : F) :
    ∃ M : ℕ, (uniformizer F : F) ^ M * a ∈ 𝒪[F] := by
  by_cases ha : a ∈ 𝒪[F]
  · exact ⟨0, by simpa using ha⟩
  · have ha0 : a ≠ 0 := fun h => ha (h ▸ zero_mem _)
    have hinv : a⁻¹ ∈ 𝒪[F] := by
      rw [Valuation.mem_integer_iff] at ha ⊢
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp ha))
    have hne : (⟨a⁻¹, hinv⟩ : 𝒪[F]) ≠ 0 := fun h => inv_ne_zero ha0 (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne (irreducible_uniformizer F)
    refine ⟨n, ?_⟩
    have hu' : ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (⟨a⁻¹, hinv⟩ : 𝒪[F]) = uniformizer F ^ n := by
      rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
    have h2 := congrArg Subtype.val hu'
    push_cast at h2
    have key : (uniformizer F : F) ^ n * a = (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) := by
      rw [← h2, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
    rw [key]
    exact SetLike.coe_mem _


open GroundTheory.Automorphic.GLnLocal in
theorem pow_mul_mem_of_le {M M' : ℕ} (h : M ≤ M') {a : F}
    (ha : (uniformizer F : F) ^ M * a ∈ 𝒪[F]) : (uniformizer F : F) ^ M' * a ∈ 𝒪[F] := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, mul_comm ((uniformizer F : F) ^ M), mul_assoc]
  exact mul_mem (pow_mem (uniformizer F).2 d) ha

theorem lat_mono {m M M' : ℕ} (h : M ≤ M') : lat F m M ⊆ lat F m M' := by
  intro x hx
  simp only [lat, Set.mem_ofPred_eq] at hx ⊢
  exact fun i => pow_mul_mem_of_le h (hx i)

theorem exists_mem_lat {m : ℕ} (y : Fin m → F) : ∃ M, y ∈ lat F m M := by
  choose N hN using fun i => exists_pow_mul_mem_integer (y i)
  refine ⟨Finset.univ.sup N, ?_⟩
  simp only [lat, Set.mem_ofPred_eq]
  exact fun i => pow_mul_mem_of_le (Finset.le_sup (Finset.mem_univ i)) (hN i)

theorem add_mem_lat {m M : ℕ} {x y : Fin m → F} (hx : x ∈ lat F m M) (hy : y ∈ lat F m M) :
    x + y ∈ lat F m M := by
  simp only [lat, Set.mem_ofPred_eq] at hx hy ⊢
  intro i
  rw [Pi.add_apply, mul_add]
  exact add_mem (hx i) (hy i)

theorem sub_mem_lat {m M : ℕ} {x y : Fin m → F} (hx : x ∈ lat F m M) (hy : y ∈ lat F m M) :
    x - y ∈ lat F m M := by
  simp only [lat, Set.mem_ofPred_eq] at hx hy ⊢
  intro i
  rw [Pi.sub_apply, mul_sub]
  exact sub_mem (hx i) (hy i)

theorem setIntegral_lat_add [MeasurableSpace F] [BorelSpace F] (μ : Measure F)
    [μ.IsAddHaarMeasure] {m M : ℕ} (hmeas : MeasurableSet (lat F m M))
    {y : Fin m → F} (hy : y ∈ lat F m M) (f : (Fin m → F) → ℂ) :
    ∫ x in lat F m M, f (x + y) ∂(Measure.pi fun _ => μ)
      = ∫ x in lat F m M, f x ∂(Measure.pi fun _ => μ) := by
  have hpre : (fun x => y + x) ⁻¹' lat F m M = lat F m M := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro h
      have h' := sub_mem_lat h hy
      rwa [add_sub_cancel_left] at h'
    · intro h
      exact add_mem_lat hy h
  have hmp := measurePreserving_add_left (Measure.pi fun _ : Fin m => μ) y
  have e := hmp.setIntegral_preimage_emb (measurableEmbedding_addLeft y) f (lat F m M)
  rw [hpre] at e
  simp only [add_comm y] at e
  exact e

end Lat

theorem equivariant_of_steps : L0 → ColumnsMirabolic → ColumnsUnipotent → FormCoefficientStability → FormEquivariantColumn := by
  intro hL0 hL3c hL3d _
  unfold L0 ColumnsMirabolic ColumnsUnipotent FormEquivariantColumn ForR ForF at *
  intro F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ _ l k B B' hk hInv hChar g hg u u'
  obtain ⟨-, hlat⟩ := hL0 F μ ψ hψ
  have hmeas : ∀ M, MeasurableSet (lat F (k + 1) M) := fun M => ((hlat (k + 1)).1 M).2.2.1
  obtain ⟨hadd, -⟩ := hL3c F μ ψ hψ n k hk
  obtain ⟨hd1, hd2⟩ := hL3d F μ ψ hψ n k hk
  obtain ⟨-, -, -, -, hequi⟩ := hInv
  obtain ⟨g', x₀, hg', rfl, hpsi⟩ := hd1 g hg
  obtain ⟨M₁, hM₁⟩ := hChar ((ρ (g' * col n k x₀)) u) u'
  obtain ⟨M₂, hM₂⟩ := hChar u u'
  obtain ⟨M₃, hM₃⟩ := exists_mem_lat x₀
  have hx₀ : x₀ ∈ lat F (k + 1) (M₁ + M₂ + M₃) := lat_mono (by omega) hM₃
  have hpt : ∀ x : Fin (k + 1) → F,
      ψ (-x (Fin.last k)) * (B u') ((ρ (col n k x)) ((ρ (g' * col n k x₀)) u)) =
        GroundTheory.Automorphic.Whittaker.psiN ψ g' * ψ (x₀ (Fin.last k)) *
          (ψ (-(x + x₀) (Fin.last k)) * (B u') ((ρ (col n k (x + x₀))) u)) := by
    intro x
    obtain ⟨g'', hg'', hc, hps⟩ := hd2 g' hg' x
    have hr : (ρ (col n k x)) ((ρ (g' * col n k x₀)) u) = (ρ g'') ((ρ (col n k (x + x₀))) u) := by
      rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, hc, mul_assoc, ← hadd, map_mul,
        Module.End.mul_apply]
    have hψ' : ψ (-x (Fin.last k)) = ψ (x₀ (Fin.last k)) * ψ (-(x + x₀) (Fin.last k)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      rw [Pi.add_apply]
      ring
    rw [hr, hequi g'' hg'', hps, hψ']
    ring
  rw [hM₁ (M₁ + M₂ + M₃) (by omega), hM₂ (M₁ + M₂ + M₃) (by omega), hpsi]
  simp_rw [hpt]
  rw [integral_const_mul]
  have e := setIntegral_lat_add μ (hmeas (M₁ + M₂ + M₃)) hx₀
    (fun x => ψ (-x (Fin.last k)) * (B u') ((ρ (col n k x)) u))
  beta_reduce at e
  rw [e]

end GlobalTheory.CompanionTheory.SatakeBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinalFormBesselBound
section
noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem inv_top {n : ℕ} (hn : 1 < n) {ρ : Representation ℂ (GL (Fin n) F) V} {ψ : AddChar F ℂ}
    {l : V →ₗ[ℂ] ℂ} {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hU : Unit' ρ B) : Inv ρ ψ l (n - 1) B := by
  obtain ⟨hh, hp, hi⟩ := hU
  refine ⟨hh, fun u => ?_, fun u hu => ?_, fun g _ u u' => ?_, fun g hg u u' => ?_⟩
  · by_cases h : u = 0
    · simp [h]
    · exact (hp u h).le
  · by_cases h : u = 0
    · simp [h]
    · have := hp u h
      rw [hu] at this
      simp at this
  · rw [hi, Nat.sub_self, pow_zero, one_mul]
  · have h1 : g = 1 := by
      apply Units.ext
      ext i j
      exact hg.2 i j (by omega)
    subst h1
    rw [Whittaker.psiN_one]
    simp

theorem inv_step [MeasurableSpace F] [BorelSpace F] (h4a : StableAverageExists) (h4b : FormHermitianPositive) (h4c : FormQuasiInvariantMirabolic) (h4d : FormEquivariantColumn)
    (μ : Measure F) [μ.IsAddHaarMeasure] {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {n : ℕ}
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : Smooth ρ) {l : V →ₗ[ℂ] ℂ} (hW : Whit ρ ψ l)
    {k : ℕ} (hk : k + 1 < n) {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hB : Inv ρ ψ l (k + 1) B) :
    ∃ B', Char μ ρ ψ k B B' ∧ Inv ρ ψ l k B' := by
  obtain ⟨B', hC⟩ := h4a F μ ψ hψ n V ρ hρ l k B hk hB
  obtain ⟨hh, hp, hz⟩ := h4b F μ ψ hψ n V ρ hρ l k B B' hk hW hB hC
  exact ⟨B', hC, hh, hp, hz, h4c F μ ψ hψ n V ρ hρ l k B B' hk hB hC,
    h4d F μ ψ hψ n V ρ hρ l k B B' hk hB hC⟩

theorem inv_down [MeasurableSpace F] [BorelSpace F] (h4a : StableAverageExists) (h4b : FormHermitianPositive) (h4c : FormQuasiInvariantMirabolic) (h4d : FormEquivariantColumn)
    (μ : Measure F) [μ.IsAddHaarMeasure] {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {n : ℕ} (hn : 1 < n)
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : Smooth ρ) {l : V →ₗ[ℂ] ℂ} (hW : Whit ρ ψ l)
    {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hU : Unit' ρ B) (d : ℕ) (hd : d ≤ n - 2) :
    ∃ B₁, Inv ρ ψ l (n - 1 - d) B₁ := by
  induction d with
  | zero => exact ⟨B, inv_top hn hU⟩
  | succ d ih =>
    obtain ⟨B₁, h₁⟩ := ih (by omega)
    have e : n - 1 - d = n - 1 - (d + 1) + 1 := by omega
    rw [e] at h₁
    obtain ⟨B₂, -, h₂⟩ := inv_step h4a h4b h4c h4d μ hψ hρ hW (by omega) h₁
    exact ⟨B₂, h₂⟩

theorem final_form_bessel_bound : StableAverageExists → FormHermitianPositive → FormQuasiInvariantMirabolic → FormEquivariantColumn → L5 → L6 := by
  intro h4a h4b h4c h4d h5 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l B hn hW hU
  obtain ⟨B₁, h₁⟩ := inv_down h4a h4b h4c h4d μ hψ hn hρ hW hU (n - 2) le_rfl
  have e : n - 1 - (n - 2) = 0 + 1 := by omega
  rw [e] at h₁
  obtain ⟨B', hC, h'⟩ := inv_step h4a h4b h4c h4d μ hψ hρ hW (k := 0) (by omega) h₁
  exact ⟨B', h', h5 F μ ψ hψ n V ρ hρ l B₁ B' hn h₁ hC⟩

end GlobalTheory.CompanionTheory.SatakeBound

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalZeroOfInjectivePower
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

namespace GlobalTheory.CompanionTheory.SatPow

theorem functional_eq_zero_of_late_iterates :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (A : V →ₗ[ℂ] V), Function.Injective A → ∀ (l : V →ₗ[ℂ] ℂ) (v : V) (j₀ : ℕ), (∀ j ≥ j₀, l ((A ^ j) v) = 0) → l v = 0 := by
  intro V _ _ _ A hA l v j₀ h
  let U : Submodule ℂ V := Submodule.span ℂ (Set.range fun i : ℕ => (A ^ (i + j₀)) v)
  have hUl : U ≤ LinearMap.ker l := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (h (i + j₀) (Nat.le_add_left j₀ i))
  have hle : U ≤ U.comap A := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have e : A ((A ^ (i + j₀)) v) = (A ^ ((i + 1) + j₀)) v := by
      rw [show i + 1 + j₀ = (i + j₀) + 1 by omega, pow_succ', Module.End.mul_apply]
    show A ((A ^ (i + j₀)) v) ∈ U
    rw [e]
    exact Submodule.subset_span ⟨i + 1, rfl⟩
  have hAU : ∀ u ∈ U, A u ∈ U := fun u hu => hle hu
  let B : U →ₗ[ℂ] U := A.restrict hAU
  have hBi : Function.Injective B := by
    intro x y hxy
    apply Subtype.ext
    apply hA
    have := congrArg Subtype.val hxy
    simpa [B, LinearMap.restrict_apply] using this
  have hBs : Function.Surjective B := LinearMap.injective_iff_surjective.mp hBi
  have pull : ∀ x : V, A x ∈ U → x ∈ U := by
    intro x hx
    obtain ⟨u, hu⟩ := hBs ⟨A x, hx⟩
    have hux : A u = A x := congrArg Subtype.val hu
    rw [← hA hux]
    exact u.2
  have key : ∀ k : ℕ, (A ^ (j₀ - k)) v ∈ U := by
    intro k
    induction k with
    | zero =>
      have e0 : (A ^ (j₀ - 0)) v = (A ^ (0 + j₀)) v := by rw [Nat.sub_zero, Nat.zero_add]
      rw [e0]
      exact Submodule.subset_span ⟨0, rfl⟩
    | succ k ih =>
      rcases Nat.eq_zero_or_pos (j₀ - k) with h0 | hpos
      · have e1 : j₀ - (k + 1) = j₀ - k := by omega
        rw [e1]
        exact ih
      · have e : j₀ - k = (j₀ - (k + 1)) + 1 := by omega
        have e2 : (A ^ (j₀ - k)) v = A ((A ^ (j₀ - (k + 1))) v) := by
          rw [e, pow_succ', Module.End.mul_apply]
        rw [e2] at ih
        exact pull _ ih
  have hv : v ∈ U := by
    have h1 := key j₀
    rwa [Nat.sub_self, pow_zero, Module.End.one_apply] at h1
  exact LinearMap.mem_ker.mp (hUl hv)

end GlobalTheory.CompanionTheory.SatPow
end

