module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LojasiewiczInequalityAnalytic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FormPolyIsHomogeneousAndEval
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem formPoly_isHomogeneous_and_eval (σ : Type) [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) :
    (formPoly n a).IsHomogeneous n ∧
      ∀ c : σ → ℝ, eval c (formPoly n a) = ∑ w : Fin n → σ, a w * ∏ j, c (w j) := by
  classical
  refine ⟨?_, fun c => ?_⟩
  · unfold formPoly
    refine IsHomogeneous.sum _ _ _ fun w _ => ?_
    have h : (∏ j : Fin n, (X (w j) : MvPolynomial σ ℝ)).IsHomogeneous (∑ _j : Fin n, 1) :=
      IsHomogeneous.prod _ _ _ fun j _ => isHomogeneous_X _ _
    have h' : (∏ j : Fin n, (X (w j) : MvPolynomial σ ℝ)).IsHomogeneous n := by simpa using h
    exact h'.C_mul _
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [formPoly, map_sum, map_prod]

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HarmonicAnnulusMaximumPrinciple
section
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem harmonic_eventually_eq_of_ball_le {h : ℂ → ℝ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : InnerProductSpace.HarmonicOnNhd h (Metric.ball z₀ r))
    (hle : ∀ z ∈ Metric.ball z₀ r, h z ≤ h z₀) : ∀ᶠ z in 𝓝 z₀, h z = h z₀ := by
  obtain ⟨F, hF, hre⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hh
  have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hball : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr
  have hnorm : ∀ z ∈ Metric.ball z₀ r, ‖Complex.exp (F z)‖ = Real.exp (h z) := fun z hz => by
    rw [Complex.norm_exp]
    exact congrArg Real.exp (hre hz)
  have hdiff : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ (fun z => Complex.exp (F z)) z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz₀] with z hz
    exact (hF z hz).differentiableAt.cexp
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (F z)) z₀ := by
    filter_upwards [hball] with z hz
    simp only [Function.comp_apply]
    rw [hnorm z hz, hnorm z₀ hz₀]
    exact Real.exp_le_exp.2 (hle z hz)
  filter_upwards [Complex.eventually_eq_of_isLocalMax_norm hdiff hmax, hball] with z hz hzb
  have h1 := congrArg norm hz
  rw [hnorm z hzb, hnorm z₀ hz₀] at h1
  exact Real.exp_injective h1

theorem harmonic_annulus_le_zero : ∀ (h : ℂ → ℝ) (a b : ℝ), 0 < a → a < b →
    ContinuousOn h {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} →
    (∀ z : ℂ, a < ‖z‖ → ‖z‖ < b → InnerProductSpace.HarmonicAt h z) →
    (∀ z : ℂ, (‖z‖ = a ∨ ‖z‖ = b) → h z ≤ 0) →
    ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → h z ≤ 0 := by
  intro h a b ha hab hc hh hb z hz1 hz2
  by_contra hpos
  push Not at hpos
  set K : Set ℂ := {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} with hK
  have hKclosed : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hKcomp : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) b).of_isClosed_subset hKclosed
      (fun w hw => by simpa using hw.2)
  have hzK : z ∈ K := ⟨hz1, hz2⟩
  obtain ⟨z₁, hz₁K, hz₁⟩ := hKcomp.exists_isMaxOn ⟨z, hzK⟩ hc
  set S : Set ℂ := K ∩ h ⁻¹' {h z₁} with hS
  have hSclosed : IsClosed S :=
    hc.preimage_isClosed_of_isClosed hKclosed isClosed_singleton
  have hScomp : IsCompact S := hKcomp.of_isClosed_subset hSclosed Set.inter_subset_left
  obtain ⟨z₀, hz₀S, hz₀⟩ :=
    hScomp.exists_isMaxOn ⟨z₁, hz₁K, rfl⟩ (continuous_norm.continuousOn (s := S))
  have hz₀K : z₀ ∈ K := hz₀S.1
  have hval : h z₀ = h z₁ := hz₀S.2
  have hMpos : 0 < h z₀ := hval ▸ hpos.trans_le (hz₁ hzK)
  have hlo : a < ‖z₀‖ := lt_of_le_of_ne hz₀K.1 fun e => absurd (hb z₀ (Or.inl e.symm)) (not_le.2 hMpos)
  have hhi : ‖z₀‖ < b := lt_of_le_of_ne hz₀K.2 fun e => absurd (hb z₀ (Or.inr e)) (not_le.2 hMpos)
  have hUopen : IsOpen {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUopen z₀ ⟨hlo, hhi⟩
  have hloc : ∀ᶠ w in 𝓝 z₀, h w = h z₀ := by
    refine harmonic_eventually_eq_of_ball_le hr (fun w hw => hh w (hrU hw).1 (hrU hw).2) ?_
    intro w hw
    rw [hval]
    exact hz₁ ⟨(hrU hw).1.le, (hrU hw).2.le⟩
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1
    (hloc.and (hUopen.mem_nhds ⟨hlo, hhi⟩))
  have hz₀pos : 0 < ‖z₀‖ := ha.trans hlo

  set t : ℝ := ε / (2 * ‖z₀‖) with ht
  have htpos : 0 < t := by positivity
  set w : ℂ := ((1 + t : ℝ) : ℂ) * z₀ with hw
  have hwnorm : ‖w‖ = (1 + t) * ‖z₀‖ := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hdist : dist w z₀ < ε := by
    have e : w - z₀ = (t : ℂ) * z₀ := by
      rw [hw]; push_cast; ring
    rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg htpos.le, ht]
    have : ε / (2 * ‖z₀‖) * ‖z₀‖ = ε / 2 := by field_simp
    rw [this]
    linarith
  obtain ⟨hwval, hwU⟩ := hεb w hdist
  have hwS : w ∈ S := ⟨⟨hwU.1.le, hwU.2.le⟩, by simpa [hval] using hwval⟩
  have hle : ‖w‖ ≤ ‖z₀‖ := hz₀ hwS
  rw [hwnorm] at hle
  nlinarith [mul_pos htpos hz₀pos]

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial

theorem killNone_formPoly {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → Option σ) → ℝ) :
    aeval (fun o : Option σ => o.elim (0 : MvPolynomial σ ℝ) X) (formPoly n a)
      = formPoly n fun w => a fun j => some (w j) := by
  classical
  unfold formPoly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  symm
  refine Finset.sum_of_injOn (fun (w : Fin n → σ) j => some (w j)) ?_ ?_ ?_ ?_
  · intro w _ w' _ h
    funext j
    exact Option.some_injective _ (congrFun h j)
  · intro w _
    exact Finset.mem_univ _
  · intro w _ hw
    have : ∃ j, w j = none := by
      by_contra hc
      apply hw
      have hc' : ∀ j, (w j).isSome := fun j => by
        cases h : w j with
        | none => exact absurd ⟨j, h⟩ hc
        | some _ => rfl
      exact ⟨fun j => (w j).get (hc' j), Finset.mem_coe.2 (Finset.mem_univ _), by funext j; simp⟩
    obtain ⟨j, hj⟩ := this
    rw [map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]
  · intro w _
    simp [map_prod]

theorem killNone_toWtS {Ψ : Type} {N : ℕ} (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) :
    aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X) (toWtS Q)
      = toWt (aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X) Q) := by
  have h : (aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X)).comp toWtS
      = toWt.comp (aeval (fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X)) := by
    apply MvPolynomial.algHom_ext
    intro o
    cases o with
    | none => simp [toWtS, toWt]
    | some p =>
      simp only [toWtS, toWt, AlgHom.comp_apply, aeval_X, Option.elim_some, aeval_rename]
      have : ((fun o : Option (Ψ × Fin N) => o.elim (0 : MvPolynomial (Ψ × Fin N) ℝ) X) ∘ some) = X := rfl
      rw [this, aeval_X_left_apply]
  exact DFunLike.congr_fun h Q

theorem eval_toWt_gap {Ψ : Type} {N : ℕ} (Q : MvPolynomial (Ψ × Fin N) ℝ) (lam : Ψ × Fin N → ℝ) :
    eval lam (toWt Q) = eval (gap lam) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [toWt]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp]; simp [toWt, gap]

theorem eval_toWtS_gapS {Ψ : Type} {N : ℕ} (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (lam : Ψ × Fin N → ℝ)
    (s : ℝ) : eval (fun o => o.elim s lam) (toWtS Q) = eval (gapS lam s) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [toWtS]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    cases i with
    | none => simp [toWtS, gapS]
    | some q =>
      simp only [toWtS, gapS, gap, aeval_X, eval_X, Option.elim_some, eval_rename]
      rfl

theorem poly_s_zero : ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ),
    (∀ (a : (Fin n → Option (Ψ × Fin N)) → ℝ),
      aeval (fun o : Option (Ψ × Fin N) => o.elim 0 X) (toWtS (formPoly n a))
        = toWt (formPoly n fun w => a fun j => some (w j))) ∧
    (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (lam : Ψ × Fin N → ℝ), eval lam (toWt Q) = eval (gap lam) Q) ∧
    ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (lam : Ψ × Fin N → ℝ) (s : ℝ),
      eval (fun o => o.elim s lam) (toWtS Q) = eval (gapS lam s) Q := by
  intro Ψ _ N n
  refine ⟨fun a => ?_, eval_toWt_gap, eval_toWtS_gapS⟩
  rw [killNone_toWtS, killNone_formPoly]

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LimRateMulLogSqLe
section
namespace GlobalTheory.CompanionTheory.Ar.PB

theorem limRate_log_inv_exp (s : ℝ) : Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) = (s ^ 2)⁻¹ := by
  rw [one_div, Real.log_inv, Real.log_exp, neg_neg]

theorem limRate_sq_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  nlinarith [mul_nonneg hx (sq_nonneg (x - 3 / 2))]

theorem limRate_mul_log_sq_le {s : ℝ} (hs : 0 < s) (h1 : s ≤ 1) : s * Real.log s ^ 2 ≤ 1 := by
  have h := limRate_sq_le_exp (x := -Real.log s) (by linarith [Real.log_nonpos hs.le h1])
  rw [Real.exp_neg, Real.exp_log hs, neg_sq] at h
  calc s * Real.log s ^ 2 ≤ s * s⁻¹ := mul_le_mul_of_nonneg_left h hs.le
    _ = 1 := mul_inv_cancel₀ hs.ne'

theorem limRate : Filter.Tendsto (fun t : ℝ => Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧ (∀ s : ℝ, 0 < s → s ≤ 1 → Real.log (Real.log (1 / Real.exp (-(s ^ 2)⁻¹))) ^ 2 / Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) ≤ 4 * s) ∧ (∀ s : ℝ, 0 < s → s ≤ 1 → Real.exp (-(s ^ 2)⁻¹) ^ ((1 : ℝ) / 3) ≤ 2 * s) ∧ ∀ C ε : ℝ, 0 < ε → ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → C * Real.log (Real.log (1 / Real.exp (-(s ^ 2)⁻¹))) / Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) ≤ ε * s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hl : Filter.Tendsto (fun t : ℝ => Real.log (1 / t)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
      simp only [one_div]
      exact Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hl
    refine h.congr fun t => ?_
    simp
  · intro s hs h1
    rw [limRate_log_inv_exp, Real.log_inv, Real.log_pow, div_inv_eq_mul]
    have h3 := limRate_mul_log_sq_le hs h1
    push_cast
    have e : (-(2 * Real.log s)) ^ 2 * s ^ 2 = 4 * s * (s * Real.log s ^ 2) := by ring
    rw [e]
    nlinarith
  · intro s hs h1
    rw [← Real.exp_mul]
    set y := (s ^ 2)⁻¹ with hy
    have hys : y * s ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
    have hy0 : 0 ≤ y := by positivity
    have ha := Real.add_one_le_exp (y * (1 / 3))
    have hE : 0 < Real.exp (y * (1 / 3)) := Real.exp_pos _
    rw [show -y * (1 / 3) = -(y * (1 / 3)) by ring, Real.exp_neg]
    have hkey : 1 ≤ 2 * s * (1 + y * (1 / 3)) := by
      nlinarith [sq_nonneg (s - 1 / 4), mul_pos hs hs]
    calc (Real.exp (y * (1 / 3)))⁻¹ ≤ (1 + y * (1 / 3))⁻¹ :=
          inv_anti₀ (by positivity) (by linarith)
      _ ≤ 2 * s := by
          rw [inv_le_iff_one_le_mul₀ (by positivity)]
          linarith
  · intro C ε hε
    set K := 2 * |C| + 1 with hK
    have hKpos : 0 < K := by positivity
    refine ⟨min 1 ((ε / K) ^ 2), by positivity, ?_⟩
    intro s hs hs0
    have h1 : s ≤ 1 := le_trans hs0 (min_le_left _ _)
    have h2 : s ≤ (ε / K) ^ 2 := le_trans hs0 (min_le_right _ _)
    rw [limRate_log_inv_exp, Real.log_inv, Real.log_pow, div_inv_eq_mul]
    push_cast
    have h3 := limRate_mul_log_sq_le hs h1
    have hsq : (s * Real.log s) ^ 2 ≤ (ε / K) ^ 2 := by
      calc (s * Real.log s) ^ 2 = s * (s * Real.log s ^ 2) := by ring
        _ ≤ s * 1 := mul_le_mul_of_nonneg_left h3 hs.le
        _ ≤ (ε / K) ^ 2 := by linarith
    have habs : |s * Real.log s| ≤ ε / K := abs_le.mpr (abs_le_of_sq_le_sq' hsq (by positivity))
    have hb : -2 * C * (s * Real.log s) ≤ ε := by
      calc -2 * C * (s * Real.log s) ≤ |-2 * C * (s * Real.log s)| := le_abs_self _
        _ = 2 * |C| * |s * Real.log s| := by
            rw [abs_mul, abs_mul, abs_neg, abs_two]
        _ ≤ 2 * |C| * (ε / K) := mul_le_mul_of_nonneg_left habs (by positivity)
        _ ≤ ε := by
            rw [mul_div_assoc', div_le_iff₀ hKpos, hK]
            nlinarith [abs_nonneg C]
    calc C * -(2 * Real.log s) * s ^ 2 = s * (-2 * C * (s * Real.log s)) := by ring
      _ ≤ s * ε := mul_le_mul_of_nonneg_left hb hs.le
      _ = ε * s := mul_comm _ _

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LmuNumNonneg
section
namespace GlobalTheory.CompanionTheory.Ar.Crv.Chain

open GlobalTheory.CompanionTheory.Ar.Crv

theorem abel_bound (ν v : ℕ → ℝ) (P : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hν : ∀ i, 1 ≤ i → i < n → ν (i + 1) ≤ ν i) (hv : ∀ i, i ≤ n → v i ≤ P) :
    ∑ i ∈ Finset.range n, ν (i + 1) * (v (i + 1) - v i) ≤
      ν n * v n - ν 1 * v 0 + P * (ν 1 - ν n) := by
  induction n, hn using Nat.le_induction with
  | base => simp; linarith
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih (fun i h h' => hν i h (by omega)) (fun i h => hv i (by omega))
    have h2 := hν n hn (by omega)
    have h3 := hv n (by omega)
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3)]

theorem lmuNum_nonneg : ∀ (T : Type) [Fintype T] (p j q : ℕ) (μ w l : T → ℕ → ℝ) (P e : ℝ), 2 < p → 1 ≤ j → 1 ≤ q → GapCond p j q μ → (∀ τ, w τ 0 = 0) → (∀ τ, l τ 0 = 0) → (∀ τ i, i ≤ j → w τ i ≤ P) → (∀ τ i, i ≤ q → l τ i ≤ P) → (∀ τ, w τ j = l τ q) → e = -2 * ∑ τ, w τ j → ((p : ℝ) - 2) * P ≤ e → 0 ≤ e → 0 ≤ lmuNum j q μ w l := by
  intro T _ p j q μ w l P e hp hj hq hgap hw0 hl0 hw hl hwl he hPe he0
  obtain ⟨hdom, M, g, hM, hg, hpg⟩ := hgap
  rcases isEmpty_or_nonempty T with hT | ⟨⟨τ₀⟩⟩
  · simp [lmuNum]
  have hp' : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  have hP : 0 ≤ P := by have := hw τ₀ 0 (by omega); rwa [hw0] at this
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM τ₀ 1 le_rfl (by omega))
  have hf : (0 : ℝ) ≤ (Fintype.card T : ℝ) := Nat.cast_nonneg _
  have hfM : 0 ≤ (Fintype.card T : ℝ) * M := mul_nonneg hf hM0
  have hg0 : 0 ≤ g := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hp' (neg_pos.2 h)]
  have key : ∀ τ, (∑ i ∈ Finset.range j, μ τ (i + 1) * (w τ (i + 1) - w τ i)) +
      ∑ m ∈ Finset.range q, μ τ (j + m + 1) * (l τ (q - m - 1) - l τ (q - m)) ≤
      g * w τ j + 2 * M * P := by
    intro τ
    have hA := abel_bound (μ τ) (w τ) P j hj (fun i h h' => hdom τ i h (by omega)) (hw τ)
    have hB := abel_bound (fun i => μ τ (j + i)) (fun m => l τ (q - m)) P q hq
      (fun i h h' => hdom τ (j + i) (by omega) (by omega)) (fun i _ => hl τ _ (by omega))
    simp only [Nat.sub_self, Nat.sub_zero, hl0, ← hwl τ] at hB
    rw [hw0] at hA
    have e1 : ∑ m ∈ Finset.range q, μ τ (j + m + 1) * (l τ (q - m - 1) - l τ (q - m)) =
        ∑ m ∈ Finset.range q, μ τ (j + (m + 1)) * (l τ (q - (m + 1)) - l τ (q - m)) := rfl
    rw [e1]
    have h1 := abs_le.1 (hM τ 1 le_rfl (by omega))
    have h2 := abs_le.1 (hM τ (j + q) (by omega) le_rfl)
    have h3 := mul_nonneg (sub_nonneg.2 (hg τ)) (sub_nonneg.2 (hw τ j le_rfl))
    have h4 : 0 ≤ P * (2 * M - (μ τ 1 - μ τ (j + q))) := mul_nonneg hP (by linarith [h1.2, h2.1])
    have h5 := mul_nonneg hg0 hP
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun τ _ => key τ)
  rw [Finset.sum_add_distrib (f := fun τ => g * w τ j), ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hS : ∑ τ, w τ j = -e / 2 := by linarith
  rw [hS] at hsum
  have hfin : g * (-e / 2) + (Fintype.card T : ℝ) * (2 * M * P) ≤ 0 := by
    have a1 := mul_le_mul_of_nonneg_left hPe hfM
    have a2 := mul_le_mul_of_nonneg_right hpg he0
    by_contra h
    push Not at h
    nlinarith [mul_pos hp' h]
  unfold lmuNum
  linarith

end GlobalTheory.CompanionTheory.Ar.Crv.Chain
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalLogarithmHomomorphism
section
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

theorem koenigs_limit_additive_for_law : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (μ : B × V × V → V) (L : B × V → V) (ρ C : ℝ), 0 < ρ → 0 ≤ C → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, Tendsto (fun k : ℕ => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k (b, s)) atTop (𝓝 (L (b, s)))) → ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, μ (b, s, t) ∈ ball (0 : V) ρ → L (b, μ (b, s, t)) = L (b, s) + L (b, t) := by
  intro B V _ _ _ _ b₀ h μ L ρ C _hρ hC hcontr happrox hhom hlim b hb s hs t ht hm
  have hsk := fun k => iter_mem_ball b₀ h ρ hcontr hb hs k
  have htk := fun k => iter_mem_ball b₀ h ρ hcontr hb ht k
  have hiter : ∀ k : ℕ, iter h k (b, μ (b, s, t)) = μ (b, iter h k (b, s), iter h k (b, t)) := by
    intro k
    induction k with
    | zero => rw [iter_zero, iter_zero, iter_zero]
    | succ k ih =>
      rw [iter_succ, iter_succ, iter_succ, ih]
      exact hhom b hb _ (hsk k) _ (htk k)
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  have herr : Tendsto (fun k : ℕ => (2 : ℂ) ^ k •
      (μ (b, iter h k (b, s), iter h k (b, t)) - iter h k (b, s) - iter h k (b, t))) atTop (𝓝 0) := by
    have hg : Tendsto (fun k : ℕ => C * ‖s‖ * ‖t‖ * (18 / 25 : ℝ) ^ k) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 18 / 25)
        (by norm_num : (18 / 25 : ℝ) < 1)
      simpa using this.const_mul (C * ‖s‖ * ‖t‖)
    refine squeeze_zero_norm (fun k => ?_) hg
    rw [norm_smul, norm_pow, hn2]
    have h1 := happrox b hb _ (hsk k) _ (htk k)
    have h2 := norm_iter_le b₀ h ρ hcontr hb hs k
    have h3 := norm_iter_le b₀ h ρ hcontr hb ht k
    calc (2 : ℝ) ^ k * ‖μ (b, iter h k (b, s), iter h k (b, t)) - iter h k (b, s) - iter h k (b, t)‖
        ≤ 2 ^ k * (C * ‖iter h k (b, s)‖ * ‖iter h k (b, t)‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 ^ k * (C * ((3 / 5) ^ k * ‖s‖) * ((3 / 5) ^ k * ‖t‖)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h3 (norm_nonneg _)
            (mul_nonneg hC (by positivity))
      _ = C * ‖s‖ * ‖t‖ * (18 / 25) ^ k := by
          rw [show (18 / 25 : ℝ) = 2 * (3 / 5) * (3 / 5) by norm_num, mul_pow, mul_pow]
          ring
  have hsum : Tendsto (fun k : ℕ => (2 : ℂ) ^ k • iter h k (b, μ (b, s, t))) atTop
      (𝓝 (L (b, s) + L (b, t) + 0)) := by
    refine (((hlim b hb s hs).add (hlim b hb t ht)).add herr).congr (fun k => ?_)
    rw [hiter k, smul_sub, smul_sub]
    abel
  rw [add_zero] at hsum
  exact tendsto_nhds_unique (hlim b hb _ hm) hsum

end GlobalTheory.CompanionTheory.Ar.Flat.LocalLog
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LojasiewiczInequalityAnalyticStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lojasiewicz_inequality_analytic : ∀ (e : ℕ) (f g : (Fin e → ℂ) → ℂ) (x : Fin e → ℂ), AnalyticAt ℂ f x → AnalyticAt ℂ g x → (∀ᶠ y in nhds x, g y = 0 → f y = 0) → ∃ (N : ℕ) (C : ℝ), 0 < N ∧ ∀ᶠ y in nhds x, ‖f y‖ ^ N ≤ C * ‖g y‖ := by
  first | exact @GlobalTheory.CompanionTheory.Loj.lojasiewicz | exact GlobalTheory.CompanionTheory.Loj.lojasiewicz | (intros; apply GlobalTheory.CompanionTheory.Loj.lojasiewicz <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProdIicBlockDiagDetFactorsStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_Iic_blockDiag_det_factors : ∀ (Φ : Type) [CommMonoid Φ] (p q : ℕ) (tW : Fin p → Φ) (tO : Fin q → Φ) (G : Fin (p + q) → Φ), (∀ (i : Fin (p + q)) (h : (i : ℕ) < p), G i = tW ⟨i, h⟩) → (∀ (i : Fin (p + q)) (h : p ≤ (i : ℕ)), G i = tO ⟨(i : ℕ) - p, by have := i.2; omega⟩) → ∀ i : Fin (p + q), (∀ h : (i : ℕ) < p, ∏ k ∈ Finset.Iic i, G k = ∏ l : Fin ((i : ℕ) + 1), tW (Fin.castLE h l)) ∧ (∀ h : p ≤ (i : ℕ), ∏ k ∈ Finset.Iic i, G k = (∏ l, tW l) * ∏ l : Fin ((i : ℕ) - p + 1), tO (Fin.castLE (by have := i.2; omega) l)) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.GradedLines.prod_first_graded_lines | exact GlobalTheory.CompanionTheory.Metric.GradedLines.prod_first_graded_lines | (intros; apply GlobalTheory.CompanionTheory.Metric.GradedLines.prod_first_graded_lines <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RatioSuccessiveNonzeroRegularStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratio_successive_nonzero_regular : ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (N : ℕ) (G E : Fin N → Φ), (∀ i, E i ≠ 0) → (∀ i, (∏ k ∈ Finset.Iic i, G k) / E i ≠ 0 ∧ (∏ k ∈ Finset.Iic i, G k) / E i ∈ R ∧ ((∏ k ∈ Finset.Iic i, G k) / E i)⁻¹ ∈ R) → ∀ i : Fin N, G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩) ≠ 0 ∧ G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩) ∈ R ∧ (G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩))⁻¹ ∈ R := by
  first | exact @GlobalTheory.CompanionTheory.Metric.UnitQuotients.consecutive_quotients_units | exact GlobalTheory.CompanionTheory.Metric.UnitQuotients.consecutive_quotients_units | (intros; apply GlobalTheory.CompanionTheory.Metric.UnitQuotients.consecutive_quotients_units <;> assumption)
end

