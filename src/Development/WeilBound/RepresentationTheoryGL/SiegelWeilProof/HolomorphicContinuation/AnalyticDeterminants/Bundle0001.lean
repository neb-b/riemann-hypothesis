module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HasFDerivAtInt
section
noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolA

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]

theorem integrable_of_cont {W : Type*} [NormedAddCommGroup W] {f : Kg → W} (hf : Continuous f) :
    Integrable f μ := by
  have hm : AEStronglyMeasurable f μ := by
    simpa using (hf.continuousOn (s := univ)).aestronglyMeasurable_of_isCompact isCompact_univ
      MeasurableSet.univ (μ := μ)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hf.continuousOn (s := univ))
  exact Integrable.of_bound hm C (Eventually.of_forall fun k => hC k (mem_univ k))

theorem hasFDerivAt_int {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    {Ω : Set E} (hΩ : IsOpen Ω) {Φ : Kg → E → W} {Φ' : Kg → E → (E →L[ℂ] W)}
    (hc : ContinuousOn (fun y : Kg × E => Φ y.1 y.2) (univ ×ˢ Ω))
    (hc' : ContinuousOn (fun y : Kg × E => Φ' y.1 y.2) (univ ×ˢ Ω))
    (hd : ∀ k, ∀ x ∈ Ω, HasFDerivAt (Φ k) (Φ' k x) x) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    HasFDerivAt (fun x => ∫ k, Φ k x ∂μ) (∫ k, Φ' k x₀ ∂μ) x₀ := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  have hsub : closedBall x₀ (r / 2) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hrΩ
  have hK : IsCompact ((univ : Set Kg) ×ˢ closedBall x₀ (r / 2)) := isCompact_univ.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc'.mono (prod_mono subset_rfl hsub))
  have cont_k : ∀ x ∈ Ω, Continuous fun k => Φ k x := fun x hx =>
    continuousOn_univ.mp (hc.comp (f := fun k : Kg => (k, x)) (Continuous.continuousOn (by fun_prop))
      fun k _ => ⟨mem_univ _, hx⟩)
  have cont_k' : ∀ x ∈ Ω, Continuous fun k => Φ' k x := fun x hx =>
    continuousOn_univ.mp (hc'.comp (f := fun k : Kg => (k, x)) (Continuous.continuousOn (by fun_prop))
      fun k _ => ⟨mem_univ _, hx⟩)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (F := fun x k => Φ k x)
    (F' := fun x k => Φ' k x) (bound := fun _ => C) (ball_mem_nhds x₀ (half_pos hr)) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hΩ.mem_nhds hx₀] with x hx
    exact (integrable_of_cont (cont_k x hx)).aestronglyMeasurable
  · exact integrable_of_cont (cont_k x₀ hx₀)
  · exact (integrable_of_cont (cont_k' x₀ hx₀)).aestronglyMeasurable
  · exact Eventually.of_forall fun k x hx => hC (k, x) ⟨mem_univ _, ball_subset_closedBall hx⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun k x hx => hd k x (hsub (ball_subset_closedBall hx))

end PositivityTheory.Rg.Sw.LVs.HolA
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompB
section
noncomputable section

open Polynomial

namespace PositivityTheory.Rg.Sw.LVs.TC

theorem ml_expand {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => V) ℂ) (Y : Fin k → Fin 3 → V) (z : ℂ) :
    A (fun i => Y i 0 + z • Y i 1 + z ^ 2 • Y i 2) =
      ∑ f : Fin k → Fin 3, z ^ (∑ i, (f i : ℕ)) * A (fun i => Y i (f i)) := by
  have h : (fun i => Y i 0 + z • Y i 1 + z ^ 2 • Y i 2) = fun i => ∑ w : Fin 3, z ^ (w : ℕ) • Y i w := by
    funext i; simp [Fin.sum_univ_three]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr (by simp) fun f _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum, smul_eq_mul]

theorem sum_eq_top {k : ℕ} (f : Fin k → Fin 3) (h : ∑ i, (f i : ℕ) = 2 * k) : ∀ i, f i = 2 := by
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  have hle : ∀ x, (f x : ℕ) ≤ 2 := fun x => by omega
  have hlt : (f i : ℕ) < 2 := by
    rcases Nat.lt_or_ge (f i : ℕ) 2 with h' | h'
    · exact h'
    · exact absurd (Fin.ext (by simp; omega)) hi
  have : ∑ x, (f x : ℕ) < ∑ _x : Fin k, 2 :=
    Finset.sum_lt_sum (fun x _ => hle x) ⟨i, Finset.mem_univ _, hlt⟩
  simp at this
  omega

theorem infinite_circle : Set.Infinite (Set.range fun θ : ℝ => Complex.exp (2 * θ * Complex.I)) := by
  have hinj : Function.Injective fun m : ℕ => Complex.exp (2 * ((1 : ℝ) / (m + 2) : ℝ) * Complex.I) := by
    intro a b hab
    have hre := congrArg Complex.re hab
    simp only at hre
    have e1 : ∀ x : ℝ, (Complex.exp (2 * (x : ℂ) * Complex.I)).re = Real.cos (2 * x) := by
      intro x
      rw [show 2 * (x : ℂ) * Complex.I = ((2 * x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_re]
    rw [e1, e1] at hre
    have ha : 2 * ((1 : ℝ) / (a + 2)) ∈ Set.Icc 0 Real.pi := by
      constructor
      · positivity
      · have : (2 : ℝ) * (1 / (a + 2)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
        linarith [Real.pi_gt_three]
    have hb : 2 * ((1 : ℝ) / (b + 2)) ∈ Set.Icc 0 Real.pi := by
      constructor
      · positivity
      · have : (2 : ℝ) * (1 / (b + 2)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
        linarith [Real.pi_gt_three]
    have := Real.injOn_cos ha hb hre
    have h2 : (1 : ℝ) / (a + 2) = 1 / (b + 2) := by linarith
    rw [div_eq_div_iff (by positivity) (by positivity)] at h2
    exact_mod_cast (by linarith : (a : ℝ) = b)
  refine Set.infinite_of_injective_forall_mem hinj fun m => ⟨_, rfl⟩

theorem top_vanish {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ} {ι : Type*} [Fintype ι]
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => V) ℂ) (sg : ι → ℂ) (Y : ι → Fin k → Fin 3 → V)
    (h : ∀ θ : ℝ, ∑ σ, sg σ * A (fun i => Y σ i 0 + Complex.exp (2 * θ * Complex.I) • Y σ i 1 +
      Complex.exp (2 * θ * Complex.I) ^ 2 • Y σ i 2) = 0) :
    ∑ σ, sg σ * A (fun i => Y σ i 2) = 0 := by
  set Q : ℂ[X] := ∑ σ, C (sg σ) * ∑ f : Fin k → Fin 3, C (A (fun i => Y σ i (f i))) * X ^ (∑ i, (f i : ℕ)) with hQ
  have heval : ∀ z : ℂ, Q.eval z = ∑ σ, sg σ * A (fun i => Y σ i 0 + z • Y σ i 1 + z ^ 2 • Y σ i 2) := by
    intro z
    simp only [hQ, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ml_expand]
    congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  have hQ0 : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ infinite_circle
    rintro _ ⟨θ, rfl⟩
    simp only [Set.mem_ofPred_eq, IsRoot.def, heval, h θ]
  have hc := congrArg (fun p : ℂ[X] => p.coeff (2 * k)) hQ0
  simp only [hQ, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
  rw [← hc]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [Finset.sum_eq_single (fun _ => 2)]
  · simp only [Fin.isValue, Fin.val_two, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [if_pos (by ring), mul_one]
  · intro f _ hf
    rw [if_neg, mul_zero]
    intro h2
    exact hf (funext (sum_eq_top f h2.symm))
  · simp

end PositivityTheory.Rg.Sw.LVs.TC
end
end

