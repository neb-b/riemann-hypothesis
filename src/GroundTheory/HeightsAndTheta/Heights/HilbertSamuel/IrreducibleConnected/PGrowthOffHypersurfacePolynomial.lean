module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem exists_eval_ne_zero_of_isOpen {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0)
    {V : Set (Fin d → ℂ)} (hV : IsOpen V) (hne : V.Nonempty) : ∃ t ∈ V, eval t Q ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  obtain ⟨t, ht⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV t ht
  apply hQ
  refine MvPolynomial.funext_set (fun i => Metric.ball (t i) ε) (fun i => ?_) (fun x hx => ?_)
  · exact infinite_of_mem_nhds (t i) (Metric.ball_mem_nhds (t i) hε)
  · rw [map_zero]
    apply hall
    apply hball
    rw [ball_pi t hε]
    exact hx

theorem dense_eval_ne_zero {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0) :
    Dense {y : Fin d → ℂ | eval y Q ≠ 0} := by
  rw [dense_iff_inter_open]
  intro V hV hne
  obtain ⟨t, htV, ht⟩ := exists_eval_ne_zero_of_isOpen hQ hV hne
  exact ⟨t, htV, ht⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
