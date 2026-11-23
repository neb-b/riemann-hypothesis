module

public import Mathlib
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0043
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0044
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0036

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlochKatoDuality
section
open MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 in
theorem UpperTheory.Reformulated.B.BlochKatoDuality.haarInvFromUnique :
    Formalism.FourierDecayAlt.B2.HaarInvFromUnique := by
  intro huniq k r U μ hU hμ
  have hm : Measurable (invM : Mt k r → Mt k r) := UpperTheory.measurable_matrix_inv _
  have hUc : IsClosed (X := Mt k r) U := hU.closed
  have hmem : ∀ x : Mt k r, x ∈ U → invM x ∈ U := fun x hx => hU.inv_mem x hx
  have hinv : ∀ x : Mt k r, x ∈ U → invM (invM x) = x := fun x hx =>
    Matrix.nonsing_inv_nonsing_inv (Matrix.of x) (hU.unit x hx)
  have hae : ∀ᵐ x ∂μ, (x : Mt k r) ∈ U := hμ.conc
  have hcont : ContinuousOn (invM : Mt k r → Mt k r) U := by
    intro x hx
    obtain ⟨u, hu⟩ := hU.unit x hx
    have h1 : ContinuousAt Ring.inverse (Matrix.of x : Mat k r).det := by
      have h2 := NormedRing.inverse_continuousAt u
      rw [hu] at h2
      exact h2
    exact (continuousAt_matrix_inv (Matrix.of x : Mat k r) h1).continuousWithinAt
  have hfin := UpperTheory.involution_map_compact_finite (Mt k r) μ U invM hm hUc hcont hmem hinv hμ.conc hμ.finite_compact
  have hconc : (μ.map invM) (Uᶜ : Set (Mat k r)) = 0 := by
    have h : ∀ᵐ x ∂(μ.map invM), (x : Mt k r) ∈ U :=
      (ae_map_iff hm.aemeasurable hUc.measurableSet).2 (hae.mono hmem)
    exact h
  have hleft : ∀ a ∈ U, (μ.map invM).map (lmulM a) = μ.map invM := by
    intro a ha
    have hl : Measurable (lmulM a : Mt k r → Mt k r) :=
      Continuous.measurable (α := Mt k r) (γ := Mt k r)
        (Continuous.matrix_mul (continuous_const (y := a)) (continuous_id (X := Mat k r)))
    have hr : Measurable (rmulF a⁻¹ : Mt k r → Mt k r) :=
      Continuous.measurable (α := Mt k r) (γ := Mt k r)
        (Continuous.matrix_mul (continuous_id (X := Mat k r)) (continuous_const (y := a⁻¹)))
    have he : (lmulM a ∘ invM : Mt k r → Mt k r) = invM ∘ rmulF a⁻¹ := by
      funext x
      change a * (Matrix.of x : Mat k r)⁻¹ = (Matrix.of x * a⁻¹ : Mat k r)⁻¹
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv a (hU.unit a ha)]
    rw [Measure.map_map hl hm, he, ← Measure.map_map hm hr, hμ.right _ (hU.inv_mem a ha)]
  obtain ⟨c, hc⟩ := huniq k r U μ (μ.map invM) hU hμ hconc hleft hfin
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hμ.finite_compact K hK⟩
  exact UpperTheory.map_involution_eq_self (Mt k r) μ invM c hm (hae.mono hinv) hc
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftingTheory
section
open Matrix in
private theorem hpk_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  have key : ∀ i : Fin (2 * r + k + 1), ∃ s : Fin (2 * r + k + 1),
      (s.val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) := fun i =>
    ⟨⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by
      have := i.isLt; split_ifs <;> omega⟩, rfl⟩
  ext i l
  obtain ⟨s, hs⟩ := key i
  have hi := i.isLt
  have hl := l.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · simp only [Formalism.QuantumDeterminants.Hpk, Matrix.one_apply, Fin.ext_iff]
    split_ifs at hs ⊢ <;> first | omega | norm_num
  · intro j _ hj
    have hj' : j.val ≠ s.val := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have : Formalism.QuantumDeterminants.Hpk k r i j = 0 := by
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs at hs ⊢ <;> first | omega | rfl
    rw [this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ s) h
end

