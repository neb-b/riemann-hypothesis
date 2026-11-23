module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StTorusInvLevi
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo

def TorusInvLevi.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (u : ((Σ k, ι k) → ℂ) → ℝ),
    ContDiffOn ℝ 2 u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      u (fun p => c p.1 * z p) = u z) →
    ∃ C : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ w : (Σ k, ι k) → ℂ,
      |leviForm u z w| ≤
        C * leviForm (fun y => ∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) z w

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def DegreeGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
      ptsIntegral P (pot L) (fun _ => 1) =
        NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) (fun j => (L j).a)

theorem isArithVar_projLine : IsArithVar (⊥ : Ideal (MRing (PBlk 2))) 2 := by
  refine ⟨inferInstance, ⟨Ideal.isPrime_bot,
    ⟨∅, fun f hf => absurd hf (Set.notMem_empty f), Ideal.span_empty.symm⟩,
    fun _ => ⟨0, by rw [Submodule.mem_bot]; exact X_ne_zero _⟩⟩, ?_, ?_⟩
  · ext a
    simp [Ideal.mem_comap]
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    have hc : Nat.card ((_ : Unit) × PBlk 2 ()) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    rw [ENat.card_eq_coe_natCard, hc, Fintype.card_unit]
    rfl

theorem isSmoothHerm_fsLine (n : ℕ) : IsSmoothHerm (fsLine n) := by
  have hfun : (fsLine n).h = fun z => ∏ k : Unit, Real.sqrt (∑ i : Fin n, ‖z ⟨k, i⟩‖ ^ 2) := by
    funext z
    simp only [fsLine, HermLine.ofMetrics, fsMetric, Pi.one_apply, zpow_one,
      EuclideanSpace.norm_eq]
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => ContDiffOn.sqrt ?_ fun z hz => ?_
  · exact (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, PBlk n k))).contDiffOn
  · obtain ⟨i, hi⟩ := hz k
    exact (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsChartRankAdjoin
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def ChartRankAdjoin.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ Φ' : Type) [Field Φ] [Field Φ'] [Algebra Φ Φ']
    (z : (Σ k, ι k) → Φ') (j : ∀ k, ι k),
    (∀ k, z ⟨k, j k⟩ ≠ 0) → IsMultiHomogIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) →
      ptDeg (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) j =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range fun q : Σ k, ι k => z q / z ⟨q.1, j q.1⟩))

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

