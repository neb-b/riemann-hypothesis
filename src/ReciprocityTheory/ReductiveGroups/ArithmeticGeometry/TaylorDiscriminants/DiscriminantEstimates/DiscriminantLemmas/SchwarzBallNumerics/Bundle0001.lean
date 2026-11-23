module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.SchwarzBallNumerics.EBasis
section
namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem eBasis : ReciprocityTheory.ChartRestriction.G.TB.EBasisSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.EBasisSt
  intro E _ _ W _ _ _ _ _ ι _ v hv hcard
  classical
  haveI : FiniteDimensional ℚ W := Module.Finite.trans E W
  have hinj : Function.Injective v := hv.injective
  have hspanQ : Submodule.span ℚ (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hv, hcard, Module.finrank_mul_finrank]
  have hspanE : Submodule.span E (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ (Set.range v) := by rw [hspanQ]; trivial
    exact Submodule.span_le_restrictScalars ℚ E (Set.range v) hx
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent E (Set.range v)
  let s : Finset ι := Finset.univ.filter (fun i => v i ∈ b)
  have hrange : Set.range (fun i : s => v i) = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (Finset.mem_filter.mp i.2).2
    · intro hx
      obtain ⟨i, rfl⟩ := hbsub hx
      exact ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩, rfl⟩
  have hli : LinearIndependent E (fun i : s => v i) := by
    let f : s → b := fun i => ⟨v i, (Finset.mem_filter.mp i.2).2⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      exact hinj (congrArg Subtype.val hij)
    exact hbli.comp f hf
  have hspan : Submodule.span E (Set.range fun i : s => v i) = ⊤ := by
    rw [hrange, hbspan, hspanE]
  refine ⟨s, ?_, hli, hspan⟩
  have hfr := finrank_span_eq_card hli
  rw [hspan, finrank_top, Fintype.card_coe] at hfr
  exact hfr.symm

end PI.UnitaryGroupMassFormula.TBNum
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.SchwarzBallNumerics.Schwarz
section
namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem schwarzBall : ReciprocityTheory.ChartRestriction.G.TB.SchwarzBallSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.SchwarzBallSt
  intro E _ _ u ρ M hρ hu hM z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzρ : ‖z‖ < ρ := mem_ball_zero_iff.mp hz
  have hmaps : Set.MapsTo (fun w : ℂ => w • z) (Metric.ball 0 (ρ / ‖z‖)) (Metric.ball (0 : E) ρ) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_smul]
    rw [lt_div_iff₀ hzpos] at hw
    exact hw
  have hg : DifferentiableOn ℂ (fun w : ℂ => u (w • z)) (Metric.ball 0 (ρ / ‖z‖)) :=
    hu.comp (differentiable_id.smul_const z).differentiableOn hmaps
  have h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (ρ / ‖z‖) := by
    rw [mem_ball_zero_iff, norm_one, lt_div_iff₀ hzpos, one_mul]
    exact hzρ
  have hmap2 : Set.MapsTo (fun w : ℂ => u (w • z)) (Metric.ball 0 (ρ / ‖z‖))
      (Metric.closedBall (u ((0 : ℂ) • z)) M) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm, zero_smul]
    exact hM _ (hmaps hw)
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hmap2 h1
  simp only [one_smul, zero_smul, dist_eq_norm, sub_zero, norm_one, mul_one] at hS
  rw [div_div_eq_mul_div] at hS
  exact hS

end PI.UnitaryGroupMassFormula.TBNum
end

