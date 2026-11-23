module

public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmDiff
section
namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem symmDiff_of_holoSection (hsec : holoSectionStatement.{u}) : symmDiffStatement.{u} := by
  intro n M _ z U u hcov hU hfinU hholo k w hw
  have hloc : IsLocalHomeomorph z := by
    rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    have := hcov.isLocalHomeomorphOn
    rwa [Set.preimage_eq_univ_iff.mpr (by rintro _ ⟨x, rfl⟩; exact hU x)] at this
  obtain ⟨W, d, s, hW, hwW, hcont, hzs, hvals⟩ := sheets n M z U u hcov w hw (hfinU w hw)
  have hWn : W ∈ 𝓝 w := hW.mem_nhds hwW
  have hdiff : ∀ i, DifferentiableAt ℂ (fun v => u (s i v)) w := fun i =>
    hsec n M z u hloc hholo (s i) w ((hcont i).continuousAt hWn)
      (Filter.eventually_of_mem hWn (hzs i))
  have heq : (fun v => ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ t, u (s i v))
      =ᶠ[𝓝 w] fiberSymm n z u k := by
    filter_upwards [hWn] with v hv
    rw [fiberSymm, hvals v hv, Finset.esymm_map_val]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
  have hprod : ∀ t : Finset (Fin d), DifferentiableAt ℂ (fun v => ∏ i ∈ t, u (s i v)) w := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hdiff a).mul ih
  exact DifferentiableAt.fun_sum fun t _ => hprod t

end ReciprocityTheory.L2DbarEstimates.Norm
end

-- bundled from ReciprocityTheory.L2DbarEstimates.SymmetricSections.SymmVanish
section
namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem symmVanish : symmVanishStatement.{u} := by
  intro n M _ z U u w₀ N hcov hw₀ hfin hvan k
  obtain ⟨W, d, s, hW, hwW, hcont, hzs, hvals⟩ := sheets n M z U u hcov w₀ hw₀ hfin
  have hWn : W ∈ 𝓝 w₀ := hW.mem_nhds hwW
  have hi : ∀ i, (fun v => u (s i v)) =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ N := by
    intro i
    have hx : z (s i w₀) = w₀ := hzs i w₀ hwW
    have h1 := IsBigO.comp_tendsto (hvan (s i w₀) hx) ((hcont i).continuousAt hWn)
    refine h1.congr' (Eventually.of_forall fun v => rfl) ?_
    filter_upwards [hWn] with v hv
    simp only [Function.comp_apply, hzs i v hv, hx]
  have hprod : ∀ t : Finset (Fin d),
      (fun v => ∏ i ∈ t, u (s i v)) =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ (t.card * N) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using (isBigO_const_const (1 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0) (𝓝 w₀))
    | insert a t ha ih =>
      have hc : (insert a t).card = t.card + 1 := by
        exact Finset.card_insert_of_notMem ha
      simp only [Finset.prod_insert ha]
      rw [hc]
      exact ((hi a).mul ih).congr' (Eventually.of_forall fun v => rfl)
        (Eventually.of_forall fun v => by
          show ‖v - w₀‖ ^ N * ‖v - w₀‖ ^ (t.card * N) = ‖v - w₀‖ ^ ((t.card + 1) * N)
          rw [← pow_add]; congr 1; ring)
  have heq : (fun v => ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ t, u (s i v))
      =ᶠ[𝓝 w₀] fiberSymm n z u k := by
    filter_upwards [hWn] with v hv
    rw [fiberSymm, hvals v hv, Finset.esymm_map_val]
  refine IsBigO.congr' ?_ heq (Eventually.of_forall fun _ => rfl)
  refine IsBigO.fun_sum fun t ht => ?_
  have := hprod t
  rwa [(Finset.mem_powersetCard.mp ht).2] at this

end ReciprocityTheory.L2DbarEstimates.Norm
end

