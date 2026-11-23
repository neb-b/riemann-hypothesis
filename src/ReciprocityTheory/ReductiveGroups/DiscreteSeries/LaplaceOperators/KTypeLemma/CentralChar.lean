module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0015
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.TopCap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0016
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0005

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem centralChar (n : ℕ) : CentralCharStatement n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hcas hVK hint hanti hgap hp hq ω y hy
  obtain ⟨hg, hnpq, h8, -⟩ := gapCentral n ε lam h hgap
  have hlam : S7.IsHCParam lam := ⟨hanti, hint⟩
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨μ, hμ⟩ := S7.exists_mu hlam
  have hq0 : 1 ≤ S7.q0 ε := le_min hp hq
  have hP : IsPsiFor ε lam T (S7.PsiM T μ) := by
    refine ⟨fun k₁ k₂ g hg' => S7.psiM_equiv T μ k₁ k₂ hg', S7.psiM_one T μ,
      S7.psiM_smooth T μ hμ, fun g hg' => S7.psiM_casimir T μ hμ hg', ?_⟩
    intro ν hν
    exact (S7.psiM_integrable T μ hμ hlam hg hq0 ν).2.1
      (by unfold S7.q0; push_cast; exact h8)
  have hstd : StdGap ε lam := ⟨hanti, h, hg, hnpq⟩
  have hV0 : V ≠ ⊥ := by
    obtain ⟨w, hw, hw0, -⟩ := hV.2.2.2
    intro hb
    rw [hb] at hw
    exact hw0 ((Submodule.mem_bot ℂ).1 hw)
  have key := capelli_data hstd hσ hD hV hcas hVK hV0 hP
    (fun Y g hg' => S7.psiCapelli (n := n) ε lam T μ hμ Y g hg') (ω - ((n : ℂ) - 1) / 2) y hy
  rw [sub_add_cancel] at key
  rw [capelliQdet.1 (Module.End ℂ D) n E ω, key, capelliQdet.{0}.2]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
