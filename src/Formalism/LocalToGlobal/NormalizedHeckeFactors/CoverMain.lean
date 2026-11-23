module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0008
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverSplit

@[expose] public section

open Formalism.BasicNotions NumberField

namespace Formalism.L2

theorem linkEtaTw_main {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ ∀ z : (Fm.D x i).host.E, (Fm.D x i).host.conj z = IsCMField.complexConj _ z) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx⟩ := hfam
  refine linkEtaTw_of_statement Fm h ⟨x0, fun x hx' i => ?_⟩
  obtain ⟨M, T, HT, hstar⟩ := hx x hx' i
  exact ⟨M, T, HT, splitEx_of_star hstar⟩

end Formalism.L2
