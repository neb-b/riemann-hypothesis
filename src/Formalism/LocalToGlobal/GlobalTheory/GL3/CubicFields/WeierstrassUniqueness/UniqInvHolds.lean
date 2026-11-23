module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.Bundle0001

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

theorem uniqLat_holds (Λ Λ' : AddSubgroup ℂ) (hΛ : IsLat Λ) (hΛ' : IsLat Λ')
    (h2 : Formalism.MainNotions.TaylorLogMetric.g2 Λ = Formalism.MainNotions.TaylorLogMetric.g2 Λ') (h3 : Formalism.MainNotions.TaylorLogMetric.g3 Λ = Formalism.MainNotions.TaylorLogMetric.g3 Λ') : Λ = Λ' := by
  obtain ⟨L, hL⟩ := exists_periodPair_of_isLat Λ hΛ
  obtain ⟨L', hL'⟩ := exists_periodPair_of_isLat Λ' hΛ'
  obtain ⟨a2, a3⟩ := g2_g3_eq_periodPair Λ L hL
  obtain ⟨b2, b3⟩ := g2_g3_eq_periodPair Λ' L' hL'
  have e : (L.lattice : Set ℂ) = L'.lattice :=
    lattice_eq_of_weierstrassP L L'
      (weierstrassP_eventuallyEq L L' (by rw [← a2, ← b2, h2]) (by rw [← a3, ← b3, h3]))
  apply SetLike.coe_injective
  rw [← hL, ← hL', e]

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
