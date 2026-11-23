module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0005
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Bundle0002
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeRatioConsecutive
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0011

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualLat
section
open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems Formalism.L2.G.Model

theorem letterWt_anti (m d : ℕ) (vec : Bool) : Antitone (letterWt m d vec) := by
  intro i j hij
  have hl : i = Fin.last m → j = Fin.last m := fun hi => le_antisymm (Fin.le_last j) (hi ▸ hij)
  have h0 : j = 0 → i = 0 := fun hj => le_antisymm (hj ▸ hij) (Fin.zero_le i)
  unfold letterWt
  cases vec
  · simp only [Bool.false_eq_true, if_false]
    by_cases hj : j = Fin.last m
    · by_cases hi : i = Fin.last m
      · simp [hi, hj]
      · simp [hi, hj]
    · have hi : i ≠ Fin.last m := fun hi => hj (hl hi)
      simp [hi, hj]
  · simp only [if_true]
    by_cases hj : j = 0
    · simp [hj, h0 hj]
    · by_cases hi : i = 0
      · simp [hi, hj]
      · simp [hi, hj]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptBlocksOfUSLines
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem restPairX : RestPairX :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun C0 _ _ _ _ _ CE1 CE2 _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => by
      intro X _ hD hI hc j rz ry _ A _ _ mu lam hP hK
      have hs := std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
      have hseg := (hs.segB j).2
      have hN : (2 * (X.N1 : ℝ) + 3) ≤ (X.m : ℝ) + 1 := hs.N1k
      have hN' : 2 * X.N1 + 2 ≤ X.m := by exact_mod_cast (by linarith : (2 * (X.N1 : ℝ) + 2) ≤ (X.m : ℝ))
      have hr : segS X.TT j + 1 ≤ X.m := by omega
      exact pf_X hP hr (X.La C0) (fun i => (hK i).2)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

