module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0584

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv Formalism.IndefR.Mi Formalism.IndefR.Mult MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RatMxCovol

theorem exists_isCovolOne_ratMx : ∀ (D : D7) (m n : ℕ), ∃ (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)),
    IsCovolOne (ratMx D m n) μ 𝓕 := by
  intro D m n
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  have : BorelSpace (Mx D m n) := ⟨rfl⟩
  exact GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (Mx D m n) (ratMx D m n) ⟨i5, K, hK, hc⟩

end GlobalTheory.CompanionTheory.RatMxCovol
