module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0285
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0267

@[expose] public section

namespace PositivityTheory.Rg.Cz

open GlobalTheory.CuspGeneric MeasureTheory

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G]

theorem avg_sub (Γ : AddSubgroup G) (hΓ : IsCoLat Γ) (Φ Φ' : G → ℂ) (h : Per Γ Φ) (h' : Per Γ Φ') :
    avg Γ (fun x => Φ x - Φ' x) = avg Γ Φ - avg Γ Φ' :=
  GlobalTheory.CompanionTheory.CuspGeneric.avg_sub_of_per Γ hΓ Φ Φ' h h'

theorem avg_integral_swap (Γ : AddSubgroup G) (hΓ : IsCoLat Γ) (F : G × ℝ → ℂ) (hF : Continuous F)
    (hp : ∀ γ ∈ Γ, ∀ x s, F (γ + x, s) = F (x, s)) (t : ℝ) :
    avg Γ (fun x => ∫ s in (0 : ℝ)..t, F (x, s)) = ∫ s in (0 : ℝ)..t, avg Γ (fun x => F (x, s)) :=
  GlobalTheory.CompanionTheory.AvgSwap.avg_intervalIntegral_swap Γ hΓ F hF hp t

end PositivityTheory.Rg.Cz
