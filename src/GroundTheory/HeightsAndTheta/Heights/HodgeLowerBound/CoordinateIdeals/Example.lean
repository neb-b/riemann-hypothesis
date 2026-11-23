module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.LineField
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder

def chartBase (a : Fin 2) : (Σ _ : Unit, Fin 2) → ℂ := fun p => if p.2 = a then 1 else 0

def chartLin (a : Fin 2) : (Fin 1 → ℂ) →L[ℂ] ((Σ _ : Unit, Fin 2) → ℂ) :=
  ContinuousLinearMap.pi fun p => if p.2 = a then 0 else (2 : ℂ) • ContinuousLinearMap.proj 0

theorem chartLin_apply (a : Fin 2) (t : Fin 1 → ℂ) (p : Σ _ : Unit, Fin 2) :
    chartLin a t p = if p.2 = a then 0 else 2 * t 0 := by
  unfold chartLin
  split_ifs <;> simp [*]

def chartMap (a : Fin 2) (t : Fin 1 → ℂ) : (Σ _ : Unit, Fin 2) → ℂ := chartBase a + chartLin a t

theorem chartMap_apply (a : Fin 2) (t : Fin 1 → ℂ) (p : Σ _ : Unit, Fin 2) :
    chartMap a t p = if p.2 = a then 1 else 2 * t 0 := by
  simp only [chartMap, Pi.add_apply, chartBase, chartLin_apply]
  split_ifs <;> simp

end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
