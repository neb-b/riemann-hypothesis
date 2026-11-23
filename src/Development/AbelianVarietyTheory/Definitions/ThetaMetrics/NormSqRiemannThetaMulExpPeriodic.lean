module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import ReciprocityTheory.ThetaQuasiPeriods.Change
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

@[expose] public section

open Complex Matrix
open scoped Real

noncomputable section

namespace GlobalTheory.RiemannThetaModel

variable {ι : Type*} [Fintype ι]

theorem riemannTheta_eq_thetaChar {g : ℕ} (a b : Fin g → ℝ) (Ω : Matrix (Fin g) (Fin g) ℂ)
    (v : Fin g → ℂ) :
    riemannTheta a b Ω v = ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar Ω (fun i => a i) (fun i => b i) v := by
  change ∑' n, riemannThetaTerm a b Ω v n = _
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar
  refine tsum_congr fun n => ?_
  change cexp (2 * π * I * (((fun i => (n i : ℂ) + a i) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ) + a i)) / 2 +
    (fun i => (n i : ℂ) + a i) ⬝ᵥ fun i => v i + b i)) = _
  congr 1
  have e1 : ((fun i => (n i : ℂ)) + fun i => (a i : ℂ)) = fun i => (n i : ℂ) + a i := rfl
  have e2 : (v + fun i => (b i : ℂ)) = fun i => v i + b i := rfl
  rw [e1, e2]
  ring

end GlobalTheory.RiemannThetaModel
