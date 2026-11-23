module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.WeilBound.CoreStatements.FlagImmersions.ArithmeticIntersectionDivisorSupport
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0016
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionDivisorSupport
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem kleiman_generic_fibre_integral : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι), IsArithVar W (e + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j W', IsArithVar W' 2 → W ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) :=
  RootFieldNumerics.arithmetic_intersection_divisor_support

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainArithVarietyStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_chain_arith_variety : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [Nonempty K] (j : K → FlBlock Ψ N), IsChain j → IsArithVar (PPart j) (cellDim j + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.isArithVar_pPart | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.isArithVar_pPart | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.isArithVar_pPart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightI9PropertiesStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height_I9_properties : PB.FlagHeight → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N → I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9 | exact GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9 | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9 <;> assumption)
end

