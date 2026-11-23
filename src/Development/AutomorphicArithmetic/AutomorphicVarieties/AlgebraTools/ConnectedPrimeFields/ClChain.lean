module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Mathlib
public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.ClConn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Bundle0001

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.clChain :
    ∀ {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
      [CommRing R] [IsLocalRing R] [Algebra O R] [IrreducibleSpace (PrimeSpectrum R)], UpperTheory.V.CA.IsCL O R → ∀ (a : Ideal R) (h k : ℕ), a ≠ ⊤ →
      ReciprocityTheory.CA.AraLE a h → ((k + h + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R →
      ∀ p ∈ a.minimalPrimes, ∀ q ∈ a.minimalPrimes,
        Relation.ReflTransGen (fun x y : Ideal R => x ∈ a.minimalPrimes ∧ y ∈ a.minimalPrimes ∧ ReciprocityTheory.CA.Linked R k x y) p q := by
  intro O R _ _ _ _ _ _ _ _ hCL a h k ha hara hdim p hp q hq
  haveI : IsNoetherianRing R := hCL.noeth
  exact chain a (k : WithBot ℕ∞) ((bridge a _).2 (clConn hCL a h k ha hara hdim)) p hp q hq
