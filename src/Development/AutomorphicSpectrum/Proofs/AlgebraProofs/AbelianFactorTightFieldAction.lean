module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagComparisonTheorem
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem flagConcl_directFactor_of_subquotient :
    SubquotientStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, (∀ x : N, p • x = 0) → IsAbFactor p AA.carrier → IsTight v p AA.carrier → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (Nw : Type) [AddCommGroup Nw] [Module F Nw] [Fintype Nw] [DecidableEq Nw] (i : Nw →+ N) (π : N →+ Nw), (∀ y, π (i y) = y) → (∀ h ∈ AA.carrier, (fun x => h (i (π x))) ∈ AA.carrier) → FStable F (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) → ∀ (n : ℕ) (b : Module.Basis (Fin n) F Nw) (σ : MulChar F R), IsFund p σ → FlagConcl v p (AA.carrier.map (LinearMap.funLeft R C (i : Nw → N))) b σ := by
  intro hS p _ C _ _ _ v R _ _ hInt hp hcomp N _ _ _ AA hpN hab htight F _ _ _ _ Nw _ _ _ _ i π hπi
    hstab hFS n b σ hσ
  obtain ⟨⟨A', hA'⟩, -, hgen⟩ := GlobalTheory.T.hopf_order_retract_restriction p C v R hInt hp N AA Nw i π hπi hstab
  have ht' := GlobalTheory.T.hopf_order_retract_elementary p C v R hInt hp N hpN AA Nw i π hπi hstab htight
  rw [← hA'] at hFS ht' ⊢
  refine _root_.GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds p C v R hInt hp F Nw A' hFS ht' n b ?_ σ hσ
  intro k
  rw [hA']
  exact hgen _ (hS p C v R hInt hp hcomp N AA.carrier hab _)

end GlobalTheory.CompanionTheory.Ar.GR
