module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL

@[expose] public section

noncomputable section

open GlobalTheory.PRep (IsSmooth)
open GlobalTheory.SmGL (HasFiniteLength IsSubquotient)

namespace PositivityTheory.Rg.BcN.F2

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (ι : Type) [Fintype ι] [DecidableEq ι]

def FinSubq : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL ι F) U), IsSmooth ρ → HasFiniteLength ρ →
    ∃ (J : Type) (_ : Fintype J) (W : J → Type) (_ : ∀ j, AddCommGroup (W j)) (_ : ∀ j, Module ℂ (W j))
      (τ : ∀ j, Representation ℂ (GL ι F) (W j)), (∀ j, IsSmooth (τ j) ∧ (τ j).IsIrreducible ∧ IsSubquotient (τ j) ρ) ∧
      ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (τ' : Representation ℂ (GL ι F) W'), τ'.IsIrreducible →
        IsSubquotient τ' ρ → ∃ j, Nonempty (τ'.Equiv (τ j))

variable (a b : ℕ)

end PositivityTheory.Rg.BcN.F2
