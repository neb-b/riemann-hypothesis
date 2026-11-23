module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0006

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.Choice
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def rh (N : ℕ) (i : ℕ) : ℤ := (N : ℤ) - 1 - 2 * (i : ℤ)

def IsStd (w : Pl E) (s : Shuf n) (sg : Fin n → ℂˣ) : Prop :=
  ∀ k, s.eps k = sg k * qU w (rh n k - Sum.elim (fun i : Fin s.a => rh s.a i) (fun j : Fin s.b => rh s.b j) (s.e.symm k))

def chiN (w : Pl E) (ξ : Fin n → ℂˣ) : Fin n → ℂˣ := fun k => ξ k * qU w (rh n k)

def TargetAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (s : Shuf n) (sg ξ : Fin n → ℂˣ)
  (ξa : Fin s.a → ℂˣ) (ξb : Fin s.b → ℂˣ), IsStd w s sg → chiOf w s ξa ξb = chiN w ξ →
    (∀ i, ξa i = ξ (s.e (.inl i)) * (sg (s.e (.inl i)))⁻¹) ∧ ∀ j, ξb j = ξ (s.e (.inr j)) * (sg (s.e (.inr j)))⁻¹

def MonoRes : Prop := ∀ (n : ℕ) (s : Shuf n) (sg ξ : Fin n → ℂˣ), N3.Mono ξ → (∀ k, ‖((sg k : ℂˣ) : ℂ)‖ = 1) →
  N3.Mono (fun i => ξ (s.e (.inl i)) * (sg (s.e (.inl i)))⁻¹) ∧ N3.Mono (fun j => ξ (s.e (.inr j)) * (sg (s.e (.inr j)))⁻¹)

def SatSph : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n) (w : Pl E) (B : Multiset ℂˣ),
  D.Sat w B → GlobalTheory.LGrp.IsSpherical (prodAt D w) (GlobalTheory.LFun.KGL w (n := n))

end PositivityTheory.Rg.BcB.F.Tail

end
