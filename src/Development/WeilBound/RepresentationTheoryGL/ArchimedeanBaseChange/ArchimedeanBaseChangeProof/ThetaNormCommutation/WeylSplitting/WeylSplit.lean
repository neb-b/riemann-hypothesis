module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8.G2

def KapOrbAE : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
  ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), GlobalTheory.BCT.IsTest (KL n) K' f →
  ∀ p₁ p₂ : E[X], p₁ ∈ Ell E p₁.natDegree → p₂ ∈ Ell E p₂.natDegree → IsCoprime p₁ p₂ → p₁.natDegree + p₂.natDegree = n →
    (Function.mulSupport fun w : Pl E => kapOrb n w (atPl w p₁) (atPl w p₂) (f w)).Finite

def EllLocal : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (p₁ p₂ : E[X]), p₁ ∈ Ell E a →
  p₂ ∈ Ell E b → IsCoprime p₁ p₂ → ∀ w : Pl E, (atPl w p₁).Monic ∧ (atPl w p₂).Monic ∧ (atPl w p₁).natDegree = a ∧
    (atPl w p₂).natDegree = b ∧ (atPl w p₁ * atPl w p₂).Separable ∧ IsCsr w (atPl w p₁) ∧ IsCsr w (atPl w p₂)

def ChWMap : Prop := ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n) (P : E[X]),
  chW lam P = ∏ v : InfinitePlace E, starRingEnd ℂ (chAt (lam v) (P.map v.embedding))

end PositivityTheory.Rg.BcB.G8.G2

end
