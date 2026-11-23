module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

section Dual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def DualCl (x y : IrrGL (k := k)) : Prop :=
  ∃ (n : ℕ) (π π' : IrrRep (GL (Fin n) k)), x = cls π ∧ y = cls π' ∧ Nonempty (π'.ρ.Equiv (contra π.ρ))

def SegDual (Δ Δ' : Segment k) : Prop :=
  Δ'.len = Δ.len ∧ DualCl (Δ.first.nu ((Δ.len : ℂ) - 1)) Δ'.first

end Dual

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def IsLExt (r rc : IrrGL (k := w.adicCompletion E) → WD h) : Prop :=
  ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (k := w.adicCompletion E)),
    IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep → rc x = segSum r l

end GlobalTheory.LocLanglands

end
