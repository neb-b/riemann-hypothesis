module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.V.Z.Bc

def Gap2 {F : Type} [Field F] (inf : (F →+* ℂ) → Multiset ℂ → Prop) : Prop :=
  ∀ τ, ∃ (a : ℂ) (k : ℕ), 2 ≤ k ∧ inf τ {a, a + k}

def GapTwo : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin 2) (Qbar l)) (P : CuspSub F 2), (CG.mk P).IsRegAlg → AttC ι r P →
    (∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (r s) ^ N = 1) → Gap2 P.HasInfChar

end UpperTheory.V.Z.Bc
