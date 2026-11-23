module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Published

def DefQuatExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Even (Module.finrank ℚ F) → Nonempty (DefQuat F)

def FormsFiniteReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (L : Subgroup (GL (Fin a) (Af F))),
    IsOpen (L : Set (GL (Fin a) (Af F))) →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (TR.Kinf F a) W),
      GlobalTheory.Published.AutFin.IsContRep ρ → ∀ c : InfinitePlace F → ℂ → ℂ,
      FiniteDimensional ℂ (Submodule.span ℂ {φ : TR.Sm F a | TR.IsAutForm φ ∧ (∀ k ∈ L, TR.finRep F a k φ = φ) ∧
        (∀ g : GA F a, (fun k : TR.Kinf F a => (TR.cptRep F a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
        ∀ v u, TR.cap v u φ = c v u • φ})

def CuspSemisimpleReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a), TR.IsCuspForm φ →
    (∃ s : ℂ, TR.lie F a (TR.oneL F a) φ = s • φ) → φ ∈ ⨆ π : TR.CuspSub F a, π.V

end UpperTheory.V.Published
