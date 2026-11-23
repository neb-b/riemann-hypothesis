module

public import Formalism.ConjugateSelfDual.Galois

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Polynomial Filter
open scoped ModularForm MatrixGroups
namespace Formalism.ConjugateSelfDual
abbrev Qbar (l : ℕ) [Fact l.Prime] := PadicAlgCl l

def cyc (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    G F Ω →* (Qbar l)ˣ :=
  (Units.map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom).comp
    ((cyclotomicCharacter (Ω) l).comp
      (MulSemiringAction.toRingAut (G F Ω) (Ω)))

section places

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def normV (v : HeightOneSpectrum (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ v.asIdeal)

def IsFrob (A : ValuationSubring (Ω)) (q : ℕ) (σ : G F Ω) : Prop :=
  σ ∈ A.decompositionSubgroup F ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1

end places
end Formalism.ConjugateSelfDual
end
