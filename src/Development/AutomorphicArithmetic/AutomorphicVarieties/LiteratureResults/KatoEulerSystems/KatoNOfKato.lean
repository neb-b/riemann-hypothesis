module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published.Kato Polynomial
open CongruenceSubgroup UpperTheory.V.Alg
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Lit

def OrdPoly {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] (a b : ℤ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  ∃ (A : ValuationSubring Ω) (N : ℕ), A.valuation (l : Ω) < 1 ∧ 1 ≤ N ∧ ∀ s ∈ Ine (F := ℚ) A, (∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) →
    (V s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
      (X - C ((cycBar ℚ Ω l s ^ a : (Qbar l)ˣ) : Qbar l)) * (X - C ((cycBar ℚ Ω l s ^ b : (Qbar l)ˣ) : Qbar l))

end UpperTheory.V.Lit
