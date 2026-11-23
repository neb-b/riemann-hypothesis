module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TorsBoundPow

@[expose] public section

noncomputable section

open CategoryTheory NumberField
open scoped TensorProduct

namespace UpperTheory.FiniteGenerationAndTorsion

open UpperTheory.V.KH

def FgShift : Prop :=
  ∀ (G : Type) [Group G] (A s m : ℕ) (X : ℕ → Type) [∀ p, MulAction G (X p)]
    (d : ∀ p, permRep G (X (p + 1)) ⟶ permRep G (X p)) (M : Rep ℤ G) (e : permRep G (X 0) ⟶ M),
    1 ≤ s → Function.Surjective e.hom → Function.Exact (d 0).hom e.hom →
    (∀ p, p < m → Function.Exact (d (p + 1)).hom (d p).hom) →
    (∀ p, p ≤ m → OrbLe G (X p) A) → (∀ p, p ≤ m → StabLe G (X p) s) →
    Module.Finite ℤ (groupHomology M m)

def HglFG : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ N m : ℕ, Module.Finite ℤ (UpperTheory.V.K.HGL L N m)

end UpperTheory.FiniteGenerationAndTorsion

end
