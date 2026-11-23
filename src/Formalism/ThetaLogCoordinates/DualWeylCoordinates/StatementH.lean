module

public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def InducedSectionsSpanStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ) (R : Type) [CommRing R] [IsDomain R],
    (IsField R ∨ IsDiscreteValuationRing R ∨ Nonempty (R ≃+* ℤ)) →
    (Dominant mu → inducedSections R mu = (Submodule.span R (Set.range fun I : TIdx mu => mapCoord (n := n) R (brk mu I)) : Set _)) ∧
    (¬ Dominant mu → inducedSections R mu = {0})

def RationalBitableauLatticeStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu →
    (Submodule.span ℤ (Set.range fun I : TIdx mu => MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu I)) :
        Set (MvPolynomial (Fin n × Fin n) ℚ)) =
      {x | x ∈ Submodule.span ℚ (Set.range fun I : TIdx mu => MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu I)) ∧
        x ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => mu a + ((-(mu (lastIdx n))).toNat : ℤ))
          (MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu (canT mu)))}

end Formalism.InvariantFactorPaths.ColumnFamilies
