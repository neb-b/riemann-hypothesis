module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.DiffIndepStatement
section
namespace ReciprocityTheory.ChartRestriction.G.AR

def DiffIndepStatement.{u, v} : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω] [CharZero K] (D : ℕ)
    (x : Fin D → Ω),
    LinearIndependent Ω (fun k => KaehlerDifferential.D K Ω (x k)) → AlgebraicIndependent K x

end ReciprocityTheory.ChartRestriction.G.AR
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetIndepStatement
section
namespace ReciprocityTheory.ChartRestriction.G.AR

def multiLt (D a : ℕ) : Finset (Fin D → ℕ) :=
  (Finset.range a).biUnion (fun d => Finset.Nat.antidiagonalTuple D d)

end ReciprocityTheory.ChartRestriction.G.AR
end

