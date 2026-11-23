module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitArchSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitArchSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    Geo.arInt (orbitIdeal x) s A.toGeo (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) =
      (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) / Module.finrank ℚ (coordField x) *
        ∑ σ : coordField x →+* ℂ,
          Real.log (‖evalCone (fun k i ↦ σ (coordVec x k i)) s‖ /
            A.metric (fun k i ↦ σ (coordVec x k i)))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitCurve.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (x : Cone n (AlgebraicClosure ℚ)), BlockNonzero x →
    Geo.IsArithVar (ι := blockIdx n) (orbitIdeal x) 1

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitDegree.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x → 0 < Geo.degC (ι := blockIdx n) (orbitIdeal x)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitDivVertical
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitDivVertical.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ¬ Geo.IsHorizontal (ι := blockIdx n) V

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitFiniteSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitFiniteSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∑ᶠ V ∈ Geo.divSupp (orbitIdeal x) s,
        (Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) *
          ((Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V)) =
      (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) / Module.finrank ℚ (coordField x) *
        ∑ᶠ v : FinitePlace (coordField x),
          (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightRecR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def HeightRecR.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (I : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    Geo.recR I (orbitIdeal x) (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) A.toGeo s =
      (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) * height A x

end GroundTheory.Heights₂.Heights
end

