module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StChartScalingIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def ChartScalingIndep.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (i : ∀ k, ι k),
    (∀ k, x ⟨k, i k⟩ ≠ 0) → IsMultiHomogIdeal (RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω)) →
      AlgebraicIndependent (IntermediateField.adjoin F (Set.range fun q : Σ k, ι k => x q / x ⟨q.1, i q.1⟩))
        (fun k => x ⟨k, i k⟩)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StFnDegAdjoin
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def FnDegAdjoin.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (v : (Σ k, ι k) → (Σ k', ι' k')) (x' : (Σ k', ι' k') → Ω) (i' : ∀ k', ι' k'),
    (∀ k', x' ⟨k', i' k'⟩ ≠ 0) → IsMultiHomogIdeal (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) →
      letI := adjoinInclAlgebra F (Set.range_comp_subset_range v fun q => x' q / x' ⟨q.1, i' q.1⟩)
      fnDeg v (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i' =
        Module.finrank (Algebra.adjoin F (Set.range ((fun q => x' q / x' ⟨q.1, i' q.1⟩) ∘ v)))
          (Algebra.adjoin F (Set.range fun q => x' q / x' ⟨q.1, i' q.1⟩))

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

