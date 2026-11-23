module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CommRingSections.IsCovPr

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GroundTheory.Arith.SchemeCoh

namespace UpperTheory.Gal.DifferentialFormSections

structure IsDiv {K : Type} [CommRing K] {W E : Sch K} (i : E ⟶ W) (L : Coc W) (s : ∀ j : L.ι, Sec W (L.U j)) : Prop where
  closed : IsClosedImmersion i.left
  ker : ∀ j, RingHom.ker (secMap i (le_refl (i.left ⁻¹ᵁ L.U j))).toRingHom = Ideal.span {s j}
  nzd : ∀ j, s j ∈ nonZeroDivisors (Sec W (L.U j))
  rel : ∀ j : Fin 2 → L.ι, secRes W (inter_le (X := W.left.toTopCat) L.U j 0) (s (j 0)) =
    (L.g j).val * secRes W (inter_le (X := W.left.toTopCat) L.U j 1) (s (j 1))

end UpperTheory.Gal.DifferentialFormSections
