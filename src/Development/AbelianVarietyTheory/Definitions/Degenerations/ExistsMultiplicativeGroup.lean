module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH

namespace TorusFibre
variable {k : Type} [Field k]

end TorusFibre

namespace AbelianFibre
variable {k : Type} [Field k]

theorem lbIso_of_gens {X : Scheme.{0}} {A B : LB X} (s : A.Gen) (hs : s.IsGen) (t : B.Gen) (ht : t.IsGen) :
    LBIso A B := by
  refine ⟨⟨fun p => res inf_le_left (t.s p.1) * (res inf_le_right (s.s p.2))⁻¹⟩,
    fun (p q : B.ι × A.ι) => unit_ext fun y hy => by
      have v : ∀ p : B.ι × A.ι, y ∈ B.U p.1 ⊓ A.U p.2 → gm (𝟙 X) y (B.U p.1 ⊓ A.U p.2)
          (res inf_le_left (t.s p.1) * (res inf_le_right (s.s p.2))⁻¹) =
          gm (𝟙 X) y _ (t.s p.1) * (gm (𝟙 X) y _ (s.s p.2))⁻¹ := fun p hp => by
        rw [map_mul, map_inv, gm_res (𝟙 X) y _ hp, gm_res (𝟙 X) y _ hp]
      have e₁ := congrArg (gm (𝟙 X) y _) (hs p.2 q.2)
      have e₂ := congrArg (gm (𝟙 X) y _) (ht p.1 q.1)
      have m₁ : y ∈ A.U p.2 ⊓ A.U q.2 := ⟨hy.1.2, hy.2.2⟩
      have m₂ : y ∈ B.U p.1 ⊓ B.U q.1 := ⟨hy.1.1, hy.2.1⟩
      rw [map_mul, gm_res (𝟙 X) y _ m₁, gm_res (𝟙 X) y _ m₁] at e₁
      rw [map_mul, gm_res (𝟙 X) y _ m₂, gm_res (𝟙 X) y _ m₂] at e₂
      refine ((gm_res (𝟙 X) y _ hy _).trans (v p hy.1)).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
        (gm_div A B (𝟙 X) y p q hy) ((gm_res (𝟙 X) y _ hy _).trans (v q hy.2))).trans ?_)))
      rw [e₁, e₂, mul_inv]
      exact mul_mul_mul_comm _ _ _ _⟩

end AbelianFibre

namespace MonomialImmersion
variable (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

end MonomialImmersion

end GlobalTheory.ZH
end
