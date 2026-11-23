module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

@[expose] public section

noncomputable section

open IsLocalRing

namespace UpperTheory.V.Hi

variable {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M]

instance heckeCommRing (Y : Submodule A M) (op : ι → Module.End A M) [h : Fact (CommOn Y op)] : CommRing (heckeAlg Y op) :=
  { (inferInstance : Ring (heckeAlg Y op)) with
    mul_comm := fun a b => by
      have key : {t : Module.End A Y | ∃ i, Restr t (op i)}.Pairwise Commute := by
        rintro s ⟨i, hi⟩ t ⟨j, hj⟩ _
        change s * t = t * s
        refine LinearMap.ext fun y => Subtype.ext ?_
        change (s (t y) : M) = t (s y)
        rw [hi, hj, hj, hi]
        exact h.out.2 i j y y.2
      exact (Algebra.isMulCommutative_adjoin A key).is_comm.comm a b }

def heckeGen (Y : Submodule A M) (op : ι → Module.End A M) [h : Fact (CommOn Y op)] (i : ι) : heckeAlg Y op :=
  ⟨(op i).restrict (h.out.1 i), Algebra.subset_adjoin ⟨i, fun _ => rfl⟩⟩

theorem IsCNL.ofCO (O R : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing R] [Algebra O R]
    [Alg.IsCO O R] : IsCNL R := by
  exact
    { complete := inferInstance
      finite := Finite.of_surjective (ResidueField.map (algebraMap O R))
        (Alg.resMap_bijective O R).2 }

end UpperTheory.V.Hi
