module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Semi

def SemistableReductionZero : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A →
  ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
    (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
    (_ : Algebra V V') (_ : Algebra V' K') (_ : IsFractionRing V' K'),
    Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧
    (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) ∧
    ∃ (G : Over (Spec (CommRingCat.of V'))) (_ : GrpObj G),
      IsCommMonObj G ∧ Smooth G.hom ∧ IsSeparated G.hom ∧ QuasiCompact G.hom ∧
      (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) ∧
      Nonempty (TorusExt (specialFibre V' G))

end ReciprocityTheory.ChartRestriction.G.Semi
