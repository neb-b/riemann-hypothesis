module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.IsTorus

@[expose] public section

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Semi

abbrev specMap (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

abbrev baseChange (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    (X : Over (Spec (CommRingCat.of A))) : Over (Spec (CommRingCat.of B)) :=
  (Over.pullback (specMap A B)).obj X

abbrev genFibre (W : Type) [CommRing W] [IsDomain W] (X : Over (Spec (CommRingCat.of W))) :
    Over (Spec (CommRingCat.of (FractionRing W))) :=
  baseChange W (FractionRing W) X

abbrev specialFibre (W : Type) [CommRing W] [IsLocalRing W] (X : Over (Spec (CommRingCat.of W))) :
    Over (Spec (CommRingCat.of (IsLocalRing.ResidueField W))) :=
  baseChange W (IsLocalRing.ResidueField W) X

structure TorusExt {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G] where

  B : Over (Spec (.of K))
  [grpB : GrpObj B]
  isAbelian : IsAbelianScheme B

  q : G ⟶ B
  q_hom : IsMonHom q
  q_flat : Flat q.left
  q_surjective : Surjective q.left
  q_quasiCompact : QuasiCompact q.left

  T₀ : Over (Spec (.of K))
  [grpT : GrpObj T₀]
  isTorus : IsTorus T₀
  i : T₀ ⟶ G
  i_hom : IsMonHom i

  isKernel : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)

attribute [instance] TorusExt.grpB TorusExt.grpT

end ReciprocityTheory.ChartRestriction.G.Semi
