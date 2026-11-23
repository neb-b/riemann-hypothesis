module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Semi

abbrev ZU : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)

noncomputable abbrev torusRing (R : CommRingCat.{u}) (X : Type u) [AddCommGroup X] : CommRingCat.{u} :=
  CommRingCat.of (AddMonoidAlgebra R X)

noncomputable abbrev splitTorusAff (R : CommRingCat.{u}) (X : Type u) [AddCommGroup X] :
    Over (Spec R) :=
  (Spec (torusRing R X)).asOver (Spec R)

noncomputable example (R : CommRingCat.{u}) (X : Type u) [AddCommGroup X] : GrpObj (splitTorusAff R X) :=
  inferInstance

noncomputable def toZ (S : Scheme.{u}) : S ⟶ Spec ZU := specULiftZIsTerminal.from S

noncomputable def splitTorus (S : Scheme.{u}) (X : Type u) [AddCommGroup X] : Over S :=
  (Over.pullback (toZ S)).obj (splitTorusAff ZU X)

noncomputable instance (S : Scheme.{u}) (X : Type u) [AddCommGroup X] :
    GrpObj (splitTorus S X) :=
  Functor.grpObjObj

noncomputable abbrev Gm (S : Scheme.{u}) : Over S := splitTorus S (ULift.{u} ℤ)

variable {S : Scheme.{u}}

noncomputable def mulN (G : Over S) [GrpObj G] : ℕ → (G ⟶ G)
  | 0 => toUnit G ≫ η
  | n + 1 => lift (mulN G n) (𝟙 G) ≫ μ

noncomputable def torsion (G : Over S) [GrpObj G] (N : ℕ) : Over S :=
  pullback (mulN G N) (η : 𝟙_ (Over S) ⟶ G)

noncomputable def torsion.ι (G : Over S) [GrpObj G] (N : ℕ) : torsion G N ⟶ G :=
  pullback.fst _ _

end ReciprocityTheory.ChartRestriction.G.Semi
