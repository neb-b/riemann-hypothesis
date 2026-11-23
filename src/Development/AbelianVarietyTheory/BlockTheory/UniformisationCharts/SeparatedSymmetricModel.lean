module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.CanonicalRigidImages

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

section BaseChange

variable {S S' : Scheme.{0}} (p : S' ⟶ S)

def dn {G : Over S} {T : Over S'} (y : T ⟶ (Over.pullback p).obj G) :
    Over.mk (T.hom ≫ p) ⟶ G :=
  Over.homMk (y.left ≫ pullback.fst G.hom p) (by
    have h := Over.w y
    dsimp at h ⊢
    rw [Category.assoc, pullback.condition, ← Category.assoc, h])

lemma dn_map {G G' : Over S} {T : Over S'} (y : T ⟶ (Over.pullback p).obj G) (f : G ⟶ G') :
    dn p (y ≫ (Over.pullback p).map f) = dn p y ≫ f := by
  ext
  have h : ((Over.pullback p).map f).left ≫ pullback.fst G'.hom p =
      pullback.fst G.hom p ≫ f.left := pullback.lift_fst _ _ _
  change (y.left ≫ ((Over.pullback p).map f).left) ≫ pullback.fst G'.hom p =
    (y.left ≫ pullback.fst G.hom p) ≫ f.left
  rw [Category.assoc, Category.assoc, h]

variable {G : Over S} [GrpObj G] [IsCommMonObj G]

instance isComm_baseChange : IsCommMonObj ((Over.pullback p).obj G) :=
  Functor.isCommMonObj_obj

lemma dn_padd {T : Over S'} (a b : T ⟶ (Over.pullback p).obj G) :
    dn p (padd _ a b) = padd G (dn p a) (dn p b) := by
  rw [padd, padd, Functor.obj.μ_def, ← Category.assoc, dn_map]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · rw [← dn_map, Category.assoc, Functor.Monoidal.μ_fst, lift_fst, lift_fst]
  · rw [← dn_map, Category.assoc, Functor.Monoidal.μ_snd, lift_snd, lift_snd]

lemma dn_pzero (T : Over S') : dn p (pzero ((Over.pullback p).obj G) T) = pzero G _ := by
  rw [pzero, pzero, Functor.obj.η_def, ← Category.assoc, dn_map]
  congr 1
  exact toUnit_unique _ _

lemma dn_foldr {T : Over S'} {n : ℕ} (x : Fin n → (T ⟶ (Over.pullback p).obj G))
    (l : List (Fin n)) :
    dn p (l.foldr (fun k acc => padd _ (x k) acc) (pzero _ T)) =
      l.foldr (fun k acc => padd G (dn p (x k)) acc) (pzero G _) := by
  induction l with
  | nil => exact dn_pzero p T
  | cons a l ih => simp only [List.foldr_cons]; rw [dn_padd, ih]

variable {H : Over S'} [GrpObj H] [IsCommMonObj H]

def dn3 (f : H ⟶ (Over.pullback p).obj G) : Over.mk ((G3 H).hom ≫ p) ⟶ G3 G :=
  lift (dn p (x3 H 0 ≫ f)) (lift (dn p (x3 H 1 ≫ f)) (dn p (x3 H 2 ≫ f)))

omit [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] in
lemma downThree_comp_proj (f : H ⟶ (Over.pullback p).obj G) (k : Fin 3) :
    dn3 p f ≫ x3 G k = dn p (x3 H k ≫ f) := by
  fin_cases k <;> simp [x3, dn3]

def bcMap (f : H ⟶ (Over.pullback p).obj G) [IsMonHom f] : CubeMap H G where
  F := (dn p f).left
  F3 := (dn3 p f).left
  e := p
  e_comm := by
    have h1 : eSec H ≫ (dn p f).left = (dn p (η[H] ≫ f)).left :=
      (Category.assoc _ _ _).symm
    have h2 : η[H] ≫ f = pzero _ (𝟙_ (Over S')) := by
      rw [IsMonHom.one_hom, pzero, toUnit_unit, Category.id_comp]
    rw [h1, h2, dn_pzero, pzero, Over.comp_left, eSec]
    congr 1
  psum_comm := fun I => by
    have h1 : (psum H (x3 H) I).left ≫ (dn p f).left = (dn p (psum H (x3 H) I ≫ f)).left :=
      (Category.assoc _ _ _).symm
    have h2 : (dn3 p f).left ≫ (psum G (x3 G) I).left = (dn3 p f ≫ psum G (x3 G) I).left := rfl
    rw [h1, h2]
    congr 1
    simp only [psum]
    rw [foldr_padd_comp, dn_foldr, ← foldr_padd_pre]
    simp only [downThree_comp_proj]


end BaseChange

section Sym

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

variable {G} {S' : Scheme.{0}} {H : Over S'} [GrpObj H]

end Sym

section IsoPull

variable {X X' Y Y' : Scheme.{0}} (L : LB X) (M : LB X')

end IsoPull

section Generic

variable (R : Type) [CommRing R] [IsDomain R]

end Generic

section Levels

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

abbrev toG (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] : CubeMap (thickObj R I e G) G :=
  bcMap (thick R I e) (𝟙 (thickObj R I e G))

def toB {e : ℕ} (j : CanonicalRigidImages.GtIso D I e G) : CubeMap (thickObj R I e G) D.P.A :=
  haveI := j.q_hom
  bcMap (thick R I e) j.q




end Levels

end GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel
