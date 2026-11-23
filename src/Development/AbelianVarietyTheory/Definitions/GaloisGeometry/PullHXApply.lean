module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsContinuousForgetForget
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Sites
variable {Z Y U Z' Y' U' : Scheme.{0}}


set_option backward.isDefEq.respectTransparency.types false in
def bcSq {a : Z ⟶ Z'} {i' : Z' ⟶ Y'} {i : Z ⟶ Y} {b : Y ⟶ Y'} (h : a ≫ i' = i ≫ b) :
    bc i' ⋙ bc a ≅ bc b ⋙ bc i :=
  (MorphismProperty.Over.pullbackComp a i').symm ≪≫ MorphismProperty.Over.pullbackCongr h ≪≫
    MorphismProperty.Over.pullbackComp i b


set_option backward.isDefEq.respectTransparency.types false in
def bcComp {f : U ⟶ Z} {g : Z ⟶ Y} {k : U ⟶ Y} (h : f ≫ g = k) : bc g ⋙ bc f ≅ bc k :=
  (MorphismProperty.Over.pullbackComp f g).symm ≪≫ MorphismProperty.Over.pullbackCongr h


set_option backward.isDefEq.respectTransparency.types false in
def bcFst (f : U ⟶ Y) : bc f ⋙ (Scheme.Etale.forget U ⋙ Over.forget U) ⟶ Scheme.Etale.forget Y ⋙ Over.forget Y where
  app V := pullback.fst V.hom f
  naturality V W g := pullback.lift_fst _ _ _

end Sites

variable (R : Type) [CommRing R]

section Functors
variable {Z Y U Z' Y' U' : Scheme.{0}}

instance (f : U ⟶ Y) : (bc f ⋙ (Scheme.Etale.forget U ⋙ Over.forget U)).IsContinuous Y.smallEtaleTopology
    Scheme.etaleTopology :=
  Functor.isContinuous_comp _ _ _ U.smallEtaleTopology _

def resUnit (f : U ⟶ Y) : Rel.res R Y ⟶ Rel.res R U ⋙ push R f :=
  Functor.sheafPushforwardContinuousNatTrans (bcFst f) _ _ _

def nb (i : Z ⟶ Y) (j : U ⟶ Y) : Shv R ⥤ ShvS R Z := Rel.res R U ⋙ push R j ⋙ Rel.pull R i

instance (X : Scheme.{0}) : (Rel.res R X).Additive where
  map_add := rfl

instance (i : Z ⟶ Y) (j : U ⟶ Y) : (nb R i j).Additive := by
  unfold nb; infer_instance

instance {A : Z'.Etale ⥤ Z.Etale} [A.IsContinuous Z'.smallEtaleTopology Z.smallEtaleTopology] (i' : Z' ⟶ Y') :
    (bc i' ⋙ A).IsContinuous Y'.smallEtaleTopology Z.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ Z'.smallEtaleTopology _

instance (i : Z ⟶ Y) (b : Y ⟶ Y') :
    (bc b ⋙ bc i).IsContinuous Y'.smallEtaleTopology Z.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ Y.smallEtaleTopology _

def pushSq {A : Z'.Etale ⥤ Z.Etale} [A.IsContinuous Z'.smallEtaleTopology Z.smallEtaleTopology]
    {i' : Z' ⟶ Y'} {i : Z ⟶ Y} {b : Y ⟶ Y'} (α : bc i' ⋙ A ⟶ bc b ⋙ bc i) :
    push R i ⋙ push R b ⟶ A.sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) _ _ ⋙ push R i' :=
  Functor.sheafPushforwardContinuousNatTrans α _ _ _

def bcMap {A : Z'.Etale ⥤ Z.Etale} [A.IsContinuous Z'.smallEtaleTopology Z.smallEtaleTopology]
    {i' : Z' ⟶ Y'} {i : Z ⟶ Y} {b : Y ⟶ Y'} (α : bc i' ⋙ A ⟶ bc b ⋙ bc i) :
    push R b ⋙ Rel.pull R i' ⟶ Rel.pull R i ⋙ A.sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) _ _ :=
  ((mateEquiv (adj (R := R) i) (adj (R := R) i')).symm (TwoSquare.mk _ _ _ _ (pushSq R α))).natTrans

def trans {A : Z'.Etale ⥤ Z.Etale} [A.IsContinuous Z'.smallEtaleTopology Z.smallEtaleTopology]
    {i' : Z' ⟶ Y'} {j' : U' ⟶ Y'} {i : Z ⟶ Y} {j : U ⟶ Y} {b : Y ⟶ Y'} {c : U ⟶ U'}
    (α : bc i' ⋙ A ⟶ bc b ⋙ bc i) (hc : c ≫ j' = j ≫ b) :
    nb R i' j' ⟶ nb R i j ⋙ A.sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) _ _ :=
  Functor.whiskerRight (Functor.whiskerRight (resUnit R c) (push R j') ≫
      Functor.whiskerLeft (Rel.res R U) (pushSq R (bcSq hc).inv)) (Rel.pull R i') ≫
    Functor.whiskerLeft (Rel.res R U ⋙ push R j) (bcMap R α)

end Functors

end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

variable (R : Type) [CommRing R]

section Flat
variable {Z Y U Z' Y' U' : Scheme.{0}}

def nbC (i : Z ⟶ Y) (j : U ⟶ Y) (F : Shv R) : CochainComplex (ShvS R Z) ℤ :=
  ((nb R i j).mapHomologicalComplex _).obj (GlobalTheory.EtC.res R F)

def nbCMap (i : Z ⟶ Y) (j : U ⟶ Y) {F G : Shv R} (φ : F ⟶ G) : nbC R i j F ⟶ nbC R i j G :=
  ((nb R i j).mapHomologicalComplex _).map (resMap R φ)

end Flat

section HX
variable {Z Z' : Scheme.{0}}

end HX

end GlobalTheory.EtC.Psi
