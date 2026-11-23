module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

structure AbVar (K : Type) [Field K] where

  X : Over (Sp K)
  [grp : GrpObj X]
  ab : IsAbelianScheme X

  dim : ℕ
  smooth : SmoothOfRelativeDimension dim X.hom

attribute [instance] AbVar.grp

namespace AbVar

variable {K : Type} [Field K]

instance (A : AbVar K) : IsCommMonObj A.X := A.ab.comm

def homSub (A B : AbVar K) : Subgroup (A.X ⟶ B.X) where
  carrier := {f | IsMonHom f}
  mul_mem' := fun {f g} hf hg => by
    have : IsMonHom f := hf
    have : IsMonHom g := hg
    exact inferInstanceAs (IsMonHom (lift f g ≫ μ[B.X]))
  one_mem' := by
    change IsMonHom (1 : A.X ⟶ B.X)
    rw [CategoryTheory.Hom.one_def]
    infer_instance
  inv_mem' := fun {f} hf => by
    have : IsMonHom f := hf
    change IsMonHom (f⁻¹)
    infer_instance

def Hom (A B : AbVar K) : Type := Additive (homSub A B)

def Hom.hom {A B : AbVar K} (f : Hom A B) : A.X ⟶ B.X := (Additive.toMul (α := homSub A B) f).1

instance {A B : AbVar K} (f : Hom A B) : IsMonHom f.hom := (Additive.toMul (α := homSub A B) f).2

def Hom.mk {A B : AbVar K} (f : A.X ⟶ B.X) [h : IsMonHom f] : Hom A B :=
  Additive.ofMul (α := homSub A B) ⟨f, h⟩

instance : Category (AbVar K) where
  Hom := Hom
  id A := Hom.mk (𝟙 A.X)
  comp f g := Hom.mk (f.hom ≫ g.hom)
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

@[simp] theorem id_hom (A : AbVar K) : Hom.hom (𝟙 A) = 𝟙 A.X := rfl

@[simp] theorem comp_hom {A B C : AbVar K} (f : A ⟶ B) (g : B ⟶ C) : Hom.hom (f ≫ g) = f.hom ≫ g.hom := rfl

@[simp] theorem mk_hom {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] : (Hom.mk f : Hom A B).hom = f := rfl

instance : Preadditive (AbVar K) where
  homGroup A B := inferInstanceAs (AddCommGroup (Additive (homSub A B)))
  add_comp _ _ _ f f' g := Subtype.ext (MonObj.mul_comp f.hom f'.hom g.hom)
  comp_add _ _ _ f g g' := Subtype.ext (MonObj.comp_mul f.hom g.hom g'.hom)

@[simp] theorem add_hom {A B : AbVar K} (f g : A ⟶ B) : Hom.hom (f + g) = f.hom * g.hom := rfl

@[simp] theorem zero_hom (A B : AbVar K) : Hom.hom (0 : A ⟶ B) = 1 := rfl

@[simp] theorem neg_hom {A B : AbVar K} (f : A ⟶ B) : Hom.hom (-f) = f.hom⁻¹ := rfl

@[simp] theorem nsmul_hom {A B : AbVar K} (n : ℕ) (f : A ⟶ B) : Hom.hom (n • f) = f.hom ^ n := rfl

@[simp] theorem zsmul_hom {A B : AbVar K} (n : ℤ) (f : A ⟶ B) : Hom.hom (n • f) = f.hom ^ n := rfl

def IsIsogeny {A B : AbVar K} (f : A ⟶ B) : Prop := IsFinite f.hom.left ∧ Surjective f.hom.left

def origin (A : AbVar K) : A.X.left :=
  (1 : Over.mk (𝟙 (Sp K)) ⟶ A.X).left (IsLocalRing.closedPoint K)


open Classical in
def deg {A B : AbVar K} (f : A ⟶ B) : ℕ := if IsIsogeny f then f.hom.left.finrank B.origin else 0

abbrev End0 (A : AbVar K) : Type := ℚ ⊗[ℤ] End A

def toEnd0 (A : AbVar K) : End A →+* End0 A := Algebra.TensorProduct.includeRight.toRingHom

abbrev Pt (A : AbVar K) : Type := ptOver K (AlgebraicClosure K) ⟶ A.X

abbrev Gal (K : Type) [Field K] : Type := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K

def ptMap {A B : AbVar K} (f : A ⟶ B) : A.Pt →* B.Pt :=
  MonoidHom.mk' (fun x => x ≫ f.hom) fun x y => MonObj.mul_comp x y f.hom

@[simp] theorem ptMap_apply {A B : AbVar K} (f : A ⟶ B) (x : A.Pt) : ptMap f x = x ≫ f.hom := rfl

section Tate

variable (l : ℕ) [Fact l.Prime]

abbrev Tl (A : AbVar K) : Type := Tate l A.Pt

abbrev Vl (A : AbVar K) : Type := ℚ_[l] ⊗[ℤ_[l]] Tl l A

def tmap (A B : AbVar K) : (A ⟶ B) →+ (Tl l A →ₗ[ℤ_[l]] Tl l B) :=
  AddMonoidHom.mk' (fun f => Tate.map l (ptMap f)) fun f g =>
    LinearMap.ext fun t => Tate.ext fun n => MonObj.comp_mul (t.lev n) f.hom g.hom

theorem lev_tmap {A B : AbVar K} (f : A ⟶ B) (t : Tl l A) (n : ℕ) :
    (tmap l A B f t).lev n = t.lev n ≫ f.hom := rfl

theorem tmap_comp {A B C : AbVar K} (f : A ⟶ B) (g : B ⟶ C) :
    tmap l A C (f ≫ g) = tmap l B C g ∘ₗ tmap l A B f :=
  LinearMap.ext fun t => Tate.ext fun n => (Category.assoc (t.lev n) f.hom g.hom).symm

theorem tmap_id (A : AbVar K) : tmap l A A (𝟙 A) = LinearMap.id :=
  LinearMap.ext fun t => Tate.ext fun n => Category.comp_id (t.lev n)

def vmap {A B : AbVar K} (f : A ⟶ B) : Vl l A →ₗ[ℚ_[l]] Vl l B := (tmap l A B f).baseChange ℚ_[l]

def tend (A : AbVar K) : End A →+* Module.End ℤ_[l] (Tl l A) where
  toFun f := tmap l A A f.asHom
  map_one' := tmap_id l A
  map_mul' f g := tmap_comp l g.asHom f.asHom
  map_zero' := map_zero (tmap l A A)
  map_add' f g := map_add (tmap l A A) f.asHom g.asHom

end Tate

def IsCharpoly {A : AbVar K} (f : End A) (P : Polynomial ℤ) : Prop :=
  P.Monic ∧ P.natDegree = 2 * A.dim ∧ ∀ n : ℤ, P.eval n = (deg ((n : End A) - f).asHom : ℤ)


open Classical in
def charpoly {A : AbVar K} (f : End A) : Polynomial ℤ := if h : ∃ P, IsCharpoly f P then h.choose else 0

def trace {A : AbVar K} (f : End A) : ℤ := -(charpoly f).nextCoeff


def lam {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) : Pic Y.left :=
  CechPic.pull (x * y).left c - CechPic.pull x.left c - CechPic.pull y.left c

def IsAdj {A B : AbVar K} (c : Pic A.X.left) (d : Pic B.X.left) (f : A ⟶ B) (n : ℤ) (h : B ⟶ A) : Prop :=
  n • lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X) = lam c (fst A.X B.X) (snd A.X B.X ≫ h.hom)

def IsAmpleCls {A : AbVar K} (c : Pic A.X.left) : Prop :=
  ∃ (L : LB A.X.left) (hL : L.IsLB), Out.RelAmple A.X L ∧ cls L hL = c

def zero (K : Type) [Field K] : AbVar K where
  X := 𝟙_ (Over (Sp K))
  ab := GlobalTheory.Diag.isAbelianScheme_unit _
  dim := 0
  smooth := inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 (Sp K)))

def prod (A B : AbVar K) : AbVar K where
  X := A.X ⊗ B.X
  ab := GlobalTheory.SemiProd.isAbelianScheme_tensor A.ab B.ab
  dim := A.dim + B.dim
  smooth := by
    have := A.smooth
    have := B.smooth
    have h : SmoothOfRelativeDimension B.dim (pullback.fst A.X.hom B.X.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (n := B.dim)).of_isPullback
        (IsPullback.of_hasPullback A.X.hom B.X.hom).flip B.smooth
    have := smoothOfRelativeDimension_comp (n := B.dim) (m := A.dim) (pullback.fst A.X.hom B.X.hom) A.X.hom
    rw [add_comm]
    exact this

def prodFst (A B : AbVar K) : prod A B ⟶ A := Hom.mk (A := prod A B) (fst A.X B.X)
  (h := inferInstanceAs (IsMonHom (fst A.X B.X)))

def prodSnd (A B : AbVar K) : prod A B ⟶ B := Hom.mk (A := prod A B) (snd A.X B.X)
  (h := inferInstanceAs (IsMonHom (snd A.X B.X)))

def prodLift {T A B : AbVar K} (f : T ⟶ A) (g : T ⟶ B) : T ⟶ prod A B :=
  Hom.mk (B := prod A B) (lift f.hom g.hom) (h := inferInstanceAs (IsMonHom (lift f.hom g.hom)))

def baseChange (L : Type) [Field L] [Algebra K L] (A : AbVar K) : AbVar L where
  X := (Over.pullback (spMap (algebraMap K L))).obj A.X
  ab := GlobalTheory.isAbelianScheme_pullback_obj _ A.X A.ab
  dim := A.dim
  smooth := (smoothOfRelativeDimension_isStableUnderBaseChange (n := A.dim)).of_isPullback
    (IsPullback.of_hasPullback A.X.hom (spMap (algebraMap K L))) A.smooth

def bcMap (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f : A ⟶ B) : baseChange L A ⟶ baseChange L B :=
  Hom.mk (A := baseChange L A) (B := baseChange L B) ((Over.pullback (spMap (algebraMap K L))).map f.hom)
    (h := inferInstanceAs (IsMonHom ((Over.pullback (spMap (algebraMap K L))).map f.hom)))

@[reducible] def algΓ (A : AbVar K) : Algebra K Γ(A.X.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ A.X.hom.appTop).hom.toAlgebra

def inter (A : AbVar K) {J : Type} [Fintype J] (c : J → Pic A.X.left) : ℤ :=
  letI := A.algΓ
  multiDiff c (chiPic K (structureModule A.X.left)) 0

def IsDualPair (A B : AbVar K) (P : LB (A.X ⊗ B.X).left) : Prop :=
  AbDual.IsDual A.X B.X P ∧ AbDual.IsDual B.X A.X (AbDual.swap P)


open GlobalTheory.WeierstrassCurve in
def ell (W : WeierstrassCurve K) [W.IsElliptic] : AbVar K where
  X := (ellPolAV W).A
  ab := (ellPolAV W).isAb
  dim := 1
  smooth := (ellPolAV W).smoothDim



theorem lam_eq {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) :
    lam c x y = CechPic.lam c x y := by
  have h : CechPic.pull (1 : Y ⟶ A.X).left c = 0 := by
    rw [CategoryTheory.Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨V, hV, hc⟩ := AbDual.exists_pull_eq_zero (CechPic.pull (η[A.X]).left c) (IsLocalRing.closedPoint K)
    exact AbDual.pull_eq_zero_of_mem V _ (fun z => by
      have : (toUnit Y).left z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
      rw [this]; exact hV) hc
  rw [lam, CechPic.lam, h, add_zero]

end AbVar

end GlobalTheory.AV
