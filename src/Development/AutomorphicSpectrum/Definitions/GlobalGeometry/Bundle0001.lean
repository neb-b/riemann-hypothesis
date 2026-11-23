module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def genPt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : X := ξ (IsLocalRing.closedPoint Ω)

def Cpt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Type := {p : X // genPt ξ ⤳ p}

def genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : X.presheaf.stalk p.1 →+* Ω :=
  (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom

def regAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : Subring Ω := (genMap ξ p).range

def unitAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω) : Prop :=
  a ≠ 0 ∧ a ∈ regAt ξ p ∧ a⁻¹ ∈ regAt ξ p

structure IsCptGen (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Prop where
  bij : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom
  inj : ∀ p : Cpt ξ, Function.Injective (genMap ξ p)

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

abbrev epsAt (x : Spec (CommRingCat.of R) ⟶ S) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)

def IsTanAt (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (v : epsAt x ⟶ G) : Prop :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ v.left = (1 : Over.mk x ⟶ G).left

def epsMul (c : R) : DualNumber R →+* DualNumber R :=
  (TrivSqZeroExt.map (c • (LinearMap.id : R →ₗ[R] R))).toRingHom

def dualMap (φ : R →+* R') : DualNumber R →+* DualNumber R' where
  toFun a := TrivSqZeroExt.inl (φ a.fst) + TrivSqZeroExt.inr (φ a.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

structure LieModel (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E]
    [Module R E] where

  pt : E → (epsAt x ⟶ G)
  tan : ∀ e, IsTanAt G x (pt e)
  inj : Function.Injective pt
  onto : ∀ v, IsTanAt G x v → ∃ e, pt e = v
  add : ∀ e e', pt (e + e') = pt e * pt e'
  smul : ∀ (c : R) e, (pt (c • e)).left = Spec.map (CommRingCat.ofHom (epsMul c)) ≫ (pt e).left

def LieModel.IsDiffOf {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E]
    [Module R E] (M : LieModel G x E) (f : G ⟶ G) (A : E →ₗ[R] E) : Prop :=
  ∀ e, M.pt (A e) = M.pt e ≫ f

def LieModel.IsActOf {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E]
    [Module R E] (M : LieModel G x E) {O : Type} [CommRing O] (act : O → (G ⟶ G))
    (ρ : O →+* Module.End R E) : Prop :=
  ∀ a, M.IsDiffOf (act a) (ρ a)

def eigSp {E : Type} [AddCommGroup E] [Module R E] {O : Type} [CommRing O] (ρ : O →+* Module.End R E)
    (σ : O →+* R) : Submodule R E :=
  ⨅ a, LinearMap.ker (ρ a - σ a • LinearMap.id)

end GlobalTheory.CompanionTheory.Ar
end
end

