module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ConeClZeroBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

universe v u

variable {k k' k'' : Type} [CommRing k] [CommRing k'] [CommRing k''] {X X' X'' : Scheme.{0}}

def resAlg (σ : k →+* k') (B : CommAlgCat.{0} k') : CommAlgCat.{0} k :=
  letI : Algebra k B := Algebra.compHom B σ
  CommAlgCat.of k B

def resHom (σ : k →+* k') {B B' : CommAlgCat.{0} k'} (f : B ⟶ B') : resAlg σ B ⟶ resAlg σ B' :=
  letI : Algebra k B := Algebra.compHom B σ
  letI : Algebra k B' := Algebra.compHom B' σ
  CommAlgCat.ofHom { (f.hom : B →+* B') with commutes' := fun r ↦ f.hom.commutes (σ r) }

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := Spec.map_comp _ _

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem eq_of_spMap_eq {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := congrArg CommRingCat.Hom.hom (Spec.map_injective h)

structure AffPt (s : X ⟶ Sp k) : Type 1 where

  B : CommAlgCat.{0} k

  x : Sp B ⟶ X

  w : x ≫ s = spMap (algebraMap k B)

namespace AffPt

variable {s : X ⟶ Sp k}

instance : Category.{0} (AffPt s) where
  Hom T T' := {φ : T.B ⟶ T'.B // spMap (φ.hom : T.B →+* T'.B) ≫ T.x = T'.x}
  id T := ⟨𝟙 _, by
    rw [show spMap ((𝟙 T.B : T.B ⟶ T.B).hom : T.B →+* T.B) = 𝟙 _ from spMap_id' _, Category.id_comp]⟩
  comp {T T' T''} φ ψ := ⟨φ.1 ≫ ψ.1, by
    have e : ((φ.1 ≫ ψ.1).hom : T.B →+* T''.B) =
        (ψ.1.hom : T'.B →+* T''.B).comp (φ.1.hom : T.B →+* T'.B) := rfl
    rw [e, spMap_comp', Category.assoc, φ.2, ψ.2]⟩
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

theorem hom_ext {T T' : AffPt s} {φ ψ : T ⟶ T'} (h : φ.1 = ψ.1) : φ = ψ :=
  Subtype.ext h

end AffPt

def OPt (s : X ⟶ Sp k) : AffPt s ⥤ CommAlgCat.{0} k where
  obj T := T.B
  map φ := φ.1
  map_id _ := rfl
  map_comp _ _ := rfl

section Coef

variable {s : X ⟶ Sp k} {σ : k →+* k'} {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} k'}
  (x : ∀ T : C, Sp (F.obj T) ⟶ X) (hx : ∀ T, x T ≫ s = spMap ((algebraMap k' (F.obj T)).comp σ))
  (hc : ∀ ⦃T T' : C⦄ (a : T ⟶ T'), spMap (mp F a : F.obj T →+* F.obj T') ≫ x T = x T')

def ptFun : C ⥤ AffPt s where
  obj T := ⟨resAlg σ (F.obj T), x T, hx T⟩
  map a := ⟨resHom σ (F.map a), hc a⟩
  map_id T := AffPt.hom_ext (CommAlgCat.hom_ext (AlgHom.ext fun b ↦ mp_id F T b))
  map_comp a b := AffPt.hom_ext (CommAlgCat.hom_ext (AlgHom.ext fun c ↦ mp_comp F a b c))

end Coef

abbrev HdR (s : X ⟶ Sp k) (n : ℕ) : Type 1 := Hyp (OPt s) n

abbrev HdR.fil (s : X ⟶ Sp k) (p n : ℕ) : Submodule k (HdR s n) := Hyp.fil (OPt s) p n

section Pull

variable {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {s'' : X'' ⟶ Sp k''} {σ : k →+* k'} {τ : k' →+* k''}

end Pull

section Aff

variable (s : X ⟶ Sp k)

end Aff

section Fil

variable (s : X ⟶ Sp k)

theorem HdR.fil_succ (n : ℕ) : HdR.fil s (n + 1) n = ⊥ := Hyp.fil_eq_bot _ (Nat.lt_succ_self n)

end Fil

section Affine

variable (k) (B : Type) [CommRing B] [Algebra k B]

def idPt : AffPt (algStr k B) := ⟨CommAlgCat.of k B, 𝟙 _, Category.id_comp _⟩

variable {k B}

def toPt (T : AffPt (algStr k B)) : B →ₐ[k] T.B :=
  { (Spec.preimage T.x).hom with
    commutes' := fun r ↦ by
      have e : spMap (((Spec.preimage T.x).hom).comp (algebraMap k B)) = spMap (algebraMap k T.B) := by
        rw [spMap_comp', ← T.w]
        exact congrArg (· ≫ algStr k B) (Spec.map_preimage T.x)
      exact congrArg (fun g : k →+* T.B ↦ g r) (eq_of_spMap_eq e) }

theorem spMap_toPt (T : AffPt (algStr k B)) : spMap (toPt T : B →+* T.B) = T.x := Spec.map_preimage T.x

theorem toPt_comp ⦃T T' : AffPt (algStr k B)⦄ (φ : T ⟶ T') (b : B) :
    mp (OPt (algStr k B)) φ (toPt T b) = toPt T' b := by
  have e : spMap (((φ.1.hom : T.B →+* T'.B)).comp (toPt T : B →+* T.B)) = spMap (toPt T' : B →+* T'.B) := by
    rw [spMap_comp', spMap_toPt, spMap_toPt]; exact φ.2
  exact congrArg (fun g : B →+* T'.B ↦ g b) (eq_of_spMap_eq e)

def idPt_isInitial : Limits.IsInitial (idPt k B) :=
  Limits.IsInitial.ofUniqueHom (fun T ↦ ⟨CommAlgCat.ofHom (toPt T), (Category.comp_id _).trans (spMap_toPt T)⟩)
    fun T φ ↦ AffPt.hom_ext (CommAlgCat.hom_ext (AlgHom.toRingHom_injective (eq_of_spMap_eq
      (((Category.comp_id _).symm.trans φ.2).trans (spMap_toPt T).symm))))

theorem toPt_idPt (b : B) : toPt (idPt k B) b = b := by
  have e : spMap (toPt (idPt k B) : B →+* (idPt k B).B) = spMap (RingHom.id B) :=
    (spMap_toPt _).trans (spMap_id' B).symm
  exact congrArg (fun g : B →+* B ↦ g b) (@eq_of_spMap_eq B (idPt k B).B _ _ (toPt (idPt k B)) (RingHom.id B) e)

theorem toPt_idPt_bijective : Function.Bijective (toPt (idPt k B)) :=
  Function.bijective_iff_has_inverse.2 ⟨fun b ↦ b, fun b ↦ toPt_idPt b, fun b ↦ toPt_idPt b⟩

def HdR.ofForm (n : ℕ) : LinearMap.ker (dOm k B n) →ₗ[k] HdR (algStr k B) n :=
  coneCl (R := k) (B := B) (C := AffPt (algStr k B)) (F := OPt (algStr k B)) (fun T ↦ toPt T)
    (fun _ _ φ b ↦ toPt_comp φ b) n

theorem HdR.ofForm_mem_fil {n : ℕ} (ω : LinearMap.ker (dOm k B n)) :
    HdR.ofForm n ω ∈ HdR.fil (algStr k B) n n :=
  coneCl_mem_fil (R := k) (B := B) (C := AffPt (algStr k B)) (F := OPt (algStr k B)) (fun T ↦ toPt T)
    (fun _ _ φ b ↦ toPt_comp φ b) ω

theorem HdR.ofForm_eq_zero_iff {n : ℕ} (ω : LinearMap.ker (dOm k B (n + 1))) :
    HdR.ofForm (n + 1) ω = 0 ↔ ∃ η, dOm k B n η = ω.1 :=
  coneCl_eq_zero_iff (R := k) (B := B) (C := AffPt (algStr k B)) (F := OPt (algStr k B)) (fun T ↦ toPt T)
    (fun _ _ φ b ↦ toPt_comp φ b) (T₀ := idPt k B) toPt_idPt_bijective ω

def HdR.affZeroEquiv : LinearMap.ker (dOm k B 0) ≃ₗ[k] HdR (algStr k B) 0 :=
  LinearEquiv.ofBijective (HdR.ofForm 0) (coneCl_zero_bijective (R := k) (B := B) (C := AffPt (algStr k B)) (F := OPt (algStr k B))
    (fun T ↦ toPt T) (fun _ _ φ b ↦ toPt_comp φ b) (T₀ := idPt k B) toPt_idPt_bijective idPt_isInitial)


variable (k) in
theorem dOm_zero_self (x : Om k k 0) : dOm k k 0 x = 0 := by
  refine Subtype.ext ?_
  rw [coe_dOm, coe_eq_algebraMap_zeroEquiv x, dDR_algebraMap]
  have : D k k (exteriorPower.zeroEquiv k Ω[k⁄k] x) = 0 := by
    rw [← Algebra.algebraMap_self_apply (exteriorPower.zeroEquiv k Ω[k⁄k] x)]
    exact (D k k).map_algebraMap _
  rw [this, map_zero]; rfl


variable (k) in
def HdR.pointEquiv : k ≃ₗ[k] HdR (algStr k k) 0 :=
  (fn0 k).symm ≪≫ₗ (LinearEquiv.ofTop _ (eq_top_iff.2 fun x _ ↦ LinearMap.mem_ker.2 (dOm_zero_self k x))).symm ≪≫ₗ
    HdR.affZeroEquiv


open Polynomial in
variable (k) in
def tdtForm : LinearMap.ker (dOm k k[X] 1) :=
  ⟨⟨ι1 ((Polynomial.X : k[X]) • D k k[X] Polynomial.X), ι_mem _⟩, by
    rw [LinearMap.mem_ker, ← dOne_eq_dOm, dOne_line]⟩


open Polynomial in
theorem HdR.ofForm_tdt_ne_zero [Nontrivial k] (h2 : (2 : k) = 0) : HdR.ofForm 1 (tdtForm k) ≠ 0 := by
  rw [Ne, HdR.ofForm_eq_zero_iff]
  rintro ⟨η, hη⟩
  have e1 := congrArg Subtype.val hη
  rw [coe_dOm, coe_eq_algebraMap_zeroEquiv η, dDR_algebraMap] at e1
  have e2 := ExteriorAlgebra.ι_inj k[X] _ _ |>.1 e1
  have f3 := congrArg (polynomialEquiv k) e2
  simp only [map_smul, polynomialEquiv_D, derivative_X, smul_eq_mul, mul_one] at f3
  have hc := congrArg (fun p : k[X] ↦ p.coeff 1) f3
  simp only [coeff_derivative, coeff_X_one] at hc
  rw [show ((1 : ℕ) : k) + 1 = 2 by norm_num, h2, mul_zero] at hc
  exact zero_ne_one hc

end Affine

end GlobalTheory.HodgeCoh
