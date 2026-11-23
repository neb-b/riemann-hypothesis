module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberPointOfVectorField
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.EpsPoint

variable {S : Type} [CommRing S]

abbrev proj (S : Type) [CommRing S] : Sp (DualNumber S) ⟶ Sp S := spMap (algebraMap S (DualNumber S))

def epsOn (V : (Sp (DualNumber S)).Opens) : Γ(Sp (DualNumber S), V) :=
  ((Sp (DualNumber S)).presheaf.map (homOfLE le_top).op).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps)

theorem epsOn_mul_self (V : (Sp (DualNumber S)).Opens) : epsOn V * epsOn V = 0 := by
  rw [epsOn, ← map_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero, map_zero]

theorem epsOn_res {V V' : (Sp (DualNumber S)).Opens} (h : V' ≤ V) :
    ((Sp (DualNumber S)).presheaf.map (homOfLE h).op).hom (epsOn V) = epsOn V' := by
  rw [epsOn, epsOn, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable {Z : Scheme.{0}} {W : Z.Opens} {e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}

theorem field_one (he : IsField W e) {V : Z.Opens} (hV : V ≤ W) : e V 1 = 0 := by
  have h := he.2.1 V hV 1 1
  simp only [mul_one, one_mul] at h
  linear_combination -h

theorem field_zero (he : IsField W e) {V : Z.Opens} (hV : V ≤ W) : e V 0 = 0 := by
  have h := he.1 V hV 0 0
  simp only [add_zero] at h
  linear_combination -h

variable (g₀ : Sp S ⟶ Z) (hg : ⊤ ≤ g₀ ⁻¹ᵁ W)

include hg in
theorem le_inf_preimage (U : Z.Opens) : (proj S ≫ g₀) ⁻¹ᵁ U ≤ (proj S ≫ g₀) ⁻¹ᵁ (U ⊓ W) :=
  fun _ hx => TopologicalSpace.Opens.mem_inf.2 ⟨hx, hg trivial⟩

theorem appLE_res (U : Z.Opens) (f : Γ(Z, U)) :
    ((proj S ≫ g₀).appLE (U ⊓ W) _ (le_inf_preimage g₀ hg U)).hom (resG Z inf_le_left f) =
      ((proj S ≫ g₀).app U).hom f := by
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE]

def psi (he : IsField W e) (U : Z.Opens) : Γ(Z, U) →+* Γ(Sp (DualNumber S), (proj S ≫ g₀) ⁻¹ᵁ U) where
  toFun f := ((proj S ≫ g₀).app U).hom f + epsOn _ *
    ((proj S ≫ g₀).appLE (U ⊓ W) _ (le_inf_preimage g₀ hg U)).hom (e (U ⊓ W) (resG Z inf_le_left f))
  map_one' := by simp only [map_one, field_one he inf_le_right, map_zero, mul_zero, add_zero]
  map_mul' f f' := by
    simp only [map_mul, he.2.1 _ inf_le_right, map_add (f := _), appLE_res g₀ hg]
    linear_combination -(((proj S ≫ g₀).appLE (U ⊓ W) _ (le_inf_preimage g₀ hg U)).hom
      (e (U ⊓ W) (resG Z inf_le_left f)) * ((proj S ≫ g₀).appLE (U ⊓ W) _ (le_inf_preimage g₀ hg U)).hom
      (e (U ⊓ W) (resG Z inf_le_left f'))) * epsOn_mul_self (S := S) ((proj S ≫ g₀) ⁻¹ᵁ U)
  map_zero' := by simp only [map_zero, field_zero he inf_le_right, mul_zero, add_zero]
  map_add' f f' := by
    simp only [map_add (f := _), he.1 _ inf_le_right]
    ring

end GlobalTheory.EpsPoint

namespace GlobalTheory.EpsPoint
variable {S : Type} [CommRing S] {Z : Scheme.{0}} {W : Z.Opens} {e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
variable (g₀ : Sp S ⟶ Z) (hg : ⊤ ≤ g₀ ⁻¹ᵁ W)

theorem psi_res (he : IsField W e) {U U' : Z.Opens} (h : U' ≤ U) (f : Γ(Z, U)) :
    psi g₀ hg he U' (resG Z h f) =
      ((Sp (DualNumber S)).presheaf.map (homOfLE (fun _ hx => h hx : (proj S ≫ g₀) ⁻¹ᵁ U' ≤ (proj S ≫ g₀) ⁻¹ᵁ U)).op).hom
        (psi g₀ hg he U f) := by
  simp only [psi, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_add (f := _), map_mul, epsOn_res]
  congr 1
  · rw [resG, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  · congr 1
    have h2 : resG Z (inf_le_left : U' ⊓ W ≤ U') (resG Z h f) =
        resG Z (inf_le_inf_right W h) (resG Z (inf_le_left : U ⊓ W ≤ U) f) := by
      simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    rw [h2, he.2.2 _ _ _ inf_le_right, resG, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

end GlobalTheory.EpsPoint

namespace GlobalTheory.EpsPoint
variable {S : Type} [CommRing S] {Z : Scheme.{0}} {W : Z.Opens} {e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
variable (g₀ : Sp S ⟶ Z) (hg : ⊤ ≤ g₀ ⁻¹ᵁ W)

def cMap (he : IsField W e) : Z.presheaf ⟶ (proj S ≫ g₀).base _* (Sp (DualNumber S)).presheaf where
  app U := CommRingCat.ofHom (R := Γ(Z, U.unop)) (S := Γ(Sp (DualNumber S), (proj S ≫ g₀) ⁻¹ᵁ U.unop))
    (psi g₀ hg he U.unop)
  naturality U U' i := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro f
    exact psi_res g₀ hg he i.unop.le f

def pshHom (he : IsField W e) : (Sp (DualNumber S)).toPresheafedSpace.Hom Z.toPresheafedSpace :=
  ⟨(proj S ≫ g₀).base, cMap g₀ hg he⟩

theorem isLocal (he : IsField W e) (y : Sp (DualNumber S)) :
    IsLocalHom ((pshHom g₀ hg he).stalkMap y).hom := by
  constructor
  intro a ha
  obtain ⟨U, hU, f, rfl⟩ := TopCat.Presheaf.germ_exist _ a
  rw [PresheafedSpace.stalkMap_germ_apply] at ha
  change IsUnit ((Sp (DualNumber S)).presheaf.germ _ y hU (((proj S ≫ g₀).app U).hom f + epsOn _ *
    ((proj S ≫ g₀).appLE (U ⊓ W) _ (le_inf_preimage g₀ hg U)).hom (e (U ⊓ W) (resG Z inf_le_left f)))) at ha
  rw [map_add (f := _)] at ha
  have hn : IsNilpotent ((Sp (DualNumber S)).presheaf.germ _ y hU (epsOn _ *
      ((proj S ≫ g₀).appLE (U ⊓ W) _ (le_inf_preimage g₀ hg U)).hom (e (U ⊓ W) (resG Z inf_le_left f)))) := by
    refine ⟨2, ?_⟩
    rw [← map_pow, mul_pow, pow_two (epsOn _), epsOn_mul_self, zero_mul, map_zero]
  have h2 := hn.neg.isUnit_add_right_of_commute ha (Commute.all _ _)
  rw [add_comm, add_neg_cancel_right] at h2
  exact (isUnit_map_iff ((proj S ≫ g₀).stalkMap y).hom _).mp
    ((congrArg IsUnit (Scheme.Hom.germ_stalkMap_apply (proj S ≫ g₀) U y hU f)).mpr h2)

def epsPoint (he : IsField W e) : Sp (DualNumber S) ⟶ Z :=
  ⟨⟨pshHom g₀ hg he, isLocal g₀ hg he⟩⟩

theorem epsPoint_base (he : IsField W e) : (epsPoint g₀ hg he).base = (proj S ≫ g₀).base := rfl

end GlobalTheory.EpsPoint

namespace GlobalTheory.EpsPoint
variable {S : Type} [CommRing S] {Z : Scheme.{0}} {W : Z.Opens} {e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
variable (g₀ : Sp S ⟶ Z) (hg : ⊤ ≤ g₀ ⁻¹ᵁ W)

theorem fst_comp_proj : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ proj S = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [this, CommRingCat.ofHom_id, Spec.map_id]

theorem fst_app_epsOn (V : (Sp (DualNumber S)).Opens) :
    ((spMap (TrivSqZeroExt.fstHom S S S).toRingHom).app V).hom (epsOn V) = 0 := by
  rw [epsOn, ← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  have : ((spMap (TrivSqZeroExt.fstHom S S S).toRingHom).app ⊤).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).inv.hom DualNumber.eps) = 0 := by
    have h1 := congrArg (fun q => q.hom DualNumber.eps)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom S S S).toRingHom))
    have h2 : (CommRingCat.ofHom (TrivSqZeroExt.fstHom S S S).toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv).hom DualNumber.eps = 0 := by
      show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom ((TrivSqZeroExt.fstHom S S S).toRingHom DualNumber.eps) = 0
      have h3 : (TrivSqZeroExt.fstHom S S S).toRingHom DualNumber.eps = 0 := by simp
      rw [h3, map_zero]
    exact h1.symm.trans h2
  rw [this, map_zero]

theorem comp_eq_of_app {X T Y : Scheme.{0}} (i : X ⟶ T) (w q : T ⟶ Y) (hb : w.base = q.base)
    (h : ∀ U : Y.Opens, w.app U ≫ i.app (w ⁻¹ᵁ U) = q.app U ≫ i.app (q ⁻¹ᵁ U) ≫
      X.presheaf.map (eqToHom (by rw [hb]) : i ⁻¹ᵁ (w ⁻¹ᵁ U) ⟶ i ⁻¹ᵁ (q ⁻¹ᵁ U)).op) : i ≫ w = i ≫ q := by
  refine Scheme.Hom.ext (by rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, hb]) fun U => ?_
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app, h U]
  erw [Category.assoc, Category.assoc, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

theorem fst_app_psi (he : IsField W e) (U : Z.Opens) (a : Γ(Z, U)) :
    ((spMap (TrivSqZeroExt.fstHom S S S).toRingHom).app ((proj S ≫ g₀) ⁻¹ᵁ U)).hom (psi g₀ hg he U a) =
      ((spMap (TrivSqZeroExt.fstHom S S S).toRingHom).app ((proj S ≫ g₀) ⁻¹ᵁ U)).hom (((proj S ≫ g₀).app U).hom a) := by
  simp only [psi, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_add (f := _), map_mul, fst_app_epsOn, zero_mul,
    add_zero]

theorem fst_comp (he : IsField W e) : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ epsPoint g₀ hg he = g₀ := by
  have hb : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ proj S ≫ g₀ = g₀ := by
    rw [← Category.assoc, fst_comp_proj, Category.id_comp]
  refine Eq.trans (comp_eq_of_app _ _ (proj S ≫ g₀) (epsPoint_base g₀ hg he) fun U => ?_) hb
  erw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact fst_app_psi g₀ hg he U a

end GlobalTheory.EpsPoint

namespace GlobalTheory.EpsPoint
variable {S : Type} [CommRing S] {Z : Scheme.{0}} {W : Z.Opens} {e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
variable (g₀ : Sp S ⟶ Z) (hg : ⊤ ≤ g₀ ⁻¹ᵁ W)

theorem valR_comp_epsPoint (he : IsField W e) {C : Type} [CommRing C] (x : Sp C ⟶ Sp (DualNumber S))
    (O : Z.Opens) (f : Γ(Z, O)) :
    valR (x ≫ epsPoint g₀ hg he) O f = valR x ((proj S ≫ g₀) ⁻¹ᵁ O) (psi g₀ hg he O f) := by
  rw [GlobalTheory.Points.valR_comp]
  rfl

theorem snd_valR (he : IsField W e) {S' : Type} [CommRing S'] (ρ : S →+* S') (O : Z.Opens) (hO : O ≤ W)
    (hρ : ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O) (f : Γ(Z, O)) :
    (valR (spMap (dualMap ρ) ≫ epsPoint g₀ hg he) O f).snd = valR (spMap ρ ≫ g₀) O (e O f) := by
  have hxπ : spMap (dualMap ρ) ≫ proj S = proj S' ≫ spMap ρ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hy : spMap (dualMap ρ) ≫ proj S ≫ g₀ = proj S' ≫ spMap ρ ≫ g₀ := by
    rw [← Category.assoc, hxπ, Category.assoc]
  have hyO : ⊤ ≤ (spMap (dualMap ρ) ≫ proj S ≫ g₀) ⁻¹ᵁ O := by
    rw [hy]
    exact GlobalTheory.Points.le_preimage_comp _ _ hρ (GlobalTheory.Points.le_preimage_top _)
  have hyW : ⊤ ≤ (spMap (dualMap ρ) ≫ proj S ≫ g₀) ⁻¹ᵁ W := by
    rw [← Category.assoc]
    exact GlobalTheory.Points.le_preimage_comp _ _ hg (GlobalTheory.Points.le_preimage_top _)
  have hyOW : ⊤ ≤ (spMap (dualMap ρ) ≫ proj S ≫ g₀) ⁻¹ᵁ (O ⊓ W) :=
    fun z hz => TopologicalSpace.Opens.mem_inf.2 ⟨hyO hz, hyW hz⟩
  have hx : ⊤ ≤ spMap (dualMap ρ) ⁻¹ᵁ ((proj S ≫ g₀) ⁻¹ᵁ O) := hyO
  rw [valR_comp_epsPoint]
  simp only [psi, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [GlobalTheory.Points.valR_add _ _ hx, GlobalTheory.Points.valR_mul _ _ hx, ← GlobalTheory.Points.valR_comp,
    GlobalTheory.Points.valR_appLE _ _ _ hx, he.2.2 O (O ⊓ W) inf_le_left hO f,
    GlobalTheory.Points.valR_res _ _ hyOW, epsOn, GlobalTheory.Points.valR_res _ _ hx, GlobalTheory.Points.valR_specMap, hy,
    GlobalTheory.Points.valR_spMap_comp _ _ _ hρ, GlobalTheory.Points.valR_spMap_comp _ _ _ hρ]
  simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_epsPoint : ∀ (Z : Scheme.{0}) (W : Z.Opens) (e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W e →
    ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ Z), ⊤ ≤ g₀ ⁻¹ᵁ W → ∃ w : Sp (DualNumber S) ⟶ Z,
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ ∧
        ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (O : Z.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O →
          ∀ f : Γ(Z, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = valR (spMap ρ ≫ g₀) O (e O f) := by
  intro Z W e he S _ g₀ hg
  exact ⟨epsPoint g₀ hg he, fst_comp g₀ hg he, fun S' _ ρ O hO hρ f => snd_valR g₀ hg he ρ O hO hρ f⟩

end GlobalTheory.EpsPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointAbelianVarietyThroughFormalPoi
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifGenPoint

theorem valR_constFn {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (p : X ⟶ Sp B) (x : Sp A ⟶ X)
    (χ : B →+* A) (hx : x ≫ p = spMap χ) (a : B) : valR x ⊤ (constFn p ⊤ a) = χ a := by
  have h : ⊤ ≤ x ⁻¹ᵁ (⊤ : X.Opens) := fun _ _ => trivial
  unfold constFn
  refine (GlobalTheory.ZH.CrdMove.valR_appLE x p ⊤ ⊤ _ h _).trans ?_
  rw [hx]
  have h' : ⊤ ≤ (spMap χ) ⁻¹ᵁ (⊤ : (Sp B).Opens) := fun _ _ => trivial
  rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ h']
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ)
  have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a)) n
  refine Eq.trans ?_ (this.trans (congrArg χ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv_hom_id_apply a)))
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

end GlobalTheory.UnifGenPoint


open GlobalTheory.UnifGenPoint in
theorem GlobalTheory.UnifGenPoint.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) ∧ ξ ≫ P.A.A.hom = spMap ψ ∧ ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' ∧ ∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0 := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ n v' D Ω _ _ _ φ x' δ dd' _ hx _ _ _ hinj g _ δL _

  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun r hr => ?_
    have h1 : valR x' ⊤ (constFn t.G.hom ⊤ r) = 0 := (valR_constFn t.G.hom x' φ hx r).trans hr
    have h2 := hinj ⊤ (constFn t.G.hom ⊤ r) (fun _ _ => trivial) h1
    have h3 := valR_constFn t.G.hom (eSec t.G) (RingHom.id R) (by
      rw [eSec, Over.w]; simp [spMap]) r
    rw [h2, GlobalTheory.ZH.CrdCalc.valR_eq (eSec t.G) ⊤ (fun _ _ => trivial), map_zero] at h3
    exact h3.symm

  set L := FractionRing Ω
  have hinjL : Function.Injective ((algebraMap Ω L).comp φ) :=
    (IsFractionRing.injective Ω L).comp hφ
  let ψ : FractionRing R →+* L := IsFractionRing.lift (K := FractionRing R) hinjL
  have hψ : ∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω L (φ r) := fun r => by
    simp [ψ, IsFractionRing.lift_algebraMap]
  let u : Sp L ⟶ t.G.left := spMap (algebraMap Ω L) ≫ x'
  have hu : u ≫ t.G.hom = spMap ψ ≫ jK R := by
    simp only [u, Category.assoc, hx, spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => (hψ r).symm
  let ξ₀ : Sp L ⟶ pullback t.G.hom (jK R) := pullback.lift u (spMap ψ) hu
  let ξ : Sp L ⟶ P.A.A.left := ξ₀ ≫ P.U.gen.hom.left
  have n₁ : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, P.U.gen.hom_inv_id, Over.id_left]
  have hξ1 : ξ ≫ P.A.A.hom = spMap ψ := by
    simp only [ξ, Category.assoc, Over.w]
    exact pullback.lift_snd _ _ _
  have hξ2 : ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = u := by
    simp only [ξ, Category.assoc]
    rw [← Category.assoc P.U.gen.hom.left, n₁, Category.id_comp]
    exact pullback.lift_fst _ _ _
  refine ⟨ψ, ξ, hψ, hξ1, hξ2, ?_⟩

  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : GeometricallyConnected t.G.hom := t.semi.geomConnected
  haveI : IrreducibleSpace t.G.left :=
    GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain R t.G inferInstance inferInstance
      ⟨x' (IsLocalRing.closedPoint Ω)⟩
  set q := u (IsLocalRing.closedPoint L) with hq
  have hqg : q = genericPoint t.G.left := by
    have h1 : q ⤳ genericPoint t.G.left := by
      refine specializes_iff_forall_open.2 fun s hs hgs => ?_
      obtain ⟨V, hVa, hpV, -⟩ := exists_isAffineOpen_mem_and_subset
        (U := ⊤) (x := x' (IsLocalRing.closedPoint Ω)) trivial
      have hV : ⊤ ≤ x' ⁻¹ᵁ V := (GlobalTheory.ZH.CrdCalc.top_le_iff x' V).2 hpV
      have hgV : genericPoint t.G.left ∈ V :=
        ((genericPoint_spec t.G.left).mem_open_set_iff V.isOpen).2 ⟨_, trivial, hpV⟩
      let W : t.G.left.Opens := V ⊓ ⟨s, hs⟩
      obtain ⟨b, hbW, hgb⟩ := hVa.exists_basicOpen_le (V := W) ⟨genericPoint t.G.left, hgV, hgs⟩ hgV
      have hb : b ≠ 0 := by
        rintro rfl
        rw [Scheme.basicOpen_zero] at hgb
        exact hgb
      have hv : valR x' V b ≠ 0 := fun h => hb (hinj V b hV h)
      obtain ⟨hV', hval⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap Ω L) x' V hV
      have hu : IsUnit (valR u V b) := by
        rw [hval]
        exact (Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective Ω L)).2 hv))
      have := ((GlobalTheory.ZH.CrdCalc.isUnit_valR_iff u V hV' b).1 hu) (Set.mem_univ (IsLocalRing.closedPoint L))
      exact (hbW this).2
    exact (h1.antisymm (genericPoint_specializes q)).eq

  haveI : Smooth P.A.A.hom := P.A.isAb.smooth
  haveI : GeometricallyConnected P.A.A.hom := P.A.isAb.geomConnected
  haveI : IrreducibleSpace P.A.A.left :=
    GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain (FractionRing R) P.A.A inferInstance
      inferInstance ⟨ξ (IsLocalRing.closedPoint L)⟩
  haveI : IsIntegral P.A.A.left := GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace P.A.A.hom
  set y := ξ (IsLocalRing.closedPoint L) with hy
  let mm : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)
  haveI : IsIso P.U.gen.inv.left := ⟨⟨P.U.gen.hom.left, by
    rw [← Over.comp_left, P.U.gen.inv_hom_id, Over.id_left], n₁⟩⟩
  haveI : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  haveI : IsPreimmersion (pullback.fst t.G.hom (jK R)) := MorphismProperty.of_isPullback (IsPullback.of_hasPullback t.G.hom (jK R)).flip inferInstance
  haveI : IsPreimmersion mm := inferInstance
  have hmy : mm y = q := by
    rw [hq, ← hξ2]
    rfl
  have hyg : y = genericPoint P.A.A.left := by
    apply (Scheme.Hom.isEmbedding mm).injective
    have h1 : mm (genericPoint P.A.A.left) ⤳ mm y :=
      (genericPoint_specializes y).map (Scheme.Hom.continuous mm)
    rw [hmy, hqg] at h1 ⊢
    exact ((genericPoint_specializes _).antisymm h1).eq
  intro O f hO hf
  by_contra hne
  have hne' : P.A.A.left.basicOpen f ≠ ⊥ := fun h => hne ((basicOpen_eq_bot_iff f).1 h)
  have hgen : genericPoint P.A.A.left ∈ P.A.A.left.basicOpen f := by
    refine ((genericPoint_spec P.A.A.left).mem_open_set_iff (P.A.A.left.basicOpen f).isOpen).2 ?_
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne'
    exact ⟨z, trivial, hz⟩
  have hu : IsUnit (valR ξ O f) :=
    (GlobalTheory.ZH.CrdCalc.isUnit_valR_iff ξ O hO f).2
      ((GlobalTheory.ZH.CrdCalc.top_le_iff ξ _).2 (by rw [← hy, hyg]; exact hgen))
  exact hu.ne_zero hf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedLineBundleSectionCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)

namespace GlobalTheory.GlueOver

open GlobalTheory.KS

variable {X : Scheme.{0}}

theorem rsT_cocycle {M : LB X} (hM : M.IsLB) (a b c : M.ι) {O : X.Opens} (h : O ≤ M.U a ⊓ M.U b ⊓ M.U c) :
    rsT (M.g a b).val O * rsT (M.g b c).val O = rsT (M.g a c).val O := by
  have e := congrArg (fun u => rsT u.val O) (hM.cocycle a b c)
  simp only [Units.val_mul, GlobalTheory.KS.AdjDlog.val_res, rsT_mul] at e
  rwa [rsT_rsT inf_le_left h, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h,
    rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h] at e

theorem rsT_g_self {M : LB X} (hM : M.IsLB) (a : M.ι) {O : X.Opens} (h : O ≤ M.U a) :
    rsT (M.g a a).val O = 1 := by
  have h2 : O ≤ M.U a ⊓ M.U a := le_inf h h
  have e := rsT_cocycle hM a a a (le_inf h2 h)
  have hu : IsUnit (rsT (M.g a a).val O) := by
    rw [rsT_of_le h2]
    exact (M.g a a).isUnit.map _
  exact hu.mul_left_cancel (e.trans (_root_.mul_one _).symm)

theorem exists_glue : ∀ {X : Scheme.{0}} (M : LB X), M.IsLB → ∀ (V : X.Opens) {J : Type} (W : J → X.Opens)
    (j : J → M.ι) (F : ∀ i, Γ(X, W i)), ⨆ i, W i = V → (∀ i, W i ≤ M.U (j i)) →
    (∀ i i', rsT (F i) (W i ⊓ W i') = rsT (M.g (j i) (j i')).val (W i ⊓ W i') * rsT (F i') (W i ⊓ W i')) →
    ∃ t : ∀ c, Γ(X, M.U c ⊓ V),
      (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ V) =
        rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ V) * rsT (t c') (M.U c ⊓ M.U c' ⊓ V)) ∧
      ∀ i, rsT (t (j i)) (W i) = F i := by
  intro X M hM V J W j F hV hW Fc
  have hWV : ∀ i, W i ≤ V := fun i => hV ▸ le_iSup W i
  have cov : ∀ O : X.Opens, O ⊓ V ≤ ⨆ i, O ⊓ W i := by
    intro O y hy
    have : y ∈ ⨆ i, W i := by rw [hV]; exact hy.2
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy.1, hi⟩
  have hU : ∀ c i, M.U c ⊓ W i ≤ M.U c ⊓ M.U (j i) := fun c i => inf_le_inf le_rfl (hW i)
  have hUV : ∀ (O : X.Opens) i, O ⊓ W i ≤ O ⊓ V := fun O i => inf_le_inf le_rfl (hWV i)
  have glue : ∀ c : M.ι, ∃ t : Γ(X, M.U c ⊓ V), ∀ i,
      rsT t (M.U c ⊓ W i) = rsT (M.g c (j i)).val (M.U c ⊓ W i) * rsT (F i) (M.U c ⊓ W i) := by
    intro c
    refine exists_rsT_eq (fun i => M.U c ⊓ W i) (fun i => hUV _ i) (cov _) _ fun i i' => ?_
    have hN1 : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ M.U c ⊓ W i := inf_le_left
    have hN2 : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ M.U c ⊓ W i' := inf_le_right
    have hNW : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ W i ⊓ W i' := fun y hy => ⟨hy.1.2, hy.2.2⟩
    have h3 : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ M.U c ⊓ M.U (j i) ⊓ M.U (j i') :=
      fun y hy => ⟨⟨hy.1.1, hW i hy.1.2⟩, hW i' hy.2.2⟩
    rw [rsT_mul, rsT_mul, rsT_rsT (hU c i) hN1, rsT_rsT (hU c i') hN2,
      rsT_rsT inf_le_right hN1, rsT_rsT inf_le_right hN2, ← rsT_rsT inf_le_left hNW (F i), Fc, rsT_mul,
      rsT_rsT (inf_le_inf (hW i) (hW i')) hNW, rsT_rsT inf_le_right hNW,
      ← _root_.mul_assoc, rsT_cocycle hM _ _ _ h3]
  choose t ht using glue
  refine ⟨t, fun c c' => ?_, fun i => ?_⟩
  · refine eq_of_rsT_eq (fun i => M.U c ⊓ M.U c' ⊓ W i) (fun i => hUV _ i) (cov _) _ _ fun i => ?_
    have a1 : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c ⊓ W i := fun y hy => ⟨hy.1.1, hy.2⟩
    have a2 : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c' ⊓ W i := fun y hy => ⟨hy.1.2, hy.2⟩
    have h3 : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c ⊓ M.U c' ⊓ M.U (j i) := inf_le_inf le_rfl (hW i)
    have e' : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c ⊓ M.U c' ⊓ V := hUV _ i
    have eL : M.U c ⊓ M.U c' ⊓ V ≤ M.U c ⊓ V := fun y hy => ⟨hy.1.1, hy.2⟩
    have eR : M.U c ⊓ M.U c' ⊓ V ≤ M.U c' ⊓ V := fun y hy => ⟨hy.1.2, hy.2⟩
    rw [rsT_rsT eL e', rsT_mul, rsT_rsT eR e', rsT_rsT inf_le_left e',
      ← rsT_rsT (hUV _ i) a1 (t c), ← rsT_rsT (hUV _ i) a2 (t c'), ht, ht, rsT_mul, rsT_mul,
      rsT_rsT (hU c i) a1, rsT_rsT (hU c' i) a2, rsT_rsT inf_le_right a1,
      rsT_rsT inf_le_right a2, ← _root_.mul_assoc, rsT_cocycle hM _ _ _ h3]
  · have a : W i ≤ M.U (j i) ⊓ W i := le_inf (hW i) le_rfl
    rw [← rsT_rsT (hUV _ i) a, ht, rsT_mul, rsT_rsT (hU _ i) a, rsT_rsT inf_le_right a, rsT_self,
      rsT_g_self hM (j i) (hW i), _root_.one_mul]

end GlobalTheory.GlueOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialPeriodUnitPartGeneratorStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monomialPeriod_unitPart_generator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : DegPre R) (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → ∀ (χ : Q.X) (n : Fin m → ℕ), (∀ i, gam i χ χ = 2 * n i) → ∃ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) fun _ => -1), ψ₀.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi χ) r z J).val = cst (r ≫ jK R) z (∏ i, t i ^ n i) * (val ψ₀ (r ≫ jK R) z J).val := by
  first | exact @GlobalTheory.UnitPart.exists_psi_val_eq_monomial_mul | exact GlobalTheory.UnitPart.exists_psi_val_eq_monomial_mul | (intros; apply GlobalTheory.UnitPart.exists_psi_val_eq_monomial_mul <;> assumption)
end

