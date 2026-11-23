module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantApply
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GalSec

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

abbrev LCRing (k : ℕ) : Type := LocallyConstant (Fin k → (Ω ≃ₐ[K] Ω)) Ω

theorem isLocallyConstant_apply [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin k) (a : Ω) :
    IsLocallyConstant (fun g : Fin k → (Ω ≃ₐ[K] Ω) => g i a) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  have hfd : FiniteDimensional K (IntermediateField.adjoin K {a}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  have hopen : IsOpen {σ : Ω ≃ₐ[K] Ω | (g₀ i)⁻¹ * σ ∈ (IntermediateField.adjoin K {a}).fixingSubgroup} :=
    (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const.mul continuous_id)
  have hmem : ∀ᶠ g in nhds g₀, g i ∈ {σ : Ω ≃ₐ[K] Ω | (g₀ i)⁻¹ * σ ∈ (IntermediateField.adjoin K {a}).fixingSubgroup} :=
    ((continuous_apply i).tendsto g₀).eventually (hopen.mem_nhds (by simp [one_mem]))
  filter_upwards [hmem] with g hg
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg a (IntermediateField.mem_adjoin_simple_self K a)
  have h2 := congrArg (g₀ i) h1
  simpa [AlgEquiv.mul_apply] using h2

def coord [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin k) : Ω →+* LCRing K Ω k where
  toFun a := ⟨fun g => g i a, isLocallyConstant_apply K Ω k i a⟩
  map_one' := LocallyConstant.ext fun g => by simp
  map_mul' a b := LocallyConstant.ext fun g => by simp
  map_zero' := LocallyConstant.ext fun g => by simp
  map_add' a b := LocallyConstant.ext fun g => by simp

@[simp] theorem coord_apply [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin k) (a : Ω) (g : Fin k → (Ω ≃ₐ[K] Ω)) :
    coord K Ω k i a g = g i a := rfl

def legHom [Algebra.IsAlgebraic K Ω] (k : ℕ) : Fin (k + 1) → (Ω →+* LCRing K Ω k) :=
  Fin.cases LocallyConstant.constRingHom (coord K Ω k)

def baseHom (k : ℕ) : K →+* LCRing K Ω k := LocallyConstant.constRingHom.comp (algebraMap K Ω)

theorem legHom_comp [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin (k + 1)) :
    (legHom K Ω k i).comp (algebraMap K Ω) = baseHom K Ω k := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · ext c g
    simp [legHom, baseHom]

def tailG (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) : Fin k → (Ω ≃ₐ[K] Ω) := fun i => (σ 0)⁻¹ * σ i.succ

def ptHom (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) : LCRing K Ω k →+* Ω :=
  ((σ 0 : Ω ≃ₐ[K] Ω) : Ω →+* Ω).comp (LocallyConstant.evalRingHom (tailG K Ω k σ))

theorem ptHom_legHom [Algebra.IsAlgebraic K Ω] (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) (i : Fin (k + 1)) :
    (ptHom K Ω k σ).comp (legHom K Ω k i) = ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · ext a; simp [ptHom, legHom]
  · ext a; simp [ptHom, legHom, tailG, AlgEquiv.mul_apply]

end GlobalTheory.EtC.GalSec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafBiprod
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

def biprodPresheaf (P₁ P₂ : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (P₁.obj U × P₂.obj U)
  map f := ModuleCat.ofHom ((P₁.map f).hom.prodMap (P₂.map f).hom)
  map_id U := by ext x <;> simp
  map_comp f g := by ext x <;> simp

theorem secBiprod_total (M N : Shv R) (U : Scheme.{0}) (y : Sec (M ⊞ N) U) :
    y = Sec.map (biprod.inl : M ⟶ M ⊞ N) (Sec.map biprod.fst y) + Sec.map (biprod.inr : N ⟶ M ⊞ N) (Sec.map biprod.snd y) := by
  conv_lhs => rw [show y = (((𝟙 (M ⊞ N)) : M ⊞ N ⟶ M ⊞ N).hom.app (op U)).hom y from rfl, ← biprod.total]
  rfl

theorem secBiprod_inl_fst (M N : Shv R) {U : Scheme.{0}} (a : Sec M U) :
    Sec.map (biprod.fst : M ⊞ N ⟶ M) (Sec.map (biprod.inl : M ⟶ M ⊞ N) a) = a := by
  change ((biprod.inl ≫ biprod.fst : M ⟶ M).hom.app (op U)).hom a = a
  rw [biprod.inl_fst]; rfl

theorem secBiprod_inr_fst (M N : Shv R) {U : Scheme.{0}} (b : Sec N U) :
    Sec.map (biprod.fst : M ⊞ N ⟶ M) (Sec.map (biprod.inr : N ⟶ M ⊞ N) b) = 0 := by
  change ((biprod.inr ≫ biprod.fst : N ⟶ M).hom.app (op U)).hom b = 0
  rw [biprod.inr_fst]; rfl

theorem secBiprod_inl_snd (M N : Shv R) {U : Scheme.{0}} (a : Sec M U) :
    Sec.map (biprod.snd : M ⊞ N ⟶ N) (Sec.map (biprod.inl : M ⟶ M ⊞ N) a) = 0 := by
  change ((biprod.inl ≫ biprod.snd : M ⟶ N).hom.app (op U)).hom a = 0
  rw [biprod.inl_snd]; rfl

theorem secBiprod_inr_snd (M N : Shv R) {U : Scheme.{0}} (b : Sec N U) :
    Sec.map (biprod.snd : M ⊞ N ⟶ N) (Sec.map (biprod.inr : N ⟶ M ⊞ N) b) = b := by
  change ((biprod.inr ≫ biprod.snd : N ⟶ N).hom.app (op U)).hom b = b
  rw [biprod.inr_snd]; rfl

noncomputable section

def biprodPresheafMap {M N : Shv R} {P₁ P₂ : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (φ₁ : P₁ ⟶ M.obj) (φ₂ : P₂ ⟶ N.obj) :
    biprodPresheaf P₁ P₂ ⟶ (M ⊞ N).obj where
  app U := ModuleCat.ofHom (LinearMap.coprod (((biprod.inl : M ⟶ M ⊞ N).hom.app U).hom ∘ₗ (φ₁.app U).hom)
    (((biprod.inr : N ⟶ M ⊞ N).hom.app U).hom ∘ₗ (φ₂.app U).hom))
  naturality U V f := by
    ext ⟨a, b⟩
    have h1 := congrArg (fun g => ModuleCat.Hom.hom g a) (φ₁.naturality f)
    have h2 := congrArg (fun g => ModuleCat.Hom.hom g b) (φ₂.naturality f)
    have h3 := congrArg (fun g => ModuleCat.Hom.hom g ((φ₁.app U).hom a)) ((biprod.inl : M ⟶ M ⊞ N).hom.naturality f)
    have h4 := congrArg (fun g => ModuleCat.Hom.hom g ((φ₂.app U).hom b)) ((biprod.inr : N ⟶ M ⊞ N).hom.naturality f)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1 h2 h3 h4
    change (((biprod.inl : M ⟶ M ⊞ N).hom).app V).hom ((φ₁.app V).hom ((P₁.map f).hom a)) +
        (((biprod.inr : N ⟶ M ⊞ N).hom).app V).hom ((φ₂.app V).hom ((P₂.map f).hom b)) =
      ((M ⊞ N).obj.map f).hom ((((biprod.inl : M ⟶ M ⊞ N).hom).app U).hom ((φ₁.app U).hom a) +
        (((biprod.inr : N ⟶ M ⊞ N).hom).app U).hom ((φ₂.app U).hom b))
    rw [map_add (f := _), h1, h2, h3, h4]

theorem secRes_secMap {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have h := congrArg (fun h => ModuleCat.Hom.hom h a) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  exact h.symm

theorem flatS_biprod : ∀ (R : Type) [CommRing R] (M N : Shv R), FlatS M → FlatS N → FlatS (M ⊞ N) := by
  intro R _ M N ⟨P₁, φ₁, s₁, i₁, f₁⟩ ⟨P₂, φ₂, s₂, i₂, f₂⟩
  refine ⟨biprodPresheaf P₁ P₂, biprodPresheafMap φ₁ φ₂, ?_, ?_, ?_⟩
  · intro U y
    obtain ⟨S, hS, hS'⟩ := s₁ U (Sec.map biprod.fst y)
    obtain ⟨T, hT, hT'⟩ := s₂ U (Sec.map biprod.snd y)
    refine ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩
    obtain ⟨x₁, hx₁⟩ := hS' V g hg.1
    obtain ⟨x₂, hx₂⟩ := hT' V g hg.2
    refine ⟨(x₁, x₂), ?_⟩
    change Sec.map (biprod.inl : M ⟶ M ⊞ N) ((φ₁.app (op V)).hom x₁) +
      Sec.map (biprod.inr : N ⟶ M ⊞ N) ((φ₂.app (op V)).hom x₂) = Sec.res g y
    rw [hx₁, hx₂, ← secRes_secMap, ← secRes_secMap, ← map_add (f := _)]
    exact congrArg (Sec.res g) (secBiprod_total M N U y).symm
  · rintro U ⟨a, b⟩ hx
    change Sec.map (biprod.inl : M ⟶ M ⊞ N) ((φ₁.app (op U)).hom a) +
      Sec.map (biprod.inr : N ⟶ M ⊞ N) ((φ₂.app (op U)).hom b) = 0 at hx
    have ha : (φ₁.app (op U)).hom a = 0 := by
      have e : ∀ x y : Sec (M ⊞ N) U, Sec.map (biprod.fst : M ⊞ N ⟶ M) (x + y) =
          Sec.map biprod.fst x + Sec.map biprod.fst y := fun x y => map_add _ x y
      have z : Sec.map (biprod.fst : M ⊞ N ⟶ M) (0 : Sec (M ⊞ N) U) = 0 := map_zero _
      have h := congrArg (Sec.map (biprod.fst : M ⊞ N ⟶ M)) hx
      rwa [e, secBiprod_inl_fst, secBiprod_inr_fst, add_zero, z] at h
    have hb : (φ₂.app (op U)).hom b = 0 := by
      have e : ∀ x y : Sec (M ⊞ N) U, Sec.map (biprod.snd : M ⊞ N ⟶ N) (x + y) =
          Sec.map biprod.snd x + Sec.map biprod.snd y := fun x y => map_add _ x y
      have z : Sec.map (biprod.snd : M ⊞ N ⟶ N) (0 : Sec (M ⊞ N) U) = 0 := map_zero _
      have h := congrArg (Sec.map (biprod.snd : M ⊞ N ⟶ N)) hx
      rwa [e, secBiprod_inl_snd, secBiprod_inr_snd, zero_add, z] at h
    obtain ⟨S, hS, hS'⟩ := i₁ U a ha
    obtain ⟨T, hT, hT'⟩ := i₂ U b hb
    refine ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ?_⟩
    change ((P₁.map g.op).hom a, (P₂.map g.op).hom b) = 0
    rw [hS' V g hg.1, hT' V g hg.2]
    rfl
  · intro U hU
    haveI := f₁ U hU
    haveI := f₂ U hU
    exact GlobalTheory.flat_prod (R := ULift.{1} R) (A := P₁.obj (op U)) (B := P₂.obj (op U))

end

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFlatEtaleSheafIsoAndZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem flatS_iso_and_zero : ∀ (R : Type) [CommRing R], (∀ {M N : Shv R}, (M ≅ N) → FlatS M → FlatS N) ∧ ∀ M : Shv R, IsZero M → FlatS M := by
  intro R _
  refine ⟨?_, ?_⟩
  · intro M N e ⟨P, φ, hs, hi, hf⟩
    refine ⟨P, φ ≫ e.hom.hom, ?_, ?_, hf⟩
    · intro U y
      obtain ⟨S, hS, hy⟩ := hs U (Sec.map e.inv y)
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨x, hx⟩ := hy V g hg
      refine ⟨x, ?_⟩
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [hx]
      have h1 := congrArg ModuleCat.Hom.hom (e.hom.hom.naturality g.op)
      have h2 := congrArg (fun (f : N ⟶ N) => (f.hom.app (op U)).hom y) e.inv_hom_id
      simp only [ModuleCat.hom_comp] at h1
      have h3 := LinearMap.congr_fun h1 ((e.inv.hom.app (op U)).hom y)
      simp only [LinearMap.comp_apply] at h3
      simp only [Sec.res, Sec.map]
      rw [h3]
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] at h2
      rw [h2]
    · intro U x hx
      apply hi U x
      have h2 := congrArg (fun (f : M ⟶ M) => (f.hom.app (op U)).hom ((φ.app (op U)).hom x)) e.hom_inv_id
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] at h2
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at hx
      rw [← h2, hx, map_zero]
  · intro M hM
    refine ⟨(Functor.const _).obj (ModuleCat.of (ULift.{1} R) PUnit.{2}), 0, ?_, ?_, ?_⟩
    · intro U y
      refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨0, ?_⟩⟩
      have h := congrArg (fun (f : M ⟶ M) => (f.hom.app (op V)).hom (Sec.res g y)) (hM.eq_of_src (𝟙 M) 0)
      simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] at h
      rw [h]
      simp
    · intro U x _
      exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ => Subsingleton.elim (α := PUnit.{2}) _ _⟩
    · intro U _
      show Module.Flat (ULift.{1} R) PUnit.{2}
      infer_instance

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackLv
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.BcLevel

set_option synthInstance.maxHeartbeats 200000 in
def bcIsoOfIso {E E' : Spc} {S : Scheme.{0}} (α : E ≅ E') (p : E' ⟶ sch.obj S) : bc (α.hom ≫ p) ≅ bc p :=
  haveI : ∀ U, IsIso ((bcMap α.hom p).app U) := fun U => by
    dsimp only [bcMap]; exact pullback.map_isIso _ _ _ _ _ _ _ _ _
  haveI : IsIso (bcMap α.hom p) := NatIso.isIso_of_isIso_app _
  asIso (bcMap α.hom p)

def dq {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) : disc.obj (E.obj k) ⟶ sch.obj S :=
  disc.map (p.app k)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.BcLevel.isPullback_lv {E : _root_.GlobalTheory.EtC.Spc} {S : Scheme.{0}}
    (p : E ⟶ _root_.GlobalTheory.EtC.sch.obj S) (k : SimplexCategoryᵒᵖ) (U : Over S) :
    IsPullback (_root_.GlobalTheory.EtC.disc.map ((pullback.fst p (_root_.GlobalTheory.EtC.sch.map U.hom)).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.disc.obj (E.obj k))
      (_root_.GlobalTheory.EtC.disc.map ((pullback.snd p (_root_.GlobalTheory.EtC.sch.map U.hom)).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.sch.obj U.left)
      (_root_.GlobalTheory.EtC.BcLevel.dq p k) (_root_.GlobalTheory.EtC.sch.map U.hom) := by
  have h := (IsPullback.of_hasPullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).map
    ((evaluation SimplexCategoryᵒᵖ _root_.GlobalTheory.EtC.PSh).obj k)
  exact h.map _root_.GlobalTheory.EtC.disc

def lvIso {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) (U : Over S) :
    disc.obj ((pullback p (sch.map U.hom)).obj k) ≅ pullback (dq p k) (sch.map U.hom) :=
  (isPullback_lv p k U).isoPullback

set_option synthInstance.maxHeartbeats 200000 in
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.BcLevel.lv_nat {E : _root_.GlobalTheory.EtC.Spc} {S : Scheme.{0}}
    (p : E ⟶ _root_.GlobalTheory.EtC.sch.obj S) (k : SimplexCategoryᵒᵖ) {U V : Over S} (g : U ⟶ V) :
    (_root_.GlobalTheory.EtC.disc.map (((_root_.GlobalTheory.EtC.bc p).map g).app k) : _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map U.hom)).obj k) ⟶ _root_.GlobalTheory.EtC.disc.obj ((pullback p (_root_.GlobalTheory.EtC.sch.map V.hom)).obj k)) ≫
      (_root_.GlobalTheory.EtC.BcLevel.lvIso p k V).hom = (_root_.GlobalTheory.EtC.BcLevel.lvIso p k U).hom ≫ (_root_.GlobalTheory.EtC.bc (_root_.GlobalTheory.EtC.BcLevel.dq p k)).map g := by
  have hV₁ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k V).isoPullback_hom_fst
  have hV₂ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k V).isoPullback_hom_snd
  have hU₁ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k U).isoPullback_hom_fst
  have hU₂ := (_root_.GlobalTheory.EtC.BcLevel.isPullback_lv p k U).isoPullback_hom_snd
  unfold _root_.GlobalTheory.EtC.BcLevel.lvIso
  dsimp only [_root_.GlobalTheory.EtC.bc]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    erw [hV₁, pullback.lift_fst, Category.comp_id, hU₁]
    rw [← Functor.map_comp, ← NatTrans.comp_app, pullback.lift_fst, Category.comp_id]
  · rw [Category.assoc, Category.assoc]
    erw [hV₂, pullback.lift_snd, ← Category.assoc, hU₂]
    change _ = _root_.GlobalTheory.EtC.disc.map _ ≫
      _root_.GlobalTheory.EtC.disc.map ((_root_.GlobalTheory.EtC.sch.map g.left).app k)
    rw [← Functor.map_comp]
    erw [← Functor.map_comp]
    congr 1
    rw [← NatTrans.comp_app]
    erw [← NatTrans.comp_app, pullback.lift_snd]

def bcDiscIso {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) :
    bc p ⋙ (evaluation _ PSh).obj k ⋙ disc ≅ bc (dq p k) :=
  NatIso.ofComponents (lvIso p k) (fun g => lv_nat p k g)

theorem bc_level : ∀ (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (k : SimplexCategoryᵒᵖ) (X : Scheme.{0}) (r : X ⟶ S)
    (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r →
    Nonempty (bc (sch.map r) ≅ bc p ⋙ (evaluation _ PSh).obj k ⋙ disc) := by
  intro S E p k X r e h
  have heq : sch.map r = (disc.mapIso e : sch.obj X ≅ disc.obj (E.obj k)).hom ≫ dq p k := by
    change disc.map (yoneda.map r) = disc.map e.hom ≫ disc.map (p.app k)
    rw [← h]
    exact disc.map_comp _ _
  rw [heq]
  exact ⟨bcIsoOfIso _ (dq p k) ≪≫ (bcDiscIso p k).symm⟩

end GlobalTheory.EtC.BcLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutPoly
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace GlobalTheory.PolynomialPushoutEquivalence

theorem eqv_iso (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n

  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_comp (R : Type) [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n

  have e : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext (pull_comp R f g F n)
  rw [e]
  exact (hf n).comp (hg n)

theorem isPushout_poly {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    IsPushout (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (Polynomial.mapRingHom φ)) (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)) := by

  let _ : Algebra A B := φ.toAlgebra
  let _ : Algebra (Polynomial A) (Polynomial B) := Polynomial.algebra A B
  exact CommRingCat.isPushout_of_isPushout A (Polynomial A) B (Polynomial B)

theorem main (q : ℕ) (A : Type) [CommRing A] (i : ℤ) (A' : Type) [CommRing A']
    (s : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A))
    (h : Eqv (ZMod q) (E := sp (Polynomial A')) (spMap Polynomial.C) (tw q i)) :
    Eqv (ZMod q) (sch.map (pullback.map
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 (Spec (CommRingCat.of A))) s
      (𝟙 (Spec (CommRingCat.of A))) s (Spec.map (CommRingCat.ofHom Polynomial.C)) (𝟙 _) (𝟙 _)
      (by simp) (by simp))) (tw q i) := by

  set φ : A →+* A' := (Spec.preimage s).hom with hφ
  have hs : s = Spec.map (CommRingCat.ofHom φ) := by simp [φ]

  have sq : IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A' →+* Polynomial A')))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 (Spec (CommRingCat.of A))) s := by
    rw [Category.comp_id, hs]
    exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_poly φ)

  have e : pullback.map
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 (Spec (CommRingCat.of A))) s
      (𝟙 (Spec (CommRingCat.of A))) s (Spec.map (CommRingCat.ofHom Polynomial.C)) (𝟙 _) (𝟙 _)
      (by simp) (by simp) =
      sq.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A' →+* Polynomial A')) ≫
        inv (pullback.snd (𝟙 (Spec (CommRingCat.of A))) s) := by
    rw [← Category.assoc, IsIso.eq_comp_inv, sq.isoPullback_inv_snd]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  rw [e, Functor.map_comp, Functor.map_comp]
  exact eqv_comp _ _ _ _ (eqv_iso _ _ _) (eqv_comp _ _ _ _ h (eqv_iso _ _ _))

end GlobalTheory.PolynomialPushoutEquivalence

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatIffExistsRatFunc
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem isRat_iff_exists_ratFunc : ∀ (F : Type) [Field F] (φ : PowerSeries F), IsRat φ ↔
    ∃ ρ : RatFunc F, algebraMap (RatFunc F) (LaurentSeries F) ρ = algebraMap (PowerSeries F) (LaurentSeries F) φ := by
  intro F _ φ
  have key : ∀ P : F[X], algebraMap (RatFunc F) (LaurentSeries F) (algebraMap F[X] (RatFunc F) P) =
      algebraMap (PowerSeries F) (LaurentSeries F) (P : PowerSeries F) := by
    intro P
    exact (RatFunc.coe_coe P).symm
  constructor
  · rintro ⟨p, q, hq, h⟩
    refine ⟨algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q, ?_⟩
    have hq' : algebraMap (PowerSeries F) (LaurentSeries F) (q : PowerSeries F) ≠ 0 := by
      rw [← key]
      exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2 hq)
    rw [map_div₀, key, key, div_eq_iff hq', ← h, map_mul, mul_comm]
  · rintro ⟨ρ, h⟩
    refine ⟨ρ.num, ρ.denom, ρ.denom_ne_zero, ?_⟩
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change algebraMap (PowerSeries F) (LaurentSeries F) _ = algebraMap (PowerSeries F) (LaurentSeries F) _
    rw [map_mul, ← key, ← key, ← h, ← map_mul]
    congr 1
    have hd : algebraMap F[X] (RatFunc F) ρ.denom ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2 ρ.denom_ne_zero
    have e : ρ = algebraMap F[X] (RatFunc F) ρ.num / algebraMap F[X] (RatFunc F) ρ.denom :=
      (RatFunc.num_div_denom ρ).symm
    calc algebraMap F[X] (RatFunc F) ρ.denom * ρ
        = algebraMap F[X] (RatFunc F) ρ.denom *
            (algebraMap F[X] (RatFunc F) ρ.num / algebraMap F[X] (RatFunc F) ρ.denom) := congrArg _ e
      _ = algebraMap F[X] (RatFunc F) ρ.num := mul_div_cancel₀ _ hd

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorOfCompatIsIsoTarget
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC

theorem Pair.isTensor_of_compat_isIso (R : Type) [CommRing R] {I J K K' : Cx R} (τ : Pair I J K) (ν : Pair I J K')
    (u : K ⟶ K') : IsIso u → τ.Compat ν (𝟙 I) (𝟙 J) u → τ.IsTensor → ν.IsTensor := by
  intro hu hc hτ
  have hlift : ∀ (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w), ν.lift U w x = Sec.map (u.f w) (τ.lift U w x) := by
    intro U w x
    have h : ν.lift U w = ((u.f w).hom.app (op U)).hom ∘ₗ τ.lift U w := by
      apply DirectSum.linearMap_ext
      intro p
      apply TensorProduct.ext'
      intro a b
      simp only [Pair.lift, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul]
      exact (hc U p.1.1 p.1.2 w p.2 a b).symm
    exact LinearMap.congr_fun h x
  have hinv : ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (K'.X w) U), Sec.map (u.f w) (Sec.map ((inv u).f w) y) = y := by
    intro w U y
    change Sec.map ((inv u).f w ≫ u.f w) y = y
    rw [← HomologicalComplex.comp_f, IsIso.inv_hom_id, HomologicalComplex.id_f]
    rfl
  have hinv' : ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (K.X w) U), Sec.map ((inv u).f w) (Sec.map (u.f w) y) = y := by
    intro w U y
    change Sec.map (u.f w ≫ (inv u).f w) y = y
    rw [← HomologicalComplex.comp_f, IsIso.hom_inv_id, HomologicalComplex.id_f]
    rfl
  have hnat : ∀ {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U),
      Sec.map φ (Sec.res g z) = Sec.res g (Sec.map φ z) := by
    intro F G φ V U g z
    exact congrArg (fun f => f.hom z) (φ.hom.naturality g.op)
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · obtain ⟨S, hS, hP⟩ := hτ.1 U w (Sec.map ((inv u).f w) y)
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    refine ⟨x, ?_⟩
    rw [hlift, hx, hnat, hinv]
  · apply hτ.2 U w x
    rw [hlift] at hx
    have h2 := congrArg (Sec.map ((inv u).f w)) hx
    rw [hinv'] at h2
    rw [h2]
    exact map_zero _

end GlobalTheory.EtC

end
end

