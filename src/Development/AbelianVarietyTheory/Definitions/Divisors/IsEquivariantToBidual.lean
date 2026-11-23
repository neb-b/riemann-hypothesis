module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC pullbackSections)
open GlobalTheory.DualPull (adj adj_app pull_ext appLE_resG resG_appLE theta toCut ofCut cutEquiv)
open GlobalTheory.VB GlobalTheory.Conormal

namespace GlobalTheory.LieVB

section Eigen

variable {X Y : Scheme.{0}} {F G : X.Modules} {O : Type} [CommRing O] {ρ : O →+* End F}
  {ρ' : O →+* End G} (σ : O →+* Γ(X, ⊤))

theorem isEquivariant_inv {φ : F ≅ G} (h : IsEquivariant ρ ρ' φ.hom) :
    IsEquivariant ρ' ρ φ.inv := fun a => by
  rw [Iso.comp_inv_eq, Category.assoc, h a, Iso.inv_hom_id_assoc]

variable (ρ)

theorem smul_eq_smulHom_comp (a : Γ(X, ⊤)) (φ : F ⟶ G) : a • φ = smulHom F a ≫ φ :=
  (smul_hom_def a φ).trans (smulHom_comp a φ).symm

theorem dualMap_smul (a : Γ(X, ⊤)) (φ : F ⟶ G) : dualMap (a • φ) = a • dualMap φ := by
  rw [smul_eq_smulHom_comp, dualMap_comp, dualMap_smulHom]
  rfl

def dualQuotHom : dual (eigenQuot ρ σ) ⟶ eigen (dualAct ρ) σ :=
  eigenLift (ρ := dualAct ρ) (σ := σ) (dualMap (eigenπ ρ σ)) fun a => by
    rw [act_dualAct, ← dualMap_comp, act_eigenπ, dualMap_smul]

instance isIso_dualQuotHom : IsIso (dualQuotHom ρ σ) := by
  refine Twist.isIso_of_bijective _ fun V => ⟨Function.Injective.of_comp
    (f := (eigenι (dualAct ρ) σ).app V) (QCoh.injective_app_of_mono (dualMap (eigenπ ρ σ)) V),
    fun s => ?_⟩
  let l := (eigenι (dualAct ρ) σ).app V s
  have hl (a : O) : act ρ a ≫ toCut l = σ a • toCut l := by
    ext W t
    apply (cutEquiv V W).injective
    have := congrArg (fun m => dualApp m (DualPull.cutO_le' V W) (resM F (DualPull.cutO_le V W) t))
      (mem_eigenSub_iff.1 ((eigenSub (dualAct ρ) σ).incl_app_mem s) a)
    refine ((DualPull.toCut_app l W _).trans ?_).trans (DualPull.cutEquiv_smul V W _ _).symm
    refine (congrArg _ (app_resM (act ρ a) _ t).symm).trans (this.trans ?_)
    rw [dualApp_smul, resG_resG]
    exact congrArg₂ (fun x y : Γ(X, DualPull.cutO V W) => x * y) (resG_resG _ _ _).symm rfl
  refine ⟨ofCut (eigenDesc _ hl), (eigenSub (dualAct ρ) σ).incl_app_injective V
    (dual_ext fun W h t => ?_)⟩
  refine (DualPull.dualApp_ofCut _ h ((eigenπ ρ σ).app W t)).trans ?_
  rw [show (eigenDesc _ hl).app W ((eigenπ ρ σ).app W t) = (toCut l).app W t from
    congr(($(eigenπ_desc ρ σ _ hl)).app W t), DualPull.toCut_app, ← dualApp_resM, resM_resM,
    resM_self]
  rfl

def dualQuotIso : dual (eigenQuot ρ σ) ≅ eigen (dualAct ρ) σ := asIso (dualQuotHom ρ σ)

theorem dualQuotIso_hom_ι :
    (dualQuotIso ρ σ).hom ≫ eigenι _ _ =
      dualMap (eigenπ ρ σ) := by
  simp only [dualQuotIso, asIso_hom, dualQuotHom, eigenLift_ι]

def pullbackQuotIso (f : Y ⟶ X) : eigenQuot (pullAct ρ f) (f.appTop.hom.comp σ) ≅
    (Scheme.Modules.pullback f).obj (eigenQuot ρ σ) where
  hom := eigenDesc ((Scheme.Modules.pullback f).map (eigenπ ρ σ)) fun a => by
    rw [act_pullAct, ← Functor.map_comp, act_eigenπ, pullback_map_smul]; rfl
  inv := adj f (eigenDesc ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
    (eigenπ (pullAct ρ f) (f.appTop.hom.comp σ))) fun a => by
      rw [← Adjunction.homEquiv_naturality_left, smul_eq_smulHom_comp,
        ← Adjunction.homEquiv_naturality_left, pullback_map_smulHom, ← smul_eq_smulHom_comp]
      exact congrArg _ (act_eigenπ (pullAct ρ f) _ a))
  hom_inv_id := by
    rw [← cancel_epi (eigenπ _ _), eigenπ_desc_assoc, Category.comp_id, adj,
      ← Adjunction.homEquiv_naturality_left_symm, eigenπ_desc, Equiv.symm_apply_apply]
  inv_hom_id := by
    rw [← cancel_epi ((Scheme.Modules.pullback f).map (eigenπ ρ σ)), ← Category.assoc, adj,
      ← Adjunction.homEquiv_naturality_left_symm, eigenπ_desc, Equiv.symm_apply_apply, eigenπ_desc,
      Category.comp_id]

theorem hom_ext_of_isFrame {κ : Type} [Fintype κ] {e : κ → Γ(F, ⊤)} (he : IsFrame e)
    {φ ψ : F ⟶ G} (h : ∀ i, φ.app ⊤ (e i) = ψ.app ⊤ (e i)) : φ = ψ := by
  ext V s
  refine congr($((he.basis le_top).ext (f₁ := QCoh.appLinear φ V) (f₂ := QCoh.appLinear ψ V)
    fun i => ?_) s)
  rw [IsFrame.basis_apply]
  exact (app_resM φ _ _).trans ((congrArg _ (h i)).trans (app_resM ψ _ _).symm)

end Eigen

theorem isFrame_d_Spec {R A : CommRingCat.{0}} [Algebra R A] (ε : A →ₐ[R] R)
    {π : Spec A ⟶ Spec R} {e : Spec R ⟶ Spec A} (he : e ≫ π = 𝟙 _)
    (hπ : π = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hε : e = Spec.map (CommRingCat.ofHom ε.toRingHom)) {κ : Type} [Fintype κ]
    (b : Module.Basis κ R (AugCot ε)) (a : κ → A) (hb : ∀ i, b i = AugCot.d ε (a i)) :
    IsFrame fun i => d he (W := ⊤) (V := ⊤) le_top ((Scheme.ΓSpecIso A).inv (a i)) := by
  subst hπ hε
  exact IsChart.isFrame_d he ⟨isAffineOpen_top _, isAffineOpen_top _, le_top, le_top⟩ ε
    (Scheme.ΓSpecIso R).inv.hom (Scheme.ΓSpecIso A).inv.hom
    (IsPushout.of_vert_isIso (g := (Scheme.ΓSpecIso R).inv) (inl := (Scheme.ΓSpecIso A).inv)
      ⟨Scheme.ΓSpecIso_inv_naturality _⟩)
    (fun x => congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ε.toRingHom)) x).symm)
    b a hb

end GlobalTheory.LieVB
