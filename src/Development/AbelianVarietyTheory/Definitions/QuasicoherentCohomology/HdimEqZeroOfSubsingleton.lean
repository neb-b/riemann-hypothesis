module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ToAbSheafPreservesFiniteLimits

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

universe t v u

noncomputable section

namespace GlobalTheory

variable {X : Scheme.{u}}

instance hasSheafify_topCat (T : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u} := inferInstance

instance hasExt_sheaf_topCat (T : TopCat.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := inferInstance

instance hasSheafify_scheme (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance

instance hasExt_sheaf_scheme (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance

def cohOn (F : X.Modules) (U : X.Opens) (n : ℕ) : Type u :=
  Sheaf.H'.{u} ((toAbSheaf (X := X)).obj F) n U

abbrev coh (F : X.Modules) (n : ℕ) : Type u := cohOn F ⊤ n

namespace cohOn

def action (F : X.Modules) (U : X.Opens) (n : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (Sheaf.H'.{u} ((toAbSheaf (X := X)).obj F) n U) :=
  (SiteCoh.endAction (F := (toAbSheaf (X := X)).obj F) (n := n) (U := U)).comp
    ((functorEndRingHom (toAbSheaf (X := X)) F).comp (smulEnd F))

lemma action_apply (F : X.Modules) (U : X.Opens) (n : ℕ) (r : Γ(X, ⊤))
    (x : Sheaf.H'.{u} ((toAbSheaf (X := X)).obj F) n U) :
    action F U n r x = SiteCoh.map ((toAbSheaf (X := X)).map (smulHom F r)) n U x :=
  SiteCoh.endAction_apply _ x

instance instAddCommGroup (F : X.Modules) (U : X.Opens) (n : ℕ) : AddCommGroup (cohOn F U n) :=
  addCommGroupOfAction (M := Sheaf.H'.{u} ((toAbSheaf (X := X)).obj F) n U) inferInstance (action F U n)

def toH' (F : X.Modules) (U : X.Opens) (n : ℕ) :
    cohOn F U n ≃+ Sheaf.H'.{u} ((toAbSheaf (X := X)).obj F) n U :=
  WithAction.toBase (action F U n)

section Module

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

instance instModule (F : X.Modules) (U : X.Opens) (n : ℕ) : Module R (cohOn F U n) :=
  { WithAction.instModule (action F U n) R with
    smul := fun r x ↦ action F U n (algebraMap R Γ(X, ⊤) r) x }


variable {R} in
lemma toH'_smul {F : X.Modules} {U : X.Opens} {n : ℕ} (r : R) (x : cohOn F U n) :
    toH' F U n (r • x) =
      SiteCoh.map ((toAbSheaf (X := X)).map (smulHom F (algebraMap R Γ(X, ⊤) r))) n U (toH' F U n x) :=
  (WithAction.toBase_smul (R := R) (action F U n) r x).trans (action_apply F U n _ _)

instance instIsScalarTower (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] [Algebra R S]
    [IsScalarTower R S Γ(X, ⊤)] (F : X.Modules) (U : X.Opens) (n : ℕ) :
    IsScalarTower R S (cohOn F U n) :=
  WithAction.instIsScalarTower (action F U n) R S

def map {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) (n : ℕ) : cohOn F U n →ₗ[R] cohOn G U n :=
  WithAction.linearMap (action F U n) (action G U n) R
    (SiteCoh.map ((toAbSheaf (X := X)).map φ) n U).hom fun r x ↦ by
      rw [action_apply, action_apply, ← SiteCoh.map_comp_apply, ← SiteCoh.map_comp_apply,
        ← Functor.map_comp, ← Functor.map_comp, smulHom_comp]

def res (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (n : ℕ) : cohOn F U n →ₗ[R] cohOn F V n :=
  WithAction.linearMap (action F U n) (action F V n) R
    (SiteCoh.res ((toAbSheaf (X := X)).obj F) n (homOfLE h)).hom fun r x ↦ by
      rw [action_apply, action_apply, SiteCoh.res_map_apply]

variable {F G H : X.Modules} {U V W : X.Opens} {n : ℕ}

lemma toH'_map (φ : F ⟶ G) (x : cohOn F U n) :
    toH' G U n (map R φ U n x) = SiteCoh.map ((toAbSheaf (X := X)).map φ) n U (toH' F U n x) := rfl

lemma toH'_res (h : V ≤ U) (x : cohOn F U n) :
    toH' F V n (res R F h n x) =
      SiteCoh.res ((toAbSheaf (X := X)).obj F) n (homOfLE h) (toH' F U n x) := rfl

lemma smul_eq_map (r : R) (x : cohOn F U n) :
    r • x = map R (smulHom F (algebraMap R Γ(X, ⊤) r)) U n x := rfl


variable (F U n) in
@[simp] lemma map_id : map R (𝟙 F) U n = LinearMap.id := by
  ext x
  apply (toH' F U n).injective
  rw [toH'_map, CategoryTheory.Functor.map_id, SiteCoh.map_id_apply, LinearMap.id_apply]


variable (U n) in
lemma map_comp (φ : F ⟶ G) (ψ : G ⟶ H) :
    map R (φ ≫ ψ) U n = map R ψ U n ∘ₗ map R φ U n := by
  ext x
  apply (toH' H U n).injective
  rw [LinearMap.comp_apply, toH'_map, toH'_map, toH'_map, Functor.map_comp,
    SiteCoh.map_comp_apply]

lemma map_map (φ : F ⟶ G) (ψ : G ⟶ H) (x : cohOn F U n) :
    map R ψ U n (map R φ U n x) = map R (φ ≫ ψ) U n x := by
  rw [map_comp]; rfl


variable (U n) in
lemma map_add_hom (φ ψ : F ⟶ G) : map R (φ + ψ) U n = map R φ U n + map R ψ U n := by
  ext x
  apply (toH' G U n).injective
  rw [LinearMap.add_apply, map_add (f := toH' G U n), toH'_map, toH'_map, toH'_map,
    Functor.map_add (toAbSheaf (X := X)), SiteCoh.map_add_apply]


variable (F G U n) in
@[simps! apply] def mapAddHom : (F ⟶ G) →+ (cohOn F U n →ₗ[R] cohOn G U n) :=
  AddMonoidHom.mk' (fun φ ↦ map R φ U n) (map_add_hom R U n)


variable (F G U n) in
@[simp] lemma map_zero_hom : map R (0 : F ⟶ G) U n = 0 := map_zero (mapAddHom R F G U n)


variable (U n) in
lemma map_neg_hom (φ : F ⟶ G) : map R (-φ) U n = -map R φ U n := map_neg (mapAddHom R F G U n) φ



variable (U n) in
lemma map_sum_hom {ι : Type t} (s : Finset ι) (φ : ι → (F ⟶ G)) :
    map R (∑ i ∈ s, φ i) U n = ∑ i ∈ s, map R (φ i) U n :=
  map_sum (mapAddHom R F G U n) φ s



variable (F U n) in
@[simp] lemma res_refl : res R F (le_refl U) n = LinearMap.id := by
  ext x
  apply (toH' F U n).injective
  rw [toH'_res, show homOfLE (le_refl U) = 𝟙 U from rfl, SiteCoh.res_id_apply,
    LinearMap.id_apply]


variable (F n) in
lemma res_comp_res (h : V ≤ U) (h' : W ≤ V) :
    res R F h' n ∘ₗ res R F h n = res R F (h'.trans h) n := by
  ext x
  apply (toH' F W n).injective
  rw [LinearMap.comp_apply, toH'_res, toH'_res, toH'_res, ← SiteCoh.res_comp_apply,
    homOfLE_comp]

lemma res_map (φ : F ⟶ G) (h : V ≤ U) (x : cohOn F U n) :
    res R G h n (map R φ U n x) = map R φ V n (res R F h n x) := by
  apply (toH' G V n).injective
  rw [toH'_res, toH'_map, toH'_map, toH'_res, SiteCoh.res_map_apply]



variable (U n) in
@[simps! apply symm_apply] def mapIso (e : F ≅ G) : cohOn F U n ≃ₗ[R] cohOn G U n :=
  LinearEquiv.ofLinearMap (map R e.hom U n) (map R e.inv U n)
    (by rw [← map_comp, e.inv_hom_id, map_id]) (by rw [← map_comp, e.hom_inv_id, map_id])



end Module

lemma subsingleton_of_isZero {F : X.Modules} (h : IsZero F) (U : X.Opens) (n : ℕ) :
    Subsingleton (cohOn F U n) :=
  subsingleton_of_forall_eq 0 fun x ↦ by
    have h₁ : map ℤ (𝟙 F) U n x = x := by rw [map_id]; rfl
    rw [← h₁, h.eq_of_src (𝟙 F) 0, map_zero_hom]; rfl


section Products

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] {ι : Type t} (U : X.Opens) (n : ℕ)

@[simps! apply symm_apply] def biconeEquiv [Fintype ι] {F : ι → X.Modules} {c : Bicone F}
    (hc : c.IsBilimit) : cohOn c.pt U n ≃ₗ[R] ∀ i, cohOn (F i) U n :=
  LinearEquiv.ofLinearMap (LinearMap.pi fun i ↦ map R (c.π i) U n)
    (∑ i, map R (c.ι i) U n ∘ₗ LinearMap.proj i)
    (by
      classical
      refine LinearMap.ext fun x ↦ funext fun i ↦ ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
        LinearMap.proj_apply, LinearMap.id_apply, map_map]
      rw [Finset.sum_eq_single i]
      · rw [bicone_ι_π_self, map_id, LinearMap.id_apply]
      · intro j _ hj
        rw [bicone_ι_π_ne _ hj, map_zero_hom, LinearMap.zero_apply]
      · simp)
    (by
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply,
        LinearMap.proj_apply, LinearMap.id_apply, map_map]
      rw [← LinearMap.sum_apply, ← map_sum_hom, IsBilimit.total hc, map_id, LinearMap.id_apply])

lemma pi_map_bijective [Finite ι] {F : ι → X.Modules} {c : Fan F} (hc : IsLimit c) :
    Function.Bijective (LinearMap.pi fun i ↦ map R (c.proj i) U n) := by
  cases nonempty_fintype ι
  exact (biconeEquiv R U n (biconeIsBilimitOfLimitConeOfIsLimit hc)).bijective

def fanEquiv [Finite ι] {F : ι → X.Modules} {c : Fan F} (hc : IsLimit c) :
    cohOn c.pt U n ≃ₗ[R] ∀ i, cohOn (F i) U n :=
  LinearEquiv.ofBijective _ (pi_map_bijective R U n hc)

def piEquiv [Finite ι] (F : ι → X.Modules) : cohOn (∏ᶜ F) U n ≃ₗ[R] ∀ i, cohOn (F i) U n :=
  fanEquiv R U n (productIsProduct F)

@[simp] lemma piEquiv_apply [Finite ι] (F : ι → X.Modules) (x : cohOn (∏ᶜ F) U n) (i : ι) :
    piEquiv R U n F x i = map R (Pi.π F i) U n x := rfl

attribute [local instance] Abelian.hasFiniteBiproducts

def biproductEquiv [Finite ι] (F : ι → X.Modules) :
    cohOn (⨁ F) U n ≃ₗ[R] ∀ i, cohOn (F i) U n :=
  fanEquiv R U n (c := Fan.mk (⨁ F) (biproduct.π F)) (biproduct.isLimit F)

@[simp] lemma biproductEquiv_apply [Finite ι] (F : ι → X.Modules) (x : cohOn (⨁ F) U n) (i : ι) :
    biproductEquiv R U n F x i = map R (biproduct.π F i) U n x := rfl

end Products
end cohOn

def sectionsOn (F : X.Modules) (U : X.Opens) : Type u := Γ(F, U)

namespace sectionsOn

def action (F : X.Modules) (U : X.Opens) : Γ(X, ⊤) →+* AddMonoid.End Γ(F, U) :=
  (Module.toAddMonoidEnd Γ(X, U) Γ(F, U)).comp (restrictGlobal X U)

lemma action_apply (F : X.Modules) (U : X.Opens) (r : Γ(X, ⊤)) (x : Γ(F, U)) :
    action F U r x = restrictGlobal X U r • x := rfl

instance instAddCommGroup (F : X.Modules) (U : X.Opens) : AddCommGroup (sectionsOn F U) :=
  addCommGroupOfAction (M := Γ(F, U)) inferInstance (action F U)

def toΓ (F : X.Modules) (U : X.Opens) : sectionsOn F U ≃+ Γ(F, U) := WithAction.toBase (action F U)

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

instance instModule (F : X.Modules) (U : X.Opens) : Module R (sectionsOn F U) :=
  { WithAction.instModule (action F U) R with
    smul := fun r x ↦ action F U (algebraMap R Γ(X, ⊤) r) x }


variable {R} in
lemma toΓ_smul {F : X.Modules} {U : X.Opens} (r : R) (x : sectionsOn F U) :
    toΓ F U (r • x) = restrictGlobal X U (algebraMap R Γ(X, ⊤) r) • toΓ F U x := rfl

instance instIsScalarTower (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] [Algebra R S]
    [IsScalarTower R S Γ(X, ⊤)] (F : X.Modules) (U : X.Opens) : IsScalarTower R S (sectionsOn F U) :=
  WithAction.instIsScalarTower (action F U) R S

def map {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) : sectionsOn F U →ₗ[R] sectionsOn G U :=
  WithAction.linearMap (action F U) (action G U) R (φ.app U).hom
    fun r x ↦ φ.app_smul (restrictGlobal X U r) x

def res (F : X.Modules) {U V : X.Opens} (h : V ≤ U) : sectionsOn F U →ₗ[R] sectionsOn F V :=
  WithAction.linearMap (action F U) (action F V) R (F.presheaf.map (homOfLE h).op).hom
    fun r x ↦ by rw [action_apply, action_apply, F.map_smul, map_restrictGlobal]

variable {F G H : X.Modules} {U V W : X.Opens}

@[simp] lemma toΓ_map (φ : F ⟶ G) (x : sectionsOn F U) :
    toΓ G U (map R φ U x) = φ.app U (toΓ F U x) := rfl

@[simp] lemma toΓ_res (h : V ≤ U) (x : sectionsOn F U) :
    toΓ F V (res R F h x) = F.presheaf.map (homOfLE h).op (toΓ F U x) := rfl


variable (F U) in
@[simp] lemma map_id : map R (𝟙 F) U = LinearMap.id := rfl


variable (U) in
lemma map_comp (φ : F ⟶ G) (ψ : G ⟶ H) : map R (φ ≫ ψ) U = map R ψ U ∘ₗ map R φ U := rfl


variable (U) in
lemma map_add_hom (φ ψ : F ⟶ G) : map R (φ + ψ) U = map R φ U + map R ψ U := rfl


variable (F U) in
@[simp] lemma res_refl : res R F (le_refl U) = LinearMap.id := by
  ext x
  apply (toΓ F U).injective
  rw [toΓ_res, show homOfLE (le_refl U) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl


variable (F) in
lemma res_comp_res (h : V ≤ U) (h' : W ≤ V) : res R F h' ∘ₗ res R F h = res R F (h'.trans h) := by
  ext x
  apply (toΓ F W).injective
  rw [LinearMap.comp_apply, toΓ_res, toΓ_res, toΓ_res, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  rfl

lemma res_map (φ : F ⟶ G) (h : V ≤ U) (x : sectionsOn F U) :
    res R G h (map R φ U x) = map R φ V (res R F h x) :=
  (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x).symm


variable (F U) in
def equivOfSMul [Module R Γ(F, U)]
    (h : ∀ (r : R) (x : Γ(F, U)), r • x = restrictGlobal X U (algebraMap R Γ(X, ⊤) r) • x) :
    sectionsOn F U ≃ₗ[R] Γ(F, U) :=
  { toΓ F U with map_smul' := fun r x ↦ (toΓ_smul r x).trans (h r _).symm }


variable (F) in
def topEquiv : sectionsOn F ⊤ ≃ₗ[Γ(X, ⊤)] Γ(F, ⊤) :=
  equivOfSMul Γ(X, ⊤) F ⊤ fun r x ↦ by rw [restrictGlobal_top]; rfl

def specEquiv {A : CommRingCat.{u}} (F : (Spec A).Modules) (U : (Spec A).Opens) :
    sectionsOn F U ≃ₗ[A] Γ(F, U) :=
  equivOfSMul A F U fun r x ↦ by
    rw [Scheme.Modules.smul_Spec_def]
    congr 1

end sectionsOn

namespace cohOn

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

def zeroEquiv (F : X.Modules) (U : X.Opens) : cohOn F U 0 ≃ₗ[R] sectionsOn F U :=
  WithAction.linearEquiv (action F U 0) (sectionsOn.action F U) R
    (SiteCoh.zeroEquiv ((toAbSheaf (X := X)).obj F) U) fun r x ↦ by
      rw [action_apply]
      exact SiteCoh.zeroEquiv_map ((toAbSheaf (X := X)).map (smulHom F r)) U x

variable {F G : X.Modules} {U V : X.Opens}

lemma toΓ_zeroEquiv (x : cohOn F U 0) :
    sectionsOn.toΓ F U (zeroEquiv R F U x) =
      SiteCoh.zeroEquiv ((toAbSheaf (X := X)).obj F) U (toH' F U 0 x) := rfl


def zeroEquivSpec {A : CommRingCat.{u}} (F : (Spec A).Modules) (U : (Spec A).Opens) :
    cohOn F U 0 ≃ₗ[A] Γ(F, U) :=
  (zeroEquiv A F U).trans (sectionsOn.specEquiv F U)

end cohOn

abbrev structureModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

def structureModuleΓEquiv (X : Scheme.{u}) (U : X.Opens) :
    Γ(structureModule X, U) ≃ₗ[Γ(X, U)] Γ(X, U) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

namespace coh

def zeroEquiv (F : X.Modules) : coh F 0 ≃ₗ[Γ(X, ⊤)] Γ(F, ⊤) :=
  (cohOn.zeroEquiv Γ(X, ⊤) F ⊤).trans (sectionsOn.topEquiv F)

def toH (F : X.Modules) (n : ℕ) : coh F n ≃+ Sheaf.H.{u} ((toAbSheaf (X := X)).obj F) n :=
  (cohOn.toH' F ⊤ n).trans (SiteCoh.terminalEquiv ((toAbSheaf (X := X)).obj F) n isTerminalTop)

lemma toH_map (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] {F G : X.Modules} (φ : F ⟶ G)
    (n : ℕ) (x : coh F n) :
    toH G n (cohOn.map R φ ⊤ n x) = Sheaf.H.map ((toAbSheaf (X := X)).map φ) n (toH F n x) :=
  SiteCoh.terminalEquiv_map ((toAbSheaf (X := X)).map φ) n isTerminalTop (cohOn.toH' F ⊤ n x)

def zeroUnitEquiv (X : Scheme.{u}) :
    coh (structureModule X) 0 ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
  (zeroEquiv (structureModule X)).trans (structureModuleΓEquiv X ⊤)

def zeroUnitSpecEquiv (A : CommRingCat.{u}) :
    coh (structureModule (Spec A)) 0 ≃ₗ[A] A :=
  ((zeroUnitEquiv (Spec A)).restrictScalars A).trans
    (LinearEquiv.ofBijective (Algebra.linearMap A Γ(Spec A, ⊤)) (by
      have h : ⇑(Algebra.linearMap A Γ(Spec A, ⊤)) = (Scheme.ΓSpecIso A).inv :=
        funext fun r ↦ restrictGlobal_top ((Scheme.ΓSpecIso A).inv r)
      rw [h]
      exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv)).symm

end coh

section Functors

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

@[simps] def cohPresheaf (F : X.Modules) (n : ℕ) : X.Opensᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := ModuleCat.of R (cohOn F U.unop n)
  map i := ModuleCat.ofHom (cohOn.res R F i.unop.le n)
  map_id U := ModuleCat.hom_ext (cohOn.res_refl R F U.unop n)
  map_comp i j := ModuleCat.hom_ext (cohOn.res_comp_res R F n i.unop.le j.unop.le).symm

@[simps] def sectionsPresheaf (F : X.Modules) : X.Opensᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := ModuleCat.of R (sectionsOn F U.unop)
  map i := ModuleCat.ofHom (sectionsOn.res R F i.unop.le)
  map_id U := ModuleCat.hom_ext (sectionsOn.res_refl R F U.unop)
  map_comp i j := ModuleCat.hom_ext (sectionsOn.res_comp_res R F i.unop.le j.unop.le).symm

end Functors

abbrev algebraΓOfHom {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R)) : Algebra R Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom.toAlgebra

lemma algebraΓOfHom_algebraMap {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R)) (r : R) :
    (letI := algebraΓOfHom f; algebraMap R Γ(X, ⊤) r =
      f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) := rfl

abbrev algebraΓSpec (A : CommRingCat.{u}) : Algebra A Γ(Spec A, ⊤) := inferInstance

abbrev algebraΓOfOver (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))] :
    Algebra R Γ(X, ⊤) :=
  algebraΓOfHom (X ↘ Spec (.of R))

namespace OverSpec

scoped[GlobalTheory.OverSpec] attribute [instance 50] GlobalTheory.algebraΓOfOver

end OverSpec

def hdim (k : Type v) [Field k] [Algebra k Γ(X, ⊤)] (F : X.Modules) (n : ℕ) : ℕ :=
  Module.finrank k (coh F n)

section hdim

variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)] {F G : X.Modules} (n : ℕ)

lemma hdim_def (F : X.Modules) : hdim k F n = Module.finrank k (coh F n) := rfl

lemma hdim_eq_zero_iff [Module.Finite k (coh F n)] : hdim k F n = 0 ↔ Subsingleton (coh F n) :=
  Module.finrank_zero_iff

lemma hdim_eq_zero_of_subsingleton [Subsingleton (coh F n)] : hdim k F n = 0 :=
  Module.finrank_zero_of_subsingleton

lemma hdim_congr (e : F ≅ G) : hdim k F n = hdim k G n :=
  (cohOn.mapIso k ⊤ n e).finrank_eq

lemma hdim_zero (F : X.Modules) : hdim k F 0 = Module.finrank k (sectionsOn F ⊤) :=
  (cohOn.zeroEquiv k F ⊤).finrank_eq

end hdim

end GlobalTheory
