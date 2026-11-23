module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0756

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)

namespace GlobalTheory

namespace TopForm

open LB

section Ring

variable {k k' A B : Type} [CommRing k] [CommRing k'] [CommRing A] [CommRing B]
  {α : k →+* A} {β : k' →+* B}

def formMapSq (D : ℕ) (σ : k →+* k') (ρ : A →+* B) (h : ρ.comp α = β.comp σ) :
    Forms α D →ₛₗ[ρ] Forms β D :=
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  letI := σ.toAlgebra
  letI := (ρ.comp α).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq' h
  haveI : SMulCommClass k' A B := SMulCommClass.of_commMonoid _ _ _
  { toFun := exteriorPowerMapOver B D (KaehlerDifferential.map k k' A B)
    map_add' := map_add _
    map_smul' := fun a x => by
      rw [map_smul, ← algebraMap_smul B]
      rfl }

variable {D : ℕ}

theorem formMapSq_dForm (σ : k →+* k') (ρ : A →+* B) (h : ρ.comp α = β.comp σ) (f : Fin D → A) :
    formMapSq D σ ρ h (dForm α f) = dForm β fun i => ρ (f i) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  letI := σ.toAlgebra
  letI := (ρ.comp α).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq' h
  haveI : SMulCommClass k' A B := SMulCommClass.of_commMonoid _ _ _
  change exteriorPowerMapOver B D (KaehlerDifferential.map k k' A B)
    (exteriorPower.ιMulti A D _) = _
  rw [exteriorPowerMapOver_ιMulti, dForm_eq]
  simp only [KaehlerDifferential.map_D]
  rfl

theorem IsFreeGen.formMapSq (σ : k →+* k') (ρ : A →+* B) (h : ρ.comp α = β.comp σ)
    (H : IsPushout (CommRingCat.ofHom α) (CommRingCat.ofHom σ) (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom β)) {ω : Forms α D} (hω : IsFreeGen A ω) :
    IsFreeGen B (formMapSq D σ ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  letI := σ.toAlgebra
  letI := (ρ.comp α).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq' h
  haveI : SMulCommClass k' A B := SMulCommClass.of_commMonoid _ _ _
  haveI : Algebra.IsPushout k k' A B := (CommRingCat.isPushout_iff_isPushout.1 H).symm
  refine hω.of_isBaseChange (isBaseChange_exteriorPower
    (IsBaseChange.of_equiv (KaehlerDifferential.tensorKaehlerEquiv k k' A B) fun x => ?_) D)
  have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) :=
    (KaehlerDifferential.span_range_derivation k A).ge Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hx, hy]
  | smul a x _ hx =>
    rw [TensorProduct.tmul_smul, ← algebraMap_smul B, map_smul, hx, map_smul, algebraMap_smul]

end Ring

variable {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {Y Y' : Scheme.{0}}
  {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {φ : Y' ⟶ Y} {D : ℕ}

theorem appLE_comp_algX (w : φ ≫ p = p' ≫ spMap σ) {V : Y.Opens} {W : Y'.Opens}
    (h : W ≤ φ ⁻¹ᵁ V) : (φ.appLE V W h).hom.comp (algX p V) = (algX p' W).comp σ := by
  have e₁ : p.appLE ⊤ V le_top ≫ φ.appLE V W h =
      (spMap σ).appLE ⊤ ⊤ le_top ≫ p'.appLE ⊤ W le_top := by
    refine (Scheme.Hom.appLE_comp_appLE φ p ⊤ V W le_top h).trans (Eq.trans ?_
      (Scheme.Hom.appLE_comp_appLE p' (spMap σ) ⊤ ⊤ W le_top le_top).symm)
    simp only [w]
  have e₂ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ)
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at e₂
  have e₃ : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V le_top ≫ φ.appLE V W h =
      CommRingCat.ofHom σ ≫ (Scheme.ΓSpecIso (CommRingCat.of k')).inv ≫ p'.appLE ⊤ W le_top := by
    rw [e₁, ← Category.assoc, ← Category.assoc, e₂]
    rfl
  exact congrArg CommRingCat.Hom.hom e₃

def pullForm (w : φ ≫ p = p' ≫ spMap σ) {V : Y.Opens} {W : Y'.Opens} (h : W ≤ φ ⁻¹ᵁ V) :
    FormsOn p D V →ₛₗ[(φ.appLE V W h).hom] FormsOn p' D W :=
  formMapSq D σ (φ.appLE V W h).hom (appLE_comp_algX w h)

variable (w : φ ≫ p = p' ≫ spMap σ) {U V : Y.Opens} {U' W W' : Y'.Opens}

theorem pullForm_dOn (h : W ≤ φ ⁻¹ᵁ V) (f : Fin D → Γ(Y, V)) :
    pullForm w h (dOn p f) = dOn p' fun a => (φ.appLE V W h).hom (f a) :=
  formMapSq_dForm _ _ _ f

theorem resForm_pullForm (h : W ≤ φ ⁻¹ᵁ V) (e : W' ≤ W) (η : FormsOn p D V) :
    resForm e (pullForm w h η) = pullForm w (e.trans h) η := by
  haveI : RingHomCompTriple (φ.appLE V W h).hom (resG Y' e) (φ.appLE V W' (e.trans h)).hom :=
    ⟨RingHom.ext (resG_appLE φ h e)⟩
  refine LinearMap.congr_fun (forms_ext (φ := (resForm e).comp (pullForm w h))
    (ψ := pullForm w (e.trans h)) fun f => ?_) η
  rw [LinearMap.comp_apply, pullForm_dOn, pullForm_dOn, resForm_dOn]
  simp only [resG_appLE]

theorem pullForm_resForm (e : V ≤ U) (h : W ≤ φ ⁻¹ᵁ V) (η : FormsOn p D U) :
    pullForm w h (resForm e η) = pullForm w (h.trans (φ.preimage_mono e)) η := by
  haveI : RingHomCompTriple (resG Y e) (φ.appLE V W h).hom
      (φ.appLE U W (h.trans (φ.preimage_mono e))).hom :=
    ⟨RingHom.ext (appLE_resG φ e h)⟩
  refine LinearMap.congr_fun (forms_ext (φ := (pullForm w h).comp (resForm e))
    (ψ := pullForm w (h.trans (φ.preimage_mono e))) fun f => ?_) η
  rw [LinearMap.comp_apply, resForm_dOn, pullForm_dOn, pullForm_dOn]
  simp only [appLE_resG]

theorem IsFrame.coeff_pullForm {ω : FormsOn p D U} (hω : IsFrame ω) (hU : U' ≤ φ ⁻¹ᵁ U)
    (hω' : IsFrame (pullForm w hU ω)) (e : V ≤ U) (e' : W ≤ U') (h : W ≤ φ ⁻¹ᵁ V)
    (η : FormsOn p D V) :
    hω'.coeff e' (pullForm w h η) = (φ.appLE V W h).hom (hω.coeff e η) := by
  refine fun_ext_of_cover (fun T : {T : Y.Opens // IsAffineOpen T ∧ T ≤ V} => W ⊓ φ ⁻¹ᵁ T.1)
    (fun _ => inf_le_left) (fun x hx => ?_) fun T => ?_
  · obtain ⟨T, hT⟩ := Opens.mem_iSup.1 (le_iSup_affine V (h hx))
    exact Opens.mem_iSup.2 ⟨T, hx, hT⟩
  · have h₁ := congrArg (pullForm w (inf_le_right : W ⊓ φ ⁻¹ᵁ T.1 ≤ _))
      (hω.resForm_eq_coeff_smul e η T.2.1 T.2.2)
    rw [map_smulₛₗ, pullForm_resForm, pullForm_resForm, appLE_resG] at h₁
    rw [IsFrame.resG_coeff, resForm_pullForm, resG_appLE]
    exact hω'.coeff_eq_of_eq_smul _ (h₁.trans (by rw [resForm_pullForm]))

theorem isAffineOpen_preimage_of_isPullback (H : IsPullback φ p' p (spMap σ))
    (hU : IsAffineOpen U) : IsAffineOpen (φ ⁻¹ᵁ U) :=
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  hU.preimage φ

theorem IsFrame.pullForm (H : IsPullback φ p' p (spMap σ)) {ω : FormsOn p D U} (hω : IsFrame ω)
    (hW : IsAffineOpen W) (h : W ≤ φ ⁻¹ᵁ U) : IsFrame (pullForm H.w h ω) := by
  letI := σ.toAlgebra
  have h₁ : IsFrame (TopForm.pullForm H.w (inf_le_left : φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ ≤ _) ω) := by
    refine ⟨?_, hω.gen.formMapSq σ _ _ (isPushout_sections p p' φ H U hω.affine)⟩
    rw [show φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ = φ ⁻¹ᵁ U from inf_top_eq _]
    exact isAffineOpen_preimage_of_isPullback H hω.affine
  have h₂ := h₁.res hW (le_inf h le_top)
  rwa [resForm_pullForm] at h₂

end TopForm

namespace CanonLB

open TopForm LB

variable {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {Y Y' : Scheme.{0}}
  {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {φ : Y' ⟶ Y} {D : ℕ}
  [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']

theorem isFrame_pull (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D)
    (i : (K.bundle.pull φ).ι) : IsFrame (pullForm H.w (pull_U_le φ i) (K.om (i PUnit.unit))) :=
  (K.isFrame _).pullForm H
    (by rw [pull_U]; exact isAffineOpen_preimage_of_isPullback H (K.affine _)) _

def baseChange (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D) : CanonLB p' D where
  bundle := K.bundle.pull φ
  isLB := Semi.LB.isLB_linComb K.isLB _ _
  affine i := (K.isFrame_pull H i).affine
  om i := pullForm H.w (pull_U_le φ i) (K.om (i PUnit.unit))
  gen i := (K.isFrame_pull H i).gen
  trans i j W hW hi hj := by
    have h : W ≤ φ ⁻¹ᵁ (K.bundle.U (i PUnit.unit) ⊓ K.bundle.U (j PUnit.unit)) :=
      le_inf (hi.trans (pull_U_le φ i)) (hj.trans (pull_U_le φ j))
    have h₁ := (K.isFrame _).coeff_pullForm H.w _ (K.isFrame_pull H i) inf_le_left hi h
      (resForm inf_le_right (K.om (j PUnit.unit)))
    rw [pullForm_resForm] at h₁
    rw [resG_pull_g, g_eq_ratio, resForm_pullForm]
    exact ((K.isFrame_pull H i).coeff_smul_resForm hW hi _).symm.trans (congrArg (· • _) h₁)

theorem jacobian_baseChange (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D)
    (i : (K.bundle.pull φ).ι) {V : Y.Opens} (hV : V ≤ K.bundle.U (i PUnit.unit)) {W : Y'.Opens}
    (hW : W ≤ (K.bundle.pull φ).U i) (h : W ≤ φ ⁻¹ᵁ V) (f : Fin D → Γ(Y, V)) :
    (K.baseChange H).jacobian i hW (fun a => (φ.appLE V W h).hom (f a)) =
      (φ.appLE V W h).hom (K.jacobian (i PUnit.unit) hV f) := by
  have h₁ := (K.isFrame _).coeff_pullForm H.w _ (K.isFrame_pull H i) hV hW h (dOn p f)
  rw [pullForm_dOn] at h₁
  exact h₁

end CanonLB

theorem canonLB_baseChange (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (Y Y' : Scheme.{0}) (p : Y ⟶ Sp k) (p' : Y' ⟶ Sp k') (φ : Y' ⟶ Y) (D : ℕ)
    [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']
    (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D) (K' : CanonLB p' D) :
    ∃ w : LB.Iso K'.bundle (K.bundle.pull φ), w.IsGen ∧
      ∀ (i : (K.bundle.pull φ).ι) (j : K'.bundle.ι) (V : Y.Opens)
        (hV : V ≤ K.bundle.U (i PUnit.unit)) (W : Y'.Opens) (hW : W ≤ K'.bundle.U j)
        (h : W ≤ φ ⁻¹ᵁ V) (hw : W ≤ (LB.div (K.bundle.pull φ) K'.bundle).U (i, j))
        (f : Fin D → Γ(Y, V)),
        (φ.appLE V W h).hom (K.jacobian (i PUnit.unit) hV f) =
          resG Y' hw (w.s (i, j)).val * K'.jacobian j hW (fun a => (φ.appLE V W h).hom (f a)) :=
  ⟨K'.iso (K.baseChange H), K'.iso_isGen (K.baseChange H), fun i j _ hV _ hW h hw f =>
    (K.jacobian_baseChange H i hV (hw.trans inf_le_left) h f).symm.trans
      (K'.coeff_eq_iso_mul (K.baseChange H) i j _ hW _)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGeneratingCombinationMatrixLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixOpen

variable {A₀ X T : Scheme.{0}} {N : LB A₀} {mA mB : ℕ}

theorem isUnit_comb_chart (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (z : X) {q q' : N.ι} (hq : φ z ∈ N.U q) (hq' : φ z ∈ N.U q') (j : Fin mB) :
    IsUnit (comb a φ p c z q j) ↔ IsUnit (comb a φ p c z q' j) := by
  have e : comb a φ p c z q j = (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * comb a φ p c z q' j := by
    simp only [comb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_compat (a i) φ z hq hq', mul_left_comm]
  rw [e, Units.isUnit_units_mul]

theorem comb_comp {Y : Scheme.{0}} (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (h : Y ⟶ X) (y : Y) (q : N.ι) (hq : φ (h y) ∈ N.U q) (j : Fin mB) :
    comb a (h ≫ φ) (h ≫ p) c y q j = (h.stalkMap y).hom (comb a φ p c (h y) q j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_comp h p y ⊤ trivial, gs_comp h φ y (N.U q) hq]

theorem gs_top {Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (z : X) (c : Γ(Z, ⊤)) :
    gs f z ⊤ (g.appTop.hom c) = gs (f ≫ g) z ⊤ c :=
  gs_pull f g z ⊤ trivial c

theorem gs_sum' {Y : Scheme.{0}} (f : X ⟶ Y) (z : X) (U : Y.Opens) (h : f z ∈ U) {n : ℕ} (b : Fin n → Γ(Y, U)) :
    gs f z U (∑ i, b i) = ∑ i, gs f z U (b i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f z U h, map_sum]

def good (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) : Set X :=
  {z | ∃ q, φ z ∈ N.U q ∧ ∃ j, IsUnit (comb a φ p c z q j)}

def combFn (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (q : N.ι)
    (j : Fin mB) : Γ(X, φ ⁻¹ᵁ N.U q) :=
  ∑ i, (X.presheaf.map (homOfLE le_top).op).hom (p.appTop.hom (c i j)) * (φ.app (N.U q)).hom ((a i).f q)

theorem gs_combFn (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (q : N.ι)
    (j : Fin mB) (z : X) (hz : φ z ∈ N.U q) : gs (𝟙 X) z _ (combFn a φ p c q j) = comb a φ p c z q j := by
  have hz' : (𝟙 X) z ∈ φ ⁻¹ᵁ N.U q := hz
  rw [combFn, gs_sum' (𝟙 X) z _ hz']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul _ z _ hz', gs_res _ z le_top hz', gs_top, gs_pull (𝟙 X) φ z (N.U q) hz, Category.id_comp,
    Category.id_comp]

theorem isOpen_good (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) :
    IsOpen (good a φ p c) := by
  have e : good a φ p c = ⋃ q, ⋃ j, (X.basicOpen (combFn a φ p c q j) : Set X) := by
    ext z
    simp only [good, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq, j, hu⟩
      refine ⟨q, j, ?_⟩
      rw [← gs_combFn a φ p c q j z hq] at hu
      exact (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) z _ hq _).1 hu
    · rintro ⟨q, j, hz⟩
      have hq : φ z ∈ N.U q := X.basicOpen_le _ hz
      refine ⟨q, hq, j, ?_⟩
      rw [← gs_combFn a φ p c q j z hq]
      exact (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) z _ hq _).2 hz
  rw [e]
  exact isOpen_iUnion fun q => isOpen_iUnion fun j => (X.basicOpen _).isOpen

end GlobalTheory.HomFixOpen

namespace GlobalTheory.HomFixOpen

theorem main : ∀ (Rg : Type) [CommRing Rg] (A₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) [UniversallyClosed f] (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N), N.IsLB → ∃ U : (Sp (MvPolynomial (Fin (mA * mB)) Rg)).Opens, ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.Generates a φ p (matOf g) ↔ ∀ τ, g τ ∈ U) := by
  intro Rg _ A₀ f _ N mA mB a hN
  let π₁ := pullback.fst f (affπ Rg (mA * mB))
  let π₂ := pullback.snd f (affπ Rg (mA * mB))
  let G := good a π₁ π₂ (matOf (𝟙 (Sp (MvPolynomial (Fin (mA * mB)) Rg))))
  have hG : IsOpen G := isOpen_good _ _ _ _
  have hC : IsClosed (π₂ '' Gᶜ) := π₂.isClosedMap _ hG.isClosed_compl
  refine ⟨⟨(π₂ '' Gᶜ)ᶜ, hC.isOpen_compl⟩, fun T X' g φ p hP => ?_⟩
  have w : φ ≫ f = (p ≫ g) ≫ affπ Rg (mA * mB) := by rw [Category.assoc]; exact hP.w
  let h := pullback.lift φ (p ≫ g) w
  have h1 : h ≫ π₁ = φ := pullback.lift_fst _ _ _
  have h2 : h ≫ π₂ = p ≫ g := pullback.lift_snd _ _ _
  have hπ₁ : ∀ z, π₁ (h z) = φ z := fun z => by rw [← Scheme.Hom.comp_apply, h1]
  have key : ∀ z q j, φ z ∈ N.U q → comb a φ p (matOf g) z q j =
      (h.stalkMap z).hom (comb a π₁ π₂ (matOf (𝟙 _)) (h z) q j) := by
    intro z q j hq
    rw [← comb_comp a π₁ π₂ _ h z q (by rw [hπ₁]; exact hq) j]
    simp only [comb, h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [h2, matOf, matOf, coord, coord, gs_top, gs_top, Category.comp_id]
  have unitIff : ∀ z q j, φ z ∈ N.U q → (IsUnit (comb a φ p (matOf g) z q j) ↔
      IsUnit (comb a π₁ π₂ (matOf (𝟙 _)) (h z) q j)) := by
    intro z q j hq; rw [key z q j hq]; exact isUnit_map_iff _ _
  have stepA : Generates a φ p (matOf g) ↔ ∀ z, h z ∈ G := by
    constructor
    · intro hg z
      obtain ⟨q, hq⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hN (φ z)
      obtain ⟨j, hj⟩ := hg z q hq
      exact ⟨q, by rw [hπ₁]; exact hq, j, (unitIff z q j hq).1 hj⟩
    · intro hg z q hq
      obtain ⟨q', hq', j, hj⟩ := hg z
      exact ⟨j, (unitIff z q j hq).2 ((isUnit_comb_chart a π₁ π₂ _ (h z) hq' (by rw [hπ₁]; exact hq) j).1 hj)⟩
  rw [stepA]
  have hP' : IsPullback h p π₂ g := IsPullback.of_right (by rw [h1]; exact hP) h2 (IsPullback.of_hasPullback _ _)
  constructor
  · intro hg τ
    show g τ ∈ (π₂ '' Gᶜ)ᶜ
    rintro ⟨w', hw, he⟩
    obtain ⟨y, hy1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π₂) (g := g) w' τ he
    apply hw
    have e : h (hP'.isoPullback.inv y) = w' := by
      rw [← Scheme.Hom.comp_apply, hP'.isoPullback_inv_fst, hy1]
    rw [← e]; exact hg _
  · intro hg z
    by_contra hz
    exact hg (p z) ⟨h z, hz, by rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply]⟩

end GlobalTheory.HomFixOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.MovedVacuum

theorem isVacuum_thetaIntertwiner_selfDual (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl t0 : ℂ) (hc : StandardLatticesGL3.Crv D cc dl)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0) {a b : ℕ}
    {L L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' L₁' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (hL : StandardLatticesGL3.SD D L) (hL' : StandardLatticesGL3.SD D L') (hL₁ : StandardLatticesGL3.SD D L₁) (hL₁' : StandardLatticesGL3.SD D L₁')
    {G : TaylorLogMetric.VC D a b → ℂ} (hG : StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' G) :
    StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L₁ L₁'
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc dl) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc dl) L L')
        (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc dl) L₁ L₁') G) := by
  obtain ⟨e, κ, he, hκ, rfl⟩ := hG
  obtain ⟨μ, hμ, h⟩ := GlobalTheory.TripleIntertwiner.triple_constant D cc dl hc a b _ _ _
    (Or.inl ⟨_, e, he, rfl⟩) (Or.inr ⟨L, L', hL, hL', rfl⟩) (Or.inr ⟨L₁, L₁', hL₁, hL₁', rfl⟩) _
    (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D (GlobalTheory.InducedType.induced_type D).1 cc dl t0 hc ht e he.1)
  refine ⟨e, κ * μ, he, GlobalTheory.VacuumMove.mod1All_mul hκ hμ, funext fun z => ?_⟩
  rw [GlobalTheory.VacuumMove.Iop_mul, mul_assoc κ μ]
  exact congrArg (κ * ·) (congrFun h z)

theorem sd_stdL (D : D7) (n : ℕ) : StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D n) := by
  letI := D.host.cmStar
  exact GlobalTheory.SeamSelfDual.isSDLat_pi D.host.E n

theorem isVacuum_movedThetaVacuum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) (B.thZero a b) → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' (B.thMoved a b L L') := by
  intro D cc dl B t0 hc ht a b L L' hL hL' h0
  exact isVacuum_thetaIntertwiner_selfDual D cc dl t0 hc ht hL (sd_stdL D b) hL hL'
    (isVacuum_thetaIntertwiner_selfDual D cc dl t0 hc ht (sd_stdL D a) (sd_stdL D b) hL (sd_stdL D b) h0)

end GlobalTheory.MovedVacuum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KoszulResolutionThreeTermsExact
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Koszul

noncomputable def pairEquiv (g : ℕ) : {z : Sym2 (Fin g) // ¬ z.IsDiag} ≃ Fin (g.choose 2) :=
  Fintype.equivFinOfCardEq (by rw [Sym2.card_subtype_not_diag, Fintype.card_fin])

variable {O : Type} [CommRing O] {g : ℕ}

noncomputable def upper (x : Fin (g.choose 2) → O) : Matrix (Fin g) (Fin g) O :=
  fun i j => if h : i < j then
    x (pairEquiv g ⟨s(i, j), by rw [Sym2.mk_isDiag_iff]; exact h.ne⟩) else 0

noncomputable def skew (x : Fin (g.choose 2) → O) : Matrix (Fin g) (Fin g) O :=
  fun i j => upper x i j - upper x j i

lemma upper_add (x x' : Fin (g.choose 2) → O) : upper (x + x') = upper x + upper x' := by
  ext i j; simp only [upper, Matrix.add_apply]; split_ifs <;> simp

lemma upper_smul (a : O) (x : Fin (g.choose 2) → O) : upper (a • x) = a • upper x := by
  ext i j; simp only [upper, Matrix.smul_apply]; split_ifs <;> simp

lemma skew_add (x x' : Fin (g.choose 2) → O) : skew (x + x') = skew x + skew x' := by
  ext i j; simp only [skew, upper_add, Matrix.add_apply]; ring

lemma skew_smul (a : O) (x : Fin (g.choose 2) → O) : skew (a • x) = a • skew x := by
  ext i j; simp only [skew, upper_smul, Matrix.smul_apply, smul_eq_mul]; ring

noncomputable def d₂ (f : Fin g → O) : (Fin (g.choose 2) → O) →ₗ[O] (Fin g → O) where
  toFun x := (skew x).mulVec f
  map_add' x x' := by rw [skew_add, Matrix.add_mulVec]
  map_smul' a x := by
    rw [skew_smul]; ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

lemma d₂_apply (f : Fin g → O) (x : Fin (g.choose 2) → O) : d₂ f x = (skew x).mulVec f := rfl

lemma sum_skew_mulVec (f : Fin g → O) (x : Fin (g.choose 2) → O) :
    ∑ i, (skew x).mulVec f i * f i = 0 := by
  simp only [Matrix.mulVec, dotProduct, skew, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [sub_eq_zero, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma exists_skew_eq (c : Matrix (Fin g) (Fin g) O) (hd : ∀ i, c i i = 0)
    (hs : ∀ i j, c i j = - c j i) : ∃ x : Fin (g.choose 2) → O, skew x = c := by
  let F : Sym2 (Fin g) → O :=
    Sym2.lift ⟨fun i j => c (min i j) (max i j), fun i j => show c (min i j) (max i j) = c (min j i) (max j i) by rw [min_comm, max_comm]⟩
  refine ⟨fun k => F ((pairEquiv g).symm k).1, ?_⟩
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [skew, upper, h, lt_asymm h, F, min_eq_left h.le, max_eq_right h.le]
  · simp [skew, upper, hd]
  · simp [skew, upper, h, lt_asymm h, F, min_eq_left h.le, max_eq_right h.le, ← hs i j]

end GlobalTheory.Koszul


open GlobalTheory.Koszul in
theorem GlobalTheory.koszul_resolution_three_terms : ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∃ (e₁ : (Fin g → O) →ₗ[O] O) (e₂ : (Fin (g.choose 2) → O) →ₗ[O] (Fin g → O)), Function.Exact e₁ (Ideal.span (Set.range f)).mkQ ∧ Function.Exact e₂ e₁ ∧ (∀ x, e₁ x ∈ Ideal.span (Set.range f)) ∧ ∀ x i, e₂ x i ∈ Ideal.span (Set.range f) := by
  intro O _ g f hreg
  refine ⟨Fintype.linearCombination O f, d₂ f, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Fintype.range_linearCombination]
  · intro y
    constructor
    · intro hy
      rw [Fintype.linearCombination_apply] at hy
      obtain ⟨c, hd, hs, rfl⟩ := _root_.GlobalTheory.weaklyRegular_relations_koszul O g f hreg y (by simpa [smul_eq_mul] using hy)
      obtain ⟨x, hx⟩ := exists_skew_eq c hd hs
      exact ⟨x, by rw [d₂_apply, hx]⟩
    · rintro ⟨x, rfl⟩
      rw [Fintype.linearCombination_apply, d₂_apply]
      simpa [smul_eq_mul] using sum_skew_mulVec f x
  · intro x
    show _ ∈ Submodule.span O (Set.range f)
    rw [← Fintype.range_linearCombination]
    exact LinearMap.mem_range_self _ x
  · intro x i
    rw [d₂_apply]
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))
end

