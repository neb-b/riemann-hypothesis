module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjHom
section
set_option maxSynthPendingDepth 1

open AlgebraicGeometry CategoryTheory Limits Opposite HomogeneousLocalization

namespace GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjHom

variable {X : Scheme.{u}}

lemma specCorr_comp {Y : Scheme.{u}} {R S : CommRingCat.{u}} (a : Y ⟶ Spec S) (φ : R ⟶ S) :
    (Scheme.ΓSpecIso R).inv ≫ (a ≫ Spec.map φ).appTop =
      φ ≫ (Scheme.ΓSpecIso S).inv ≫ a.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

def toSpecAway (x : Γ(X, ⊤)) : (X.basicOpen x).toScheme ⟶ Spec (.of (Localization.Away x)) :=
  ((X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫ X.toSpecΓ ∣_ (PrimeSpectrum.basicOpen x)) ≫
    (basicOpenIsoSpecAway x).hom

lemma toSpecAway_SpecMap (x : Γ(X, ⊤)) :
    toSpecAway x ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x))) =
      (X.basicOpen x).ι ≫ X.toSpecΓ := by
  simp only [toSpecAway, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  have h1 := morphismRestrict_ι X.toSpecΓ (PrimeSpectrum.basicOpen x)
  calc _ = (X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫
        (X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen x).ι ≫ X.toSpecΓ := by
          congr 1
    _ = _ := Scheme.isoOfEq_inv_ι_assoc _ _ _

lemma specCorr_toSpecAway (x : Γ(X, ⊤)) :
    CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x)) ≫ (Scheme.ΓSpecIso _).inv ≫
      (toSpecAway x).appTop = (X.basicOpen x).ι.appTop := by
  rw [← specCorr_comp, toSpecAway_SpecMap, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  exact Iso.inv_hom_id_assoc _ _

lemma specCorr_toSpecAway_apply (x : Γ(X, ⊤)) (z : Γ(X, ⊤)) :
    ((Scheme.ΓSpecIso _).inv ≫ (toSpecAway x).appTop) (algebraMap Γ(X, ⊤) (Localization.Away x) z) =
      (X.basicOpen x).ι.appTop z := by
  rw [← specCorr_toSpecAway x, ConcreteCategory.comp_apply]
  rfl

def corr (g : X ⟶ Proj 𝒜) (r : A) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ Proj.basicOpen 𝒜 r) :
    CommRingCat.of (Away 𝒜 r) ⟶ Γ(V, ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫ (g.resLE _ V h ≫ Proj.basicOpenToSpec 𝒜 r).appTop

variable (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)

lemma corr_fromOfGlobalSections {r : A} {d : ℕ} (hd : 0 < d) (hr : r ∈ 𝒜 d) (k : ℕ) (a : A)
    (ha : a ∈ 𝒜 (k • d)) :
    corr 𝒜 (Proj.fromOfGlobalSections 𝒜 f hf) r (X.basicOpen (f r))
      (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf hd hr).ge (Away.mk 𝒜 hr k a ha) *
      (X.basicOpen (f r)).ι.appTop (f r) ^ k = (X.basicOpen (f r)).ι.appTop (f a) := by
  rw [corr, Proj.fromOfGlobalSections_resLE 𝒜 f hf hd hr, Proj.toBasicOpenOfGlobalSections]
  simp only [Category.assoc, ← Proj.basicOpenIsoSpec_hom 𝒜 r hr hd, Iso.inv_hom_id,
    Category.comp_id]
  simp only [← Category.assoc]
  rw [specCorr_comp]
  change ((CommRingCat.ofHom _ ≫ (Scheme.ΓSpecIso _).inv ≫ (toSpecAway (f r)).appTop) _) * _ = _
  rw [← specCorr_toSpecAway_apply, ← specCorr_toSpecAway_apply, ← map_pow]
  rw [ConcreteCategory.comp_apply (CommRingCat.ofHom _), ← map_mul]
  congr 1
  simp only [CommRingCat.hom_ofHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk']
  rw [← map_pow, ← map_pow f]
  exact IsLocalization.mk'_spec (Localization.Away (f r)) (f a) _

lemma corr_fromOfGlobalSections' {r : A} {d : ℕ} (hd : 0 < d) (hr : r ∈ 𝒜 d) (V : X.Opens)
    (hV : X.basicOpen (f r) = V) (h : V ≤ Proj.fromOfGlobalSections 𝒜 f hf ⁻¹ᵁ Proj.basicOpen 𝒜 r)
    (k : ℕ) (a : A) (ha : a ∈ 𝒜 (k • d)) :
    corr 𝒜 (Proj.fromOfGlobalSections 𝒜 f hf) r V h (Away.mk 𝒜 hr k a ha) *
      V.ι.appTop (f r) ^ k = V.ι.appTop (f a) := by
  subst hV
  exact corr_fromOfGlobalSections 𝒜 f hf hd hr k a ha

lemma corr_comp {Y : Scheme.{u}} (h : Y ⟶ X) (g : X ⟶ Proj 𝒜) (r : A) {V : X.Opens}
    {W : Y.Opens} (hV : V ≤ g ⁻¹ᵁ Proj.basicOpen 𝒜 r) (hW : W ≤ h ⁻¹ᵁ V) :
    corr 𝒜 (h ≫ g) r W (hW.trans ((TopologicalSpace.Opens.map h.base).map (homOfLE hV)).le) =
      corr 𝒜 g r V hV ≫ (h.resLE V W hW).appTop := by
  rw [corr, corr, ← Scheme.Hom.resLE_comp_resLE, Category.assoc, Scheme.Hom.comp_appTop,
    Category.assoc]


set_option backward.isDefEq.respectTransparency false in
lemma isUnit_of_basicOpen_eq_top {Y : Scheme.{u}} (s : Γ(Y, ⊤)) (h : Y.basicOpen s = ⊤) :
    IsUnit s := by
  have hu : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op s) :=
    Y.toRingedSpace.isUnit_res_basicOpen s
  convert! (Y.presheaf.map (eqToHom h.symm).op).hom.isUnit_map hu
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  have : (homOfLE (Y.basicOpen_le s)).op ≫ (eqToHom h.symm).op = 𝟙 (op ⊤) :=
    Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

lemma isUnit_ι_appTop (x : Γ(X, ⊤)) : IsUnit ((X.basicOpen x).ι.appTop x) := by
  apply isUnit_of_basicOpen_eq_top
  change ((X.basicOpen x).toScheme).basicOpen ((X.basicOpen x).ι.app ⊤ x) = ⊤
  rw [← Scheme.preimage_basicOpen]
  exact Scheme.Opens.ι_preimage_self _

lemma mul_pow_cancel {R : Type*} [CommRing R] {v u w c : R} (hc : IsUnit c) (k d : ℕ)
    (h : v * (c ^ d * u) ^ k = c ^ (k • d) * w) : v * u ^ k = w := by
  apply (hc.pow (k * d)).mul_right_injective
  simp only [smul_eq_mul] at h
  calc c ^ (k * d) * (v * u ^ k) = v * (c ^ d * u) ^ k := by ring
    _ = c ^ (k * d) * w := h

lemma mul_pow_cancel' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {v : S}
    {u u' w w' c : R} (hc : IsUnit c) (k d : ℕ) (hu : u' = c ^ d * u) (hw : w' = c ^ (k • d) * w)
    (h : v * φ u' ^ k = φ w') : v * φ u ^ k = φ w := by
  subst hu hw
  rw [map_mul, map_mul, map_pow, map_pow] at h
  exact mul_pow_cancel (hc.map φ) k d h

lemma transfer {R S : CommRingCat.{u}} (ρ : R ⟶ S) {v x y : R} {x' y' : S} (hx : ρ x = x')
    (hy : ρ y = y') (k : ℕ) (h : v * x ^ k = y) : ρ v * x' ^ k = y' := by
  subst hx hy
  rw [← map_pow, ← map_mul, h]

theorem hom_ext {ι : Type*} (r : ι → A) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (hr : ∀ i, r i ∈ 𝒜 (d i)) (hcov : ⨆ i, Proj.basicOpen 𝒜 (r i) = ⊤) {g g' : X ⟶ Proj 𝒜}
    (V : ι → X.Opens) (hV : ∀ i, g ⁻¹ᵁ Proj.basicOpen 𝒜 (r i) = V i)
    (hV' : ∀ i, g' ⁻¹ᵁ Proj.basicOpen 𝒜 (r i) = V i)
    (hc : ∀ i, corr 𝒜 g (r i) (V i) (hV i).ge = corr 𝒜 g' (r i) (V i) (hV' i).ge) : g = g' := by
  have hVcov : ⨆ i, V i = ⊤ := by
    simp_rw [← hV]
    rw [← Scheme.Hom.preimage_iSup, hcov]
    rfl
  refine (X.openCoverOfIsOpenCover V hVcov).hom_ext _ _ fun i => ?_
  have h1 : g.resLE _ (V i) (hV i).ge ≫ Proj.basicOpenToSpec 𝒜 (r i) =
      g'.resLE _ (V i) (hV' i).ge ≫ Proj.basicOpenToSpec 𝒜 (r i) := ext_to_Spec (hc i)
  have : IsIso (Proj.basicOpenToSpec 𝒜 (r i)) := by
    rw [← Proj.basicOpenIsoSpec_hom 𝒜 (r i) (hr i) (hd i)]
    infer_instance
  have h2 := (cancel_mono _).1 h1
  change (V i).ι ≫ g = (V i).ι ≫ g'
  rw [← Scheme.Hom.resLE_comp_ι g (hV i).ge, ← Scheme.Hom.resLE_comp_ι g' (hV' i).ge, h2]


variable {𝒜} in
theorem eq_fromOfGlobalSections {ι : Type*} (r : ι → A) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (hr : ∀ i, r i ∈ 𝒜 (d i)) (hcov : ⨆ i, Proj.basicOpen 𝒜 (r i) = ⊤) (g : X ⟶ Proj 𝒜)
    (hg : ∀ i, g ⁻¹ᵁ Proj.basicOpen 𝒜 (r i) = X.basicOpen (f (r i)))
    (hc : ∀ i k a (ha : a ∈ 𝒜 (k • d i)),
      corr 𝒜 g (r i) _ (hg i).ge (Away.mk 𝒜 (hr i) k a ha) *
        (X.basicOpen (f (r i))).ι.appTop (f (r i)) ^ k =
        (X.basicOpen (f (r i))).ι.appTop (f a)) :
    g = Proj.fromOfGlobalSections 𝒜 f hf := by
  refine hom_ext 𝒜 r d hd hr hcov (fun i => X.basicOpen (f (r i))) hg
    (fun i => Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf (hd i) (hr i)) fun i => ?_
  ext y
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (hr i) y
  exact ((isUnit_ι_appTop (f (r i))).pow k).mul_left_injective
    ((hc i k a ha).trans (corr_fromOfGlobalSections 𝒜 f hf (hd i) (hr i) k a ha).symm)


variable {𝒜} in
theorem comp_fromOfGlobalSections {ι : Type*} (r : ι → A) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (hr : ∀ i, r i ∈ 𝒜 (d i)) (hcov : ⨆ i, Proj.basicOpen 𝒜 (r i) = ⊤) {Y : Scheme.{u}}
    (h : Y ⟶ X) :
    h ≫ Proj.fromOfGlobalSections 𝒜 f hf = Proj.fromOfGlobalSections 𝒜 (h.appTop.hom.comp f)
      (by rw [← Ideal.map_map, hf, Ideal.map_top]) := by
  have hpreX : ∀ i, h ⁻¹ᵁ X.basicOpen (f (r i)) = Y.basicOpen ((h.appTop.hom.comp f) (r i)) :=
    fun i => Scheme.preimage_basicOpen h (f (r i))
  have hpre : ∀ i, (h ≫ Proj.fromOfGlobalSections 𝒜 f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 (r i) =
      Y.basicOpen ((h.appTop.hom.comp f) (r i)) := fun i => by
    rw [Scheme.Hom.comp_preimage, Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf (hd i) (hr i),
      hpreX]
  refine eq_fromOfGlobalSections _ _ r d hd hr hcov _ hpre fun i k a ha => ?_
  have hW := (hpreX i).ge
  have hι : ∀ z, (h.resLE _ _ hW).appTop ((X.basicOpen (f (r i))).ι.appTop (f z)) =
      (Y.basicOpen ((h.appTop.hom.comp f) (r i))).ι.appTop ((h.appTop.hom.comp f) z) := fun z => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
    rfl
  rw [corr_comp 𝒜 h _ (r i) (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf (hd i) (hr i)).ge hW,
    ConcreteCategory.comp_apply]
  exact transfer _ (hι _) (hι _) k (corr_fromOfGlobalSections 𝒜 f hf (hd i) (hr i) k a ha)


variable {𝒜} in
theorem fromOfGlobalSections_eq_of_twist {ι : Type*} (r : ι → A) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (hr : ∀ i, r i ∈ 𝒜 (d i)) (hcov : ⨆ i, Proj.basicOpen 𝒜 (r i) = ⊤)
    (f' : A →+* Γ(X, ⊤)) (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f' = ⊤)
    (c : Γ(X, ⊤)) (hc : IsUnit c) (hff' : ∀ m a, a ∈ 𝒜 m → f' a = c ^ m * f a) :
    Proj.fromOfGlobalSections 𝒜 f' hf' = Proj.fromOfGlobalSections 𝒜 f hf := by
  have hb : ∀ i, X.basicOpen (f' (r i)) = X.basicOpen (f (r i)) := fun i => by
    rw [hff' _ _ (hr i), Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (hc.pow _), top_inf_eq]
  refine eq_fromOfGlobalSections _ _ r d hd hr hcov _
    (fun i => (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f' hf' (hd i) (hr i)).trans (hb i))
    fun i k a ha => ?_
  have hle : X.basicOpen (f (r i)) ≤
      Proj.fromOfGlobalSections 𝒜 f' hf' ⁻¹ᵁ Proj.basicOpen 𝒜 (r i) :=
    ((Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f' hf' (hd i) (hr i)).trans (hb i)).ge
  exact mul_pow_cancel' (X.basicOpen (f (r i))).ι.appTop.hom hc k (d i) (hff' _ _ (hr i))
    (hff' _ _ ha) (corr_fromOfGlobalSections' 𝒜 f' hf' (hd i) (hr i) _ (hb i) hle k a ha)

end ProjHom
end
end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RestrictTensor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory TensorProduct

universe u

noncomputable section

namespace RestrictTensor

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) (U : X.Opens)

def ringInv : Γ(X, U) →+* Γ(Y, f ''ᵁ U) := (f.appIso U).inv.hom

def ringHom : Γ(Y, f ''ᵁ U) →+* Γ(X, U) := (f.appIso U).hom.hom

lemma ringInv_ringHom (r : Γ(Y, f ''ᵁ U)) : ringInv f U (ringHom f U r) = r := by
  change (f.appIso U).inv ((f.appIso U).hom r) = r
  exact (f.appIso U).hom_inv_id_apply r

def sec : ((preMod X).obj (M.restrict f)).obj (op U) →+ ((preMod Y).obj M).obj (op (f ''ᵁ U)) :=
  AddMonoidHom.id _

lemma sec_smul (r : Γ(X, U)) (m : ((preMod X).obj (M.restrict f)).obj (op U)) :
    sec f M U (r • m) = ringInv f U r • sec f M U m := rfl

def sec' : ((preMod Y).obj M).obj (op (f ''ᵁ U)) →+ ((preMod X).obj (M.restrict f)).obj (op U) :=
  AddMonoidHom.id _

lemma sec'_smul (r : Γ(Y, f ''ᵁ U)) (m : ((preMod Y).obj M).obj (op (f ''ᵁ U))) :
    sec' f M U (r • m) = ringHom f U r • sec' f M U m := by
  change r • m = ringInv f U (ringHom f U r) • m
  rw [ringInv_ringHom]

def toImage :
    ((preMod X).obj (M.restrict f)).obj (op U) ⊗[Γ(X, U)]
      ((preMod X).obj (N.restrict f)).obj (op U) →+
      ((preMod Y).obj M).obj (op (f ''ᵁ U)) ⊗[Γ(Y, f ''ᵁ U)]
        ((preMod Y).obj N).obj (op (f ''ᵁ U)) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n => sec f M U m ⊗ₜ sec f N U n)
      (fun a b => by rw [map_add (f := _), tmul_add]))
      (fun a b => by ext n; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add (f := _),
        add_tmul]))
    (fun r m n => by
      simp only [AddMonoidHom.mk'_apply, sec_smul]
      exact smul_tmul _ _ _)

lemma toImage_tmul (m : ((preMod X).obj (M.restrict f)).obj (op U))
    (n : ((preMod X).obj (N.restrict f)).obj (op U)) :
    toImage f M N U (m ⊗ₜ n) = sec f M U m ⊗ₜ sec f N U n := rfl

def ofImage :
    ((preMod Y).obj M).obj (op (f ''ᵁ U)) ⊗[Γ(Y, f ''ᵁ U)]
      ((preMod Y).obj N).obj (op (f ''ᵁ U)) →+
      ((preMod X).obj (M.restrict f)).obj (op U) ⊗[Γ(X, U)]
        ((preMod X).obj (N.restrict f)).obj (op U) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n => sec' f M U m ⊗ₜ sec' f N U n)
      (fun a b => by rw [map_add (f := _), tmul_add]))
      (fun a b => by ext n; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add (f := _),
        add_tmul]))
    (fun r m n => by
      simp only [AddMonoidHom.mk'_apply, sec'_smul]
      exact smul_tmul _ _ _)

lemma ofImage_toImage (z : ((preMod X).obj (M.restrict f)).obj (op U) ⊗[Γ(X, U)]
    ((preMod X).obj (N.restrict f)).obj (op U)) : ofImage f M N U (toImage f M N U z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul m n => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

lemma toImage_ofImage (z : ((preMod Y).obj M).obj (op (f ''ᵁ U)) ⊗[Γ(Y, f ''ᵁ U)]
    ((preMod Y).obj N).obj (op (f ''ᵁ U))) : toImage f M N U (ofImage f M N U z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul m n => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

lemma toImage_smul (r : Γ(X, U)) (z : ((preMod X).obj (M.restrict f)).obj (op U) ⊗[Γ(X, U)]
    ((preMod X).obj (N.restrict f)).obj (op U)) :
    toImage f M N U (r • z) = ringInv f U r • toImage f M N U z := by
  induction z using TensorProduct.inductionOn with
  | tmul m n =>
    rw [TensorProduct.smul_tmul', toImage_tmul, toImage_tmul, sec_smul, TensorProduct.smul_tmul']
  | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]

def compApp : ((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).obj (op U) →+
    ((preMod X).obj ((M ⊗ N).restrict f)).obj (op U) :=
  (sec' f (M ⊗ N) U).comp (((tensorToSheaf M N).app (op (f ''ᵁ U))).hom.toAddMonoidHom.comp
    (toImage f M N U))

lemma compApp_smul (r : Γ(X, U))
    (z : ((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).obj (op U)) :
    compApp f M N U (r • z) = r • compApp f M N U z := by
  change sec' f (M ⊗ N) U ((tensorToSheaf M N).app (op (f ''ᵁ U)) (toImage f M N U (r • z))) =
    sec' f (M ⊗ N) U (ringInv f U r • (tensorToSheaf M N).app (op (f ''ᵁ U)) (toImage f M N U z))
  exact congrArg (sec' f (M ⊗ N) U) ((congrArg ((tensorToSheaf M N).app (op (f ''ᵁ U))).hom
    (toImage_smul f M N U r z)).trans
      (((tensorToSheaf M N).app (op (f ''ᵁ U))).hom.map_smul (ringInv f U r) (toImage f M N U z)))

def comp : (preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f) ⟶
    (preMod X).obj ((M ⊗ N).restrict f) :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (compApp f M N U.unop)
      naturality := fun U V g => by
        ext z
        let L := (compApp f M N V.unop).comp (((preMod X).obj (M.restrict f) ⊗
          (preMod X).obj (N.restrict f)).map g).hom.toAddMonoidHom
        let R := (((preMod X).obj ((M ⊗ N).restrict f)).map g).hom.toAddMonoidHom.comp
          (compApp f M N U.unop)
        change L z = R z
        induction z using TensorProduct.inductionOn with
        | tmul m n =>
          exact PresheafOfModules.naturality_apply (tensorToSheaf M N)
            (f.opensFunctor.map g.unop).op (sec f M U.unop m ⊗ₜ sec f N U.unop n)
        | add a b ha hb =>
          exact (map_add L a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add R a b).symm) }
    (fun U r z => compApp_smul f M N U.unop r z)

lemma toImage_map {U V : X.Opens} (h : V ≤ U)
    (z : ((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).obj (op U)) :
    toImage f M N V (((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).map
      (homOfLE h).op z) =
      (((preMod Y).obj M ⊗ (preMod Y).obj N).map (homOfLE (f.image_mono h)).op (toImage f M N U z)) := by
  let L := (toImage f M N V).comp (((preMod X).obj (M.restrict f) ⊗
    (preMod X).obj (N.restrict f)).map (homOfLE h).op).hom.toAddMonoidHom
  let R := (((preMod Y).obj M ⊗ (preMod Y).obj N).map
    (homOfLE (f.image_mono h)).op).hom.toAddMonoidHom.comp (toImage f M N U)
  change L z = R z
  induction z using TensorProduct.inductionOn with
  | tmul m n => rfl
  | add a b ha hb => exact (map_add L a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add R a b).symm)

lemma W_comp : ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj (comp f M N) := by
  obtain ⟨hT₁, hT₂⟩ := (ModulesTensor.W_toPresheaf_iff (tensorToSheaf M N)).1 (W_tensorToSheaf M N)
  rw [ModulesTensor.W, MorphismProperty.inverseImage_iff, ModulesTensor.W_toPresheaf_iff]
  constructor
  · intro U z hz
    have h0 : (tensorToSheaf M N).app (op (f ''ᵁ U.unop)) (toImage f M N U.unop z) = 0 := hz
    have hS := hT₁ (op (f ''ᵁ U.unop)) _ h0
    rw [Opens.mem_grothendieckTopology] at hS ⊢
    intro x hx
    obtain ⟨W', i, hi, hxW'⟩ := hS (f x) ⟨x, hx, rfl⟩
    have hVU : f ⁻¹ᵁ W' ≤ U.unop := by
      rw [← f.preimage_image_eq U.unop]
      exact f.preimage_mono i.le
    refine ⟨f ⁻¹ᵁ W', homOfLE hVU, ?_, hxW'⟩
    have hi' : ((preMod Y).obj M ⊗ (preMod Y).obj N).map (homOfLE (f.image_mono hVU)).op
        (toImage f M N U.unop z) = 0 :=
      (ModulesTensor.zeroSieve _).downward_closed hi (homOfLE (f.image_preimage_le W'))
    change (((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)).map
      (homOfLE hVU).op z) = 0
    rw [← ofImage_toImage f M N (f ⁻¹ᵁ W') (((preMod X).obj (M.restrict f) ⊗
      (preMod X).obj (N.restrict f)).map (homOfLE hVU).op z), toImage_map]
    erw [hi', map_zero]
    rfl
  · intro U y
    have hS := hT₂ (op (f ''ᵁ U.unop)) y
    rw [Opens.mem_grothendieckTopology] at hS ⊢
    intro x hx
    obtain ⟨W', i, hi, hxW'⟩ := hS (f x) ⟨x, hx, rfl⟩
    have hVU : f ⁻¹ᵁ W' ≤ U.unop := by
      rw [← f.preimage_image_eq U.unop]
      exact f.preimage_mono i.le
    refine ⟨f ⁻¹ᵁ W', homOfLE hVU, ?_, hxW'⟩
    obtain ⟨w, hw⟩ := (ModulesTensor.imSieve _ _).downward_closed hi
      (homOfLE (f.image_preimage_le W'))
    refine ⟨ofImage f M N (f ⁻¹ᵁ W') w, ?_⟩
    change sec' f (M ⊗ N) _ ((tensorToSheaf M N).app _
      (toImage f M N (f ⁻¹ᵁ W') (ofImage f M N (f ⁻¹ᵁ W') w))) = _
    erw [toImage_ofImage]
    exact hw

def sheafifyIso : (sheafifyMod X).obj ((preMod X).obj (M.restrict f) ⊗ (preMod X).obj (N.restrict f)) ≅
    (M ⊗ N).restrict f :=
  haveI : IsIso ((sheafifyMod X).map (comp f M N)) :=
    Localization.inverts (modulesSheafification (Opens.grothendieckTopology X) X.sheaf)
      (ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj) _ (W_comp f M N)
  asIso ((sheafifyMod X).map (comp f M N)) ≪≫ asIso ((sheafifyModAdj X).counit.app _)

end RestrictTensor


open RestrictTensor in
def restrictTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (M ⊗ N).restrict f ≅ M.restrict f ⊗ N.restrict f :=
  (sheafifyIso f M N).symm ≪≫ tensorIso (M.restrict f) (N.restrict f)


attribute [local instance] MvPolynomial.gradedAlgebra in
def restrictTwistIso {A : Type u} [CommRing A] {n : ℕ} {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] (i : X ⟶ projectiveSpace A n) (G : X.Modules) (k : ℤ) :
    ProjScheme.twist (f ≫ i) (G.restrict f) k ≅ (ProjScheme.twist i G k).restrict f :=
  (whiskerLeftIso (G.restrict f)
    (((Scheme.Modules.pullbackComp f i).app _).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback f).app _).symm)) ≪≫
    (restrictTensorIso f G (ProjScheme.twistingSheaf i k)).symm

end

end GroundTheory.Arith.SchemeCoh
end

