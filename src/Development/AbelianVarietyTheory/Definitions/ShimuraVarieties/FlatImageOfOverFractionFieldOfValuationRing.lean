module

public import Mathlib

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace GlobalTheory

noncomputable section

section Dominant

variable {T' T P : Scheme.{u}}

theorem ker_comp_of_schemeDominant (d : T' ⟶ T) (t : T ⟶ P) [IsSchemeTheoreticallyDominant d] :
    (d ≫ t).ker = t.ker := by
  rw [Scheme.Hom.ker_comp, d.ker_eq_bot, Scheme.IdealSheafData.map_bot]

theorem schemeDominant_of_comp (d : T' ⟶ T) (t : T ⟶ P) [IsSchemeTheoreticallyDominant (d ≫ t)] :
    IsSchemeTheoreticallyDominant t :=
  ⟨le_bot_iff.mp ((d.le_ker_comp t).trans (d ≫ t).ker_eq_bot.le)⟩

theorem schemeDominant_specMap_iff {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    IsSchemeTheoreticallyDominant (Spec.map φ) ↔ Function.Injective φ.hom := by
  have e : φ = (Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso R').hom := by
    simp
  constructor
  · intro h
    rw [e]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R').hom).1.comp
      (((Spec.map φ).app_injective ⊤).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).1)
  · intro h
    have e' : (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso R').inv := by
      simp
    have hi : Function.Injective (Spec.map φ).appTop.hom := by
      rw [e']
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R').inv).1.comp
        (h.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1)
    refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
    rw [Scheme.Hom.ker_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hi

theorem isIso_of_isClosedImmersion_of_schemeDominant (i : T ⟶ P) [IsClosedImmersion i]
    [IsSchemeTheoreticallyDominant i] : IsIso i :=
  IsClosedImmersion.isIso_of_ker_eq i (𝟙 P) i (by simp) (by simp [i.ker_eq_bot])

theorem isIntegral_of_schemeDominant (d : T' ⟶ T) [IsSchemeTheoreticallyDominant d]
    [QuasiCompact d] [IsIntegral T'] : IsIntegral T := by
  have : IsReduced T := IsSchemeTheoreticallyDominant.isReduced d
  have h : IsIrreducible (closure (Set.range d)) := by
    rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ T').image _ d.continuous.continuousOn).closure
  rw [d.denseRange.closure_range] at h
  have : IrreducibleSpace T := (irreducibleSpace_def T).mpr h
  exact isIntegral_of_irreducibleSpace_of_isReduced T


set_option backward.isDefEq.respectTransparency false in
theorem eq_zero_of_mul_eq_zero_of_flat {S : Scheme.{u}} [IsAffine S] (s : T ⟶ S) [Flat s]
    (V : T.Opens) (r : Γ(S, ⊤)) (hr : r ∈ nonZeroDivisors Γ(S, ⊤)) (a : Γ(T, V))
    (h : s.appLE ⊤ V le_top r * a = 0) : a = 0 := by
  refine T.IsSheaf.section_ext fun x hx ↦ ?_
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV, hVV : V' ≤ V⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  refine ⟨V', hVV, hxV, ?_⟩
  have hf : (s.appLE ⊤ V' le_top).hom.Flat := s.flat_appLE (isAffineOpen_top S) hV' le_top
  let := (s.appLE ⊤ V' le_top).hom.toAlgebra
  have : Module.Flat Γ(S, ⊤) Γ(T, V') := hf
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(T, V')) hr
  have he : V ≤ s ⁻¹ᵁ ⊤ := by rw [s.preimage_top]; exact le_top
  have h' := congrArg (T.presheaf.map (homOfLE hVV).op)
    (show s.appLE ⊤ V he r * a = 0 from h)
  rw [map_mul, map_zero, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at h'
  simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h'


set_option backward.isDefEq.respectTransparency false in
theorem flat_of_schemeDominant_of_torsionFree_flat {O : CommRingCat.{u}}
    (hO : ∀ (M : Type u) [AddCommGroup M] [Module O M],
      Submodule.torsion O M = ⊥ → Module.Flat O M)
    (d : T' ⟶ T) (s : T ⟶ Spec O) [IsSchemeTheoreticallyDominant d] [QuasiCompact d]
    [Flat (d ≫ s)] : Flat s := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : T.affineOpens ↦ U)
    (iSup_affineOpens_eq_top T) fun U ↦ ?_
  rw [← RingHom.Flat.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso O).inv]
  let := ((s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso O).inv.hom).toAlgebra
  refine hO Γ(T, U) ?_
  rw [eq_bot_iff]
  rintro a ⟨⟨r, hr⟩, ha⟩
  have hr' : (Scheme.ΓSpecIso O).inv r ∈ nonZeroDivisors Γ(Spec O, ⊤) := by
    have := (MulEquivClass.map_nonZeroDivisors
      (Scheme.ΓSpecIso O).symm.commRingCatIsoToRingEquiv)
    rw [← this]
    exact ⟨r, hr, rfl⟩
  have he : (U : T.Opens) ≤ s ⁻¹ᵁ ⊤ := by rw [s.preimage_top]; exact le_top
  have ha' : s.appLE ⊤ U he ((Scheme.ΓSpecIso O).inv r) * a = 0 := ha
  have h0 : d.app U a = 0 := by
    refine eq_zero_of_mul_eq_zero_of_flat (d ≫ s) (d ⁻¹ᵁ U) _ hr' _ ?_
    have := congrArg (d.app U) ha'
    rw [map_mul, map_zero, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE] at this
    rw [Scheme.Hom.app_eq_appLE]
    exact this
  exact (d.app_injective U) (h0.trans (map_zero _).symm)

theorem flat_of_schemeDominant_of_isDedekindDomain {O : CommRingCat.{u}} [IsDedekindDomain O]
    (d : T' ⟶ T) (s : T ⟶ Spec O) [IsSchemeTheoreticallyDominant d] [QuasiCompact d]
    [Flat (d ≫ s)] : Flat s :=
  flat_of_schemeDominant_of_torsionFree_flat
    (fun _ _ _ ↦ IsDedekindDomain.flat_iff_torsion_eq_bot.mpr) d s

theorem flat_specMap_localization {O : Type u} [CommRing O] (M : Submonoid O) (K : Type u)
    [CommRing K] [Algebra O K] [IsLocalization M K] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K M)

theorem mono_specMap_localization {O : Type u} [CommRing O] (M : Submonoid O) (K : Type u)
    [CommRing K] [Algebra O K] [IsLocalization M K] :
    Mono (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
  have := IsPreimmersion.of_isLocalization (R := O) (S := K) M
  infer_instance

theorem flat_of_over_fractionField {O K : Type u} [CommRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (s : T ⟶ Spec (.of O)) (s' : T ⟶ Spec (.of K))
    (h : s' ≫ Spec.map (CommRingCat.ofHom (algebraMap O K)) = s) : Flat s := by
  have := flat_specMap_localization (nonZeroDivisors O) K
  rw [← h]
  infer_instance

end Dominant

section Closure

variable {W P T' T Z : Scheme.{u}} (j : W ⟶ P)

theorem ker_le_ker_of_schemeDominant (t : T ⟶ P) (d : T' ⟶ T) [IsSchemeTheoreticallyDominant d]
    (w : T' ⟶ W) (h : d ≫ t = w ≫ j) : j.ker ≤ t.ker := by
  rw [← ker_comp_of_schemeDominant d t, h]
  exact w.le_ker_comp j

def closureLift (t : T ⟶ P) (d : T' ⟶ T) [IsSchemeTheoreticallyDominant d]
    (w : T' ⟶ W) (h : d ≫ t = w ≫ j) : T ⟶ j.image :=
  IsClosedImmersion.lift j.imageι t
    (by simpa using ker_le_ker_of_schemeDominant j t d w h)

@[reassoc (attr := simp)]
theorem closureLift_imageι (t : T ⟶ P) (d : T' ⟶ T) [IsSchemeTheoreticallyDominant d]
    (w : T' ⟶ W) (h : d ≫ t = w ≫ j) : closureLift j t d w h ≫ j.imageι = t :=
  IsClosedImmersion.lift_fac _ _ _

theorem comp_closureLift (t : T ⟶ P) (d : T' ⟶ T) [IsSchemeTheoreticallyDominant d]
    (w : T' ⟶ W) (h : d ≫ t = w ≫ j) : d ≫ closureLift j t d w h = w ≫ j.toImage := by
  rw [← cancel_mono j.imageι]
  simp [h]

def closureToClosed (g : W ⟶ Z) (i : Z ⟶ P) [IsClosedImmersion i] (h : g ≫ i = j) :
    j.image ⟶ Z :=
  IsClosedImmersion.lift i j.imageι (by simpa [← h] using g.le_ker_comp i)

theorem closureToClosed_comp (g : W ⟶ Z) (i : Z ⟶ P) [IsClosedImmersion i] (h : g ≫ i = j) :
    closureToClosed j g i h ≫ i = j.imageι :=
  IsClosedImmersion.lift_fac _ _ _

theorem toImage_closureToClosed (g : W ⟶ Z) (i : Z ⟶ P) [IsClosedImmersion i] (h : g ≫ i = j) :
    j.toImage ≫ closureToClosed j g i h = g := by
  rw [← cancel_mono i, Category.assoc, closureToClosed_comp, j.toImage_imageι, h]

instance schemeDominant_toImage : IsSchemeTheoreticallyDominant j.toImage := by
  let c := closureToClosed j j.toImage.toImage (j.toImage.imageι ≫ j.imageι) (by simp)
  have hc : c ≫ j.toImage.imageι = 𝟙 _ := by
    rw [← cancel_mono j.imageι, Category.assoc, closureToClosed_comp, Category.id_comp]
  have : IsSchemeTheoreticallyDominant (c ≫ j.toImage.imageι) := by
    rw [hc]; infer_instance
  have := schemeDominant_of_comp c j.toImage.imageι
  exact ⟨by simpa using j.toImage.imageι.ker_eq_bot⟩

instance isIso_closureToClosed (g : W ⟶ Z) (i : Z ⟶ P) [IsClosedImmersion i]
    [IsSchemeTheoreticallyDominant g] (h : g ≫ i = j) : IsIso (closureToClosed j g i h) :=
  IsClosedImmersion.isIso_of_ker_eq j.imageι i _ (closureToClosed_comp j g i h)
    (by simp [← h, ker_comp_of_schemeDominant])

theorem isIso_imageι_iff : IsIso j.imageι ↔ IsSchemeTheoreticallyDominant j := by
  rw [Scheme.isIso_subschemeι_iff_eq_bot, isSchemeTheoreticallyDominant_iff]

theorem isOpenImmersion_toImage [IsImmersion j] [QuasiCompact j] : IsOpenImmersion j.toImage :=
  inferInstance

instance isReduced_image [QuasiCompact j] [IsReduced W] : IsReduced j.image :=
  IsSchemeTheoreticallyDominant.isReduced j.toImage

instance isIntegral_image [QuasiCompact j] [IsIntegral W] : IsIntegral j.image :=
  isIntegral_of_schemeDominant j.toImage

theorem flat_image_of_isDedekindDomain {O : CommRingCat.{u}} [IsDedekindDomain O]
    (s : P ⟶ Spec O) [QuasiCompact j] [Flat (j ≫ s)] : Flat (j.imageι ≫ s) :=
  have : Flat (j.toImage ≫ j.imageι ≫ s) := by simpa
  flat_of_schemeDominant_of_isDedekindDomain j.toImage _

theorem flat_image_of_over_fractionField {O K : Type u} [CommRing O] [IsDedekindDomain O]
    [Field K] [Algebra O K] [IsFractionRing O K] (s : P ⟶ Spec (.of O)) (s' : W ⟶ Spec (.of K))
    (h : s' ≫ Spec.map (CommRingCat.ofHom (algebraMap O K)) = j ≫ s) [QuasiCompact j] :
    Flat (j.imageι ≫ s) :=
  have := flat_of_over_fractionField (j ≫ s) s' h
  flat_image_of_isDedekindDomain j s

theorem ker_eq_comap_of_flat {W' P' : Scheme.{u}} {j' : W' ⟶ P'} {w : W' ⟶ W} {g : P' ⟶ P}
    (H : IsPullback j' w g j) [Flat g] [QuasiCompact j] : j'.ker = j.ker.comap g := by
  let e : W' ⟶ pullback g j.imageι := pullback.lift j' (w ≫ j.toImage) (by simpa using H.w)
  have he : e ≫ pullback.fst g j.imageι = j' := pullback.lift_fst _ _ _
  have He : IsPullback w e j.toImage (pullback.snd g j.imageι) := by
    refine (IsPullback.of_right (h₁₂ := pullback.fst g j.imageι) (h₂₂ := j.imageι) (v₁₃ := g)
      ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback g j.imageι)).flip
    rwa [he, j.toImage_imageι]
  have := IsSchemeTheoreticallyDominant.of_isPullback He
  rw [Scheme.IdealSheafData.comap, ← ker_comp_of_schemeDominant e, he]

theorem isPullback_toImage_of_isClosedImmersion {P' : Scheme.{u}} (c : W ⟶ P') (u : P' ⟶ P)
    [IsClosedImmersion c] [Flat u] [Mono u] (h : c ≫ u = j) [QuasiCompact j] :
    IsPullback c j.toImage u j.imageι := by
  have H : IsPullback c (𝟙 W) u j := by
    refine IsPullback.of_isLimit' ⟨by simpa using h⟩ (PullbackCone.IsLimit.mk _ (fun s ↦ s.snd)
      (fun s ↦ ?_) (fun s ↦ by simp) (fun s m _ h₂ ↦ by simpa using h₂))
    rw [← cancel_mono u, Category.assoc, h, s.condition]
  exact isPullback_of_isClosedImmersion _ _ _ _ (by simpa using h)
    (by simp [ker_eq_comap_of_flat j H])

end Closure

section Graph

variable {S Z₁ Z₂ U T T' : Scheme.{u}} (f₁ : Z₁ ⟶ S) (f₂ : Z₂ ⟶ S) (u : U ⟶ Z₁) (φ : U ⟶ Z₂)
  (h : u ≫ f₁ = φ ≫ f₂)

def graphMap : U ⟶ pullback f₁ f₂ := pullback.lift u φ h

theorem graphMap_fst : graphMap f₁ f₂ u φ h ≫ pullback.fst f₁ f₂ = u := pullback.lift_fst _ _ _

theorem graphMap_snd : graphMap f₁ f₂ u φ h ≫ pullback.snd f₁ f₂ = φ := pullback.lift_snd _ _ _

instance isImmersion_graphMap [IsImmersion u] : IsImmersion (graphMap f₁ f₂ u φ h) :=
  have : IsImmersion (graphMap f₁ f₂ u φ h ≫ pullback.fst f₁ f₂) := by
    rw [graphMap_fst]
    infer_instance
  IsImmersion.of_comp _ (pullback.fst f₁ f₂)

instance quasiCompact_graphMap [QuasiCompact u] [QuasiSeparated f₂] :
    QuasiCompact (graphMap f₁ f₂ u φ h) :=
  have : QuasiCompact (graphMap f₁ f₂ u φ h ≫ pullback.fst f₁ f₂) := by
    rw [graphMap_fst]
    infer_instance
  QuasiCompact.of_comp _ (pullback.fst f₁ f₂)

def graphClosure : Scheme.{u} := (graphMap f₁ f₂ u φ h).image

namespace graphClosure

def ι : graphClosure f₁ f₂ u φ h ⟶ pullback f₁ f₂ := (graphMap f₁ f₂ u φ h).imageι

def incl : U ⟶ graphClosure f₁ f₂ u φ h := (graphMap f₁ f₂ u φ h).toImage

def fst : graphClosure f₁ f₂ u φ h ⟶ Z₁ := ι f₁ f₂ u φ h ≫ pullback.fst f₁ f₂

def snd : graphClosure f₁ f₂ u φ h ⟶ Z₂ := ι f₁ f₂ u φ h ≫ pullback.snd f₁ f₂

@[reassoc (attr := simp)]
theorem ι_fst : ι f₁ f₂ u φ h ≫ pullback.fst f₁ f₂ = fst f₁ f₂ u φ h := rfl

theorem ι_snd : ι f₁ f₂ u φ h ≫ pullback.snd f₁ f₂ = snd f₁ f₂ u φ h := rfl

@[reassoc (attr := simp)]
theorem incl_ι : incl f₁ f₂ u φ h ≫ ι f₁ f₂ u φ h = graphMap f₁ f₂ u φ h :=
  (graphMap f₁ f₂ u φ h).toImage_imageι

theorem incl_fst : incl f₁ f₂ u φ h ≫ fst f₁ f₂ u φ h = u := by
  rw [← ι_fst, incl_ι_assoc, graphMap_fst]

theorem incl_snd : incl f₁ f₂ u φ h ≫ snd f₁ f₂ u φ h = φ := by
  rw [← ι_snd, incl_ι_assoc, graphMap_snd]

theorem condition : fst f₁ f₂ u φ h ≫ f₁ = snd f₁ f₂ u φ h ≫ f₂ := by
  rw [← ι_fst, ← ι_snd, Category.assoc, Category.assoc, pullback.condition]

instance isClosedImmersion_ι : IsClosedImmersion (ι f₁ f₂ u φ h) :=
  inferInstanceAs (IsClosedImmersion (graphMap f₁ f₂ u φ h).imageι)

instance schemeDominant_incl : IsSchemeTheoreticallyDominant (incl f₁ f₂ u φ h) :=
  schemeDominant_toImage (graphMap f₁ f₂ u φ h)

instance quasiCompact_incl [QuasiCompact u] [QuasiSeparated f₂] :
    QuasiCompact (incl f₁ f₂ u φ h) :=
  inferInstanceAs (QuasiCompact (graphMap f₁ f₂ u φ h).toImage)

instance isOpenImmersion_incl [IsImmersion u] [QuasiCompact u] [QuasiSeparated f₂] :
    IsOpenImmersion (incl f₁ f₂ u φ h) :=
  isOpenImmersion_toImage (graphMap f₁ f₂ u φ h)

instance isReduced [QuasiCompact u] [QuasiSeparated f₂] [IsReduced U] :
    IsReduced (graphClosure f₁ f₂ u φ h) :=
  isReduced_image (graphMap f₁ f₂ u φ h)

instance isIntegral [QuasiCompact u] [QuasiSeparated f₂] [IsIntegral U] :
    IsIntegral (graphClosure f₁ f₂ u φ h) :=
  isIntegral_image (graphMap f₁ f₂ u φ h)

theorem hom_ext {a b : T ⟶ graphClosure f₁ f₂ u φ h}
    (h₁ : a ≫ fst f₁ f₂ u φ h = b ≫ fst f₁ f₂ u φ h)
    (h₂ : a ≫ snd f₁ f₂ u φ h = b ≫ snd f₁ f₂ u φ h) : a = b := by
  rw [← cancel_mono (ι f₁ f₂ u φ h)]
  apply pullback.hom_ext <;> simpa

def lift (t₁ : T ⟶ Z₁) (t₂ : T ⟶ Z₂) (ht : t₁ ≫ f₁ = t₂ ≫ f₂) (d : T' ⟶ T)
    [IsSchemeTheoreticallyDominant d] (w : T' ⟶ U) (h₁ : d ≫ t₁ = w ≫ u) (h₂ : d ≫ t₂ = w ≫ φ) :
    T ⟶ graphClosure f₁ f₂ u φ h :=
  closureLift (graphMap f₁ f₂ u φ h) (pullback.lift t₁ t₂ ht) d w (by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, graphMap_fst, h₁]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, graphMap_snd, h₂])

section

variable (t₁ : T ⟶ Z₁) (t₂ : T ⟶ Z₂) (ht : t₁ ≫ f₁ = t₂ ≫ f₂) (d : T' ⟶ T)
  [IsSchemeTheoreticallyDominant d] (w : T' ⟶ U) (h₁ : d ≫ t₁ = w ≫ u) (h₂ : d ≫ t₂ = w ≫ φ)

@[reassoc (attr := simp)]
theorem lift_ι : lift f₁ f₂ u φ h t₁ t₂ ht d w h₁ h₂ ≫ ι f₁ f₂ u φ h = pullback.lift t₁ t₂ ht :=
  closureLift_imageι _ _ _ _ _

theorem lift_fst : lift f₁ f₂ u φ h t₁ t₂ ht d w h₁ h₂ ≫ fst f₁ f₂ u φ h = t₁ := by
  rw [← ι_fst, lift_ι_assoc, pullback.lift_fst]

theorem lift_snd : lift f₁ f₂ u φ h t₁ t₂ ht d w h₁ h₂ ≫ snd f₁ f₂ u φ h = t₂ := by
  rw [← ι_snd, lift_ι_assoc, pullback.lift_snd]


include ht d w h₁ h₂ in
include ht h₁ h₂ in
theorem existsUnique_lift : ∃! l : T ⟶ graphClosure f₁ f₂ u φ h,
    l ≫ fst f₁ f₂ u φ h = t₁ ∧ l ≫ snd f₁ f₂ u φ h = t₂ := by
  have hf := lift_fst f₁ f₂ u φ h t₁ t₂ ht d w h₁ h₂
  have hs := lift_snd f₁ f₂ u φ h t₁ t₂ ht d w h₁ h₂
  exact ⟨lift f₁ f₂ u φ h t₁ t₂ ht d w h₁ h₂, ⟨hf, hs⟩,
    fun _ hl ↦ hom_ext f₁ f₂ u φ h (hl.1.trans hf.symm) (hl.2.trans hs.symm)⟩

end

instance isProper_fst [IsProper f₂] : IsProper (fst f₁ f₂ u φ h) := by
  rw [← ι_fst]; infer_instance

instance isSeparated_fst [IsSeparated f₂] : IsSeparated (fst f₁ f₂ u φ h) := by
  rw [← ι_fst]; infer_instance

instance locallyOfFiniteType_fst [LocallyOfFiniteType f₂] :
    LocallyOfFiniteType (fst f₁ f₂ u φ h) := by
  rw [← ι_fst]; infer_instance

instance quasiCompact_fst [QuasiCompact f₂] : QuasiCompact (fst f₁ f₂ u φ h) := by
  rw [← ι_fst]; infer_instance

theorem isPullback_incl [Flat u] [Mono u] [QuasiCompact u] [IsSeparated f₂] :
    IsPullback (𝟙 U) (incl f₁ f₂ u φ h) u (fst f₁ f₂ u φ h) := by
  let u' : pullback (u ≫ f₁) f₂ ⟶ pullback f₁ f₂ :=
    pullback.lift (pullback.fst _ _ ≫ u) (pullback.snd _ _) (by simpa using pullback.condition)
  have hu₁ : u' ≫ pullback.fst f₁ f₂ = pullback.fst _ _ ≫ u := pullback.lift_fst _ _ _
  have hu₂ : u' ≫ pullback.snd f₁ f₂ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have Hu : IsPullback (pullback.fst (u ≫ f₁) f₂) u' u (pullback.fst f₁ f₂) := by
    refine IsPullback.of_bot (h₃₁ := f₂) (v₂₁ := pullback.snd f₁ f₂) (v₂₂ := f₁) ?_ hu₁.symm
      (IsPullback.of_hasPullback f₁ f₂)
    rw [hu₂]
    exact IsPullback.of_hasPullback _ _
  have : Flat u' := MorphismProperty.of_isPullback Hu ‹_›
  have : Mono u' := (MorphismProperty.monomorphisms _).of_isPullback Hu.flip.flip ‹Mono u›
  let c : U ⟶ pullback (u ≫ f₁) f₂ := pullback.lift (𝟙 U) φ (by simpa using h)
  have hc₁ : c ≫ pullback.fst _ _ = 𝟙 U := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = φ := pullback.lift_snd _ _ _
  have : IsClosedImmersion (c ≫ pullback.fst _ _) := by rw [hc₁]; infer_instance
  have : IsClosedImmersion c := .of_comp c (pullback.fst _ _)
  have hc : c ≫ u' = graphMap f₁ f₂ u φ h := by
    apply pullback.hom_ext
    · rw [Category.assoc, hu₁, reassoc_of% hc₁, graphMap_fst]
    · rw [Category.assoc, hu₂, hc₂, graphMap_snd]
  have H := (isPullback_toImage_of_isClosedImmersion _ c u' hc).paste_horiz Hu
  rw [hc₁] at H
  exact H

theorem isIso_fst_restrict_of_le [IsOpenImmersion u] [QuasiCompact u] [IsSeparated f₂]
    (V : Z₁.Opens) (hV : V ≤ u.opensRange) : IsIso (fst f₁ f₂ u φ h ∣_ V) := by
  let l : (V : Scheme.{u}) ⟶ U := IsOpenImmersion.lift u V.ι (by rw [Scheme.Opens.range_ι]; exact hV)
  have hl : l ≫ u = V.ι := IsOpenImmersion.lift_fac _ _ _
  have H := (IsPullback.id_horiz l).paste_vert (isPullback_incl f₁ f₂ u φ h)
  rw [hl] at H
  have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict (fst f₁ f₂ u φ h) V) H
  rw [← e]
  infer_instance

instance isIso_fst_restrict_opens (V : Z₁.Opens) (ψ : (V : Scheme.{u}) ⟶ Z₂)
    (hψ : V.ι ≫ f₁ = ψ ≫ f₂) [QuasiCompact V.ι] [IsSeparated f₂] :
    IsIso (fst f₁ f₂ V.ι ψ hψ ∣_ V) :=
  isIso_fst_restrict_of_le f₁ f₂ V.ι ψ hψ V (by simp)

theorem exists_extension_of_isIso_fst [IsIso (fst f₁ f₂ u φ h)] :
    ∃ ψ : Z₁ ⟶ Z₂, f₁ = ψ ≫ f₂ ∧ u ≫ ψ = φ := by
  refine ⟨inv (fst f₁ f₂ u φ h) ≫ snd f₁ f₂ u φ h, by simp [← condition], ?_⟩
  have : u ≫ inv (fst f₁ f₂ u φ h) = incl f₁ f₂ u φ h := by simp [incl_fst]
  rw [reassoc_of% this, incl_snd]

end graphClosure

end Graph

section Examples

namespace GraphClosureExample

end GraphClosureExample

end Examples

end

end GlobalTheory
