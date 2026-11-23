module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe w' w u

noncomputable section

namespace GlobalTheory.QCoh

variable {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}

section Sections

def appLinear (φ : M ⟶ N) (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul φ

@[simp]
theorem appLinear_apply (φ : M ⟶ N) (U : X.Opens) (s : Γ(M, U)) :
    appLinear φ U s = φ.app U s := rfl

theorem coe_appLinear (φ : M ⟶ N) (U : X.Opens) : ⇑(appLinear φ U) = φ.app U := rfl

theorem appLinear_comp (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens) :
    appLinear (φ ≫ ψ) U = appLinear ψ U ∘ₗ appLinear φ U := rfl

theorem app_app (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens) (s : Γ(M, U)) :
    ψ.app U (φ.app U s) = (φ ≫ ψ).app U s := rfl

theorem app_res (φ : M ⟶ N) (h : V ≤ U) (s : Γ(M, U)) :
    φ.app V (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (φ.app U s) :=
  congr($(φ.mapPresheaf.naturality (homOfLE h).op) s)

def sections (U : X.Opens) : X.Modules ⥤ ModuleCat.{u} Γ(X, U) where
  obj M := ModuleCat.of Γ(X, U) Γ(M, U)
  map φ := ModuleCat.ofHom (appLinear φ U)

instance (U : X.Opens) : (sections U).Additive where

instance sections_preservesLimits (U : X.Opens) : PreservesLimits (sections U) := by
  have : PreservesLimits (sections U ⋙ forget₂ (ModuleCat.{u} Γ(X, U)) Ab.{u}) :=
    haveI : PreservesLimits ((evaluation (Opens X)ᵒᵖ Ab.{u}).obj (op U)) :=
      ⟨fun {_} _ ↦ evaluation_preservesLimitsOfShape _⟩
    comp_preservesLimits (Scheme.Modules.toPresheaf X) ((evaluation _ _).obj (op U))
  exact preservesLimits_of_reflects_of_preserves _ (forget₂ (ModuleCat.{u} Γ(X, U)) Ab.{u})

instance (U : X.Opens) : PreservesFiniteLimits (sections U) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

theorem injective_app_of_mono (φ : M ⟶ N) [Mono φ] (U : X.Opens) :
    Function.Injective (φ.app U) :=
  (ModuleCat.mono_iff_injective ((sections U).map φ)).mp inferInstance

theorem exact_app_of_exact_of_mono {S : ShortComplex X.Modules} (hS : S.Exact) [Mono S.f]
    (U : X.Opens) : Function.Exact (S.f.app U) (S.g.app U) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map (sections U))).mp
    (hS.map_of_mono_of_preservesKernel (sections U) inferInstance inferInstance)

def sectionsIsoSpec (hU : IsAffineOpen U) :
    sections U ≅ Scheme.Modules.restrictFunctor hU.fromSpec ⋙ moduleSpecΓFunctor (R := Γ(X, U)) :=
  NatIso.ofComponents (fun F ↦ LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective (M := Γ(F, U)) (M₂ := Γ(F.restrict hU.fromSpec, ⊤))
      { toFun := fun s ↦ (F.restrictAppIso hU.fromSpec ⊤).inv
          (F.presheaf.map (homOfLE (fromSpec_image_le hU ⊤)).op s)
        map_add' := fun s t ↦ by simp
        map_smul' := fun r s ↦ by
          rw [F.map_smul, RingHom.id_apply]
          exact (restrict_fromSpec_smul F hU ⊤ r _).symm }
      (by
        have key : ∀ (W : X.Opens) (h : W ≤ U), W = U →
            Function.Bijective (F.presheaf.map (homOfLE h).op) := by
          rintro W h rfl
          have : ⇑(F.presheaf.map (homOfLE h).op) = id := funext (res_self F h)
          rw [this]
          exact Function.bijective_id
        exact key _ (fromSpec_image_le hU ⊤)
          (by rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]))))
    fun φ ↦ by
      ext s
      exact (app_res φ (fromSpec_image_le hU ⊤) s).symm

end Sections

section Colimits

variable {J : Type w} [Category.{w'} J]

set_option backward.isDefEq.respectTransparency false in
theorem isQuasicoherent_of_iso (e : M ≅ N) [M.IsQuasicoherent] : N.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e ‹_›

def tildeDiagramIso {R : CommRingCat.{u}} (D : J ⥤ (Spec R).Modules)
    [∀ j, (D.obj j).IsQuasicoherent] :
    (D ⋙ moduleSpecΓFunctor (R := R)) ⋙ tilde.functor R ≅ D :=
  haveI (j : J) : IsIso (tilde.adjunction.counit.app (D.obj j)) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (D.obj j)
  NatIso.ofComponents (fun j ↦ asIso (tilde.adjunction.counit.app (D.obj j)))
    fun f ↦ tilde.adjunction.counit.naturality (D.map f)

theorem isQuasicoherent_of_isColimit_Spec {R : CommRingCat.{u}}
    [HasColimitsOfShape J (ModuleCat.{u} R)] {D : J ⥤ (Spec R).Modules}
    [∀ j, (D.obj j).IsQuasicoherent] {c : Cocone D} (hc : IsColimit c) :
    c.pt.IsQuasicoherent :=
  isQuasicoherent_of_iso (M := (tilde.functor R).obj (colimit (D ⋙ moduleSpecΓFunctor (R := R))))
    (IsColimit.coconePointsIsoOfNatIso
      (isColimitOfPreserves (tilde.functor R) (colimit.isColimit _)) hc (tildeDiagramIso D))

theorem preservesColimit_moduleSpecΓFunctor {R : CommRingCat.{u}}
    [HasColimitsOfShape J (ModuleCat.{u} R)] (D : J ⥤ (Spec R).Modules)
    [∀ j, (D.obj j).IsQuasicoherent] :
    PreservesColimit D (moduleSpecΓFunctor (R := R)) := by
  have : PreservesColimit (D ⋙ moduleSpecΓFunctor (R := R))
      (tilde.functor R ⋙ moduleSpecΓFunctor (R := R)) :=
    preservesColimit_of_natIso _ tilde.toTildeΓNatIso
  have : PreservesColimit ((D ⋙ moduleSpecΓFunctor (R := R)) ⋙ tilde.functor R)
      (moduleSpecΓFunctor (R := R)) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves (tilde.functor R) (colimit.isColimit _))
      (isColimitOfPreserves (tilde.functor R ⋙ moduleSpecΓFunctor (R := R)) (colimit.isColimit _))
  exact preservesColimit_of_iso_diagram _ (tildeDiagramIso D)

variable [Small.{u} J]

theorem isQuasicoherent_of_isColimit {D : J ⥤ X.Modules}
    [∀ j, (D.obj j).IsQuasicoherent] {c : Cocone D} (hc : IsColimit c) :
    c.pt.IsQuasicoherent := by
  refine (isQuasicoherent_iff_forall_affine _).mpr fun U hU ↦ ?_
  rw [← isQuasicoherent_restrict_fromSpec_iff _ hU]
  have (j : J) : ((D ⋙ Scheme.Modules.restrictFunctor hU.fromSpec).obj j).IsQuasicoherent :=
    inferInstanceAs ((D.obj j).restrict hU.fromSpec).IsQuasicoherent
  exact isQuasicoherent_of_isColimit_Spec
    (isColimitOfPreserves (Scheme.Modules.restrictFunctor hU.fromSpec) hc)

theorem preservesColimit_sections (hU : IsAffineOpen U) (D : J ⥤ X.Modules)
    [∀ j, (D.obj j).IsQuasicoherent] : PreservesColimit D (sections U) := by
  have (j : J) : ((D ⋙ Scheme.Modules.restrictFunctor hU.fromSpec).obj j).IsQuasicoherent :=
    inferInstanceAs ((D.obj j).restrict hU.fromSpec).IsQuasicoherent
  have := preservesColimit_moduleSpecΓFunctor (D ⋙ Scheme.Modules.restrictFunctor hU.fromSpec)
  have : PreservesColimit D
      (Scheme.Modules.restrictFunctor hU.fromSpec ⋙ moduleSpecΓFunctor (R := Γ(X, U))) :=
    ⟨fun hc ↦ ⟨isColimitOfPreserves (moduleSpecΓFunctor (R := Γ(X, U)))
      (isColimitOfPreserves (Scheme.Modules.restrictFunctor hU.fromSpec) hc)⟩⟩
  exact preservesColimit_of_natIso _ (sectionsIsoSpec hU).symm

end Colimits

section Closure

instance isQuasicoherent_colimit {J : Type w} [Category.{w'} J] [Small.{u} J] (D : J ⥤ X.Modules)
    [HasColimit D] [∀ j, (D.obj j).IsQuasicoherent] : (colimit D).IsQuasicoherent :=
  isQuasicoherent_of_isColimit (colimit.isColimit D)

instance isQuasicoherent_parallelPair_obj (φ ψ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (j : WalkingParallelPair) : ((parallelPair φ ψ).obj j).IsQuasicoherent := by
  cases j <;> assumption

instance isQuasicoherent_discrete_obj {ι : Type w} (F : ι → X.Modules)
    [h : ∀ i, (F i).IsQuasicoherent] (j : Discrete ι) :
    ((Discrete.functor F).obj j).IsQuasicoherent := h j.as

instance isQuasicoherent_pair_obj [M.IsQuasicoherent] [N.IsQuasicoherent]
    (j : Discrete WalkingPair) : ((pair M N).obj j).IsQuasicoherent := by
  obtain ⟨_ | _⟩ := j <;> assumption


instance isQuasicoherent_cokernel (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel φ).IsQuasicoherent :=
  isQuasicoherent_colimit _

instance isQuasicoherent_biproduct {ι : Type w} [Small.{u} ι] (F : ι → X.Modules)
    [HasBiproduct F] [∀ i, (F i).IsQuasicoherent] : (⨁ F).IsQuasicoherent :=
  isQuasicoherent_of_isColimit (biproduct.isColimit F)

instance isQuasicoherent_biprod [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent :=
  isQuasicoherent_of_isColimit (BinaryBiproduct.isColimit M N)

instance isQuasicoherent_pi {ι : Type w} [Finite ι] (F : ι → X.Modules) [HasProduct F]
    [∀ i, (F i).IsQuasicoherent] : (∏ᶜ F).IsQuasicoherent :=
  haveI : HasBiproduct F := HasBiproduct.of_hasProduct F
  isQuasicoherent_of_iso (biproduct.isoProduct F)

theorem isQuasicoherent_of_exact_app {K : X.Modules} (ι : K ⟶ M) (φ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hι : ∀ U, IsAffineOpen U → Function.Injective (ι.app U))
    (hex : ∀ U, IsAffineOpen U → Function.Exact (ι.app U) (φ.app U)) :
    K.IsQuasicoherent := by
  refine (isQuasicoherent_iff_forall_affine _).mpr fun U hU f ↦ ?_
  rw [isLocalizedModule_resBasicOpen_iff]
  refine ⟨fun s ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨n, m, hm⟩ := exists_pow_smul_eq_res M hU f (X.basicOpen_le f) rfl (ι.app _ s)
    obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero N hU f (X.basicOpen_le f) rfl (φ.app U m) (by
      rw [← app_res, ← hm, Scheme.Modules.Hom.app_smul,
        (hex _ (hU.basicOpen f)).apply_apply_eq_zero, smul_zero])
    rw [← Scheme.Modules.Hom.app_smul] at hk
    obtain ⟨t, ht⟩ := (hex U hU _).mp hk
    refine ⟨k + n, t, hι _ (hU.basicOpen f) ?_⟩
    rw [app_res, ht, M.map_smul, ← hm, Scheme.Modules.Hom.app_smul, map_pow, pow_add, mul_smul]
  · obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero M hU f (X.basicOpen_le f) rfl (ι.app U t) (by
      rw [← app_res, ht, map_zero])
    exact ⟨n, hι U hU (by rw [Scheme.Modules.Hom.app_smul, hn, map_zero])⟩

theorem injective_kernel_ι_app (φ : M ⟶ N) (U : X.Opens) :
    Function.Injective ((kernel.ι φ).app U) :=
  injective_app_of_mono _ U

theorem exact_kernel_ι_app (φ : M ⟶ N) (U : X.Opens) :
    Function.Exact ((kernel.ι φ).app U) (φ.app U) :=
  exact_app_of_exact_of_mono (S := ShortComplex.mk _ _ (kernel.condition φ))
    (ShortComplex.exact_kernel φ) U

instance isQuasicoherent_kernel (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (kernel φ).IsQuasicoherent :=
  isQuasicoherent_of_exact_app (kernel.ι φ) φ (fun U _ ↦ injective_kernel_ι_app φ U)
    fun U _ ↦ exact_kernel_ι_app φ U

instance isQuasicoherent_abelianImage (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (Abelian.image φ).IsQuasicoherent :=
  isQuasicoherent_kernel _

instance isQuasicoherent_abelianCoimage (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (Abelian.coimage φ).IsQuasicoherent :=
  isQuasicoherent_cokernel _

instance isQuasicoherent_image (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (image φ).IsQuasicoherent :=
  isQuasicoherent_of_iso (Abelian.imageIsoImage φ)

end Closure

section Affine

theorem exact_and_surjective_app_of_exact_of_epi {S : ShortComplex X.Modules} (hS : S.Exact)
    [Epi S.g] [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] (hU : IsAffineOpen U) :
    Function.Exact (S.f.app U) (S.g.app U) ∧ Function.Surjective (S.g.app U) := by
  have := preservesColimit_sections hU (parallelPair S.f 0)
  have h := ((S.map (sections U)).exact_and_epi_g_iff_g_is_cokernel).mpr
    ⟨CokernelCofork.mapIsColimit _ hS.gIsCokernel (sections U)⟩
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map (sections U))).mp h.1,
    (ModuleCat.epi_iff_surjective _).mp h.2⟩

theorem exact_cokernel_π_app (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) : Function.Exact (φ.app U) ((cokernel.π φ).app U) :=
  (exact_and_surjective_app_of_exact_of_epi (S := ShortComplex.mk _ _ (cokernel.condition φ))
    (ShortComplex.exact_cokernel φ) hU).1

theorem surjective_cokernel_π_app (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) : Function.Surjective ((cokernel.π φ).app U) :=
  (exact_and_surjective_app_of_exact_of_epi (S := ShortComplex.mk _ _ (cokernel.condition φ))
    (ShortComplex.exact_cokernel φ) hU).2

theorem subsingleton_sections_of_isZero (h : IsZero M) (U : X.Opens) : Subsingleton Γ(M, U) :=
  ModuleCat.isZero_iff_subsingleton.mp ((sections U).map_isZero h)

theorem surjective_app_of_epi (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi φ]
    (hU : IsAffineOpen U) : Function.Surjective (φ.app U) := fun t ↦
  haveI := subsingleton_sections_of_isZero (isZero_cokernel_of_epi φ) U
  (exact_cokernel_π_app φ hU t).mp (Subsingleton.elim _ _)

theorem exact_app_iff_surjective_lift (S : ShortComplex X.Modules) (U : X.Opens) :
    Function.Exact (S.f.app U) (S.g.app U) ↔
      Function.Surjective ((kernel.lift S.g S.f S.zero).app U) := by
  refine ⟨fun h t ↦ ?_, fun h t ↦ ⟨fun ht ↦ ?_, ?_⟩⟩
  · obtain ⟨s, hs⟩ := (h _).mp ((exact_kernel_ι_app S.g U).apply_apply_eq_zero t)
    exact ⟨s, injective_kernel_ι_app S.g U (by rw [app_app, kernel.lift_ι, hs])⟩
  · obtain ⟨t, rfl⟩ := (exact_kernel_ι_app S.g U t).mp ht
    obtain ⟨s, rfl⟩ := h t
    exact ⟨s, by rw [app_app, kernel.lift_ι]⟩
  · rintro ⟨s, rfl⟩
    rw [app_app, S.zero]
    rfl

theorem exact_app_of_exact {S : ShortComplex X.Modules} (hS : S.Exact) [S.X₁.IsQuasicoherent]
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] (hU : IsAffineOpen U) :
    Function.Exact (S.f.app U) (S.g.app U) :=
  haveI := (S.exact_iff_epi_kernel_lift).mp hS
  (exact_app_iff_surjective_lift S U).mpr (surjective_app_of_epi _ hU)

theorem surjective_factorThruImage_app (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) : Function.Surjective ((factorThruImage φ).app U) :=
  surjective_app_of_epi _ hU

end Affine

section Cover

variable {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i))
include hcov haff

theorem isZero_iff_affineCover [M.IsQuasicoherent] :
    IsZero M ↔ ∀ i, Subsingleton Γ(M, 𝒰 i) := by
  refine ⟨fun h i ↦ subsingleton_sections_of_isZero h _, fun h ↦ ?_⟩
  rw [IsZero.iff_id_eq_zero]
  ext V s
  change s = 0
  refine TopCat.Presheaf.IsSheaf.section_ext M.isSheaf fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := hcov.exists_mem x
  obtain ⟨f, hfV, hxf⟩ := (haff i).exists_basicOpen_le (V := V) ⟨x, hx⟩ hi
  refine ⟨X.basicOpen f, hfV, hxf, ?_⟩
  obtain ⟨n, t, ht⟩ := exists_pow_smul_eq_res M (haff i) f (X.basicOpen_le f) rfl
    (M.presheaf.map (homOfLE hfV).op s)
  rw [Subsingleton.elim t 0, map_zero,
    ((isUnit_res_of_le_basicOpen f (X.basicOpen_le f) le_rfl).pow n).smul_eq_zero] at ht
  rw [map_zero]
  exact ht

variable [M.IsQuasicoherent] [N.IsQuasicoherent]

theorem mono_iff_affineCover (φ : M ⟶ N) : Mono φ ↔ ∀ i, Function.Injective (φ.app (𝒰 i)) := by
  refine ⟨fun _ i ↦ injective_app_of_mono φ _, fun h ↦ ?_⟩
  refine Preadditive.mono_of_isZero_kernel φ
    ((isZero_iff_affineCover 𝒰 hcov haff).mpr fun i ↦ subsingleton_of_forall_eq 0 fun s ↦ ?_)
  refine injective_kernel_ι_app φ _ (h i ?_)
  rw [(exact_kernel_ι_app φ _).apply_apply_eq_zero, map_zero, map_zero]

theorem epi_iff_affineCover (φ : M ⟶ N) : Epi φ ↔ ∀ i, Function.Surjective (φ.app (𝒰 i)) := by
  refine ⟨fun _ i ↦ surjective_app_of_epi φ (haff i), fun h ↦ ?_⟩
  refine Preadditive.epi_of_isZero_cokernel φ
    ((isZero_iff_affineCover 𝒰 hcov haff).mpr fun i ↦ subsingleton_of_forall_eq 0 fun s ↦ ?_)
  obtain ⟨t, rfl⟩ := surjective_cokernel_π_app φ (haff i) s
  obtain ⟨t, rfl⟩ := h i t
  exact (exact_cokernel_π_app φ (haff i)).apply_apply_eq_zero t

theorem isIso_iff_affineCover (φ : M ⟶ N) : IsIso φ ↔ ∀ i, Function.Bijective (φ.app (𝒰 i)) := by
  rw [isIso_iff_mono_and_epi, mono_iff_affineCover 𝒰 hcov haff, epi_iff_affineCover 𝒰 hcov haff,
    ← forall_and]
  rfl

variable (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
  [S.X₃.IsQuasicoherent]

theorem exact_iff_affineCover :
    S.Exact ↔ ∀ i, Function.Exact (S.f.app (𝒰 i)) (S.g.app (𝒰 i)) := by
  simp only [S.exact_iff_epi_kernel_lift, epi_iff_affineCover 𝒰 hcov haff,
    exact_app_iff_surjective_lift]

end Cover

section Subcategory


variable (X) in
abbrev qcoh : ObjectProperty X.Modules := fun M ↦ M.IsQuasicoherent

end Subcategory

section Equivs

theorem range_kernel_ι_app (φ : M ⟶ N) (U : X.Opens) :
    LinearMap.range (appLinear (kernel.ι φ) U) = LinearMap.ker (appLinear φ U) :=
  Submodule.ext fun s ↦ (exact_kernel_ι_app φ U s).symm

def kernelSectionsEquiv (φ : M ⟶ N) (U : X.Opens) :
    Γ(kernel φ, U) ≃ₗ[Γ(X, U)] LinearMap.ker (appLinear φ U) :=
  (LinearEquiv.ofInjective (appLinear (kernel.ι φ) U) (injective_kernel_ι_app φ U)).trans
    (LinearEquiv.ofEq _ _ (range_kernel_ι_app φ U))


theorem app_sum {ι : Type w} (t : Finset ι) (φ : ι → (M ⟶ N)) (U : X.Opens) (s : Γ(M, U)) :
    (∑ i ∈ t, φ i).app U s = ∑ i ∈ t, (φ i).app U s := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

def biproductSectionsEquiv {ι : Type} [Fintype ι] (F : ι → X.Modules) [HasBiproduct F]
    (U : X.Opens) : Γ(⨁ F, U) ≃ₗ[Γ(X, U)] (∀ i, Γ(F i, U)) where
  toLinearMap := LinearMap.pi fun i ↦ appLinear (biproduct.π F i) U
  invFun s := ∑ i, (biproduct.ι F i).app U (s i)
  left_inv s := by
    simp only [LinearMap.toFun_eq_coe, LinearMap.pi_apply, appLinear_apply, app_app]
    rw [← app_sum, biproduct.total]
    rfl
  right_inv s := by
    classical
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.toFun_eq_coe, LinearMap.pi_apply, appLinear_apply, map_sum, app_app]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [biproduct.ι_π_ne F hj]; rfl) (by simp),
      biproduct.ι_π_self]
    rfl

theorem biproductSectionsEquiv_symm_apply {ι : Type} [Fintype ι] (F : ι → X.Modules)
    [HasBiproduct F] (U : X.Opens) (s : ∀ i, Γ(F i, U)) :
    (biproductSectionsEquiv F U).symm s = ∑ i, (biproduct.ι F i).app U (s i) := rfl

def biprodSectionsEquiv (M N : X.Modules) (U : X.Opens) :
    Γ(M ⊞ N, U) ≃ₗ[Γ(X, U)] Γ(M, U) × Γ(N, U) where
  toLinearMap := LinearMap.prod (appLinear biprod.fst U) (appLinear biprod.snd U)
  invFun s := (biprod.inl : M ⟶ M ⊞ N).app U s.1 + (biprod.inr : N ⟶ M ⊞ N).app U s.2
  left_inv s := by
    change (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr : M ⊞ N ⟶ M ⊞ N).app U s = s
    rw [biprod.total]
    rfl
  right_inv s := by
    ext
    · change (biprod.fst : M ⊞ N ⟶ M).app U _ = _
      rw [map_add (f := _), app_app, app_app, biprod.inl_fst, biprod.inr_fst]
      exact add_zero _
    · change (biprod.snd : M ⊞ N ⟶ N).app U _ = _
      rw [map_add (f := _), app_app, app_app, biprod.inl_snd, biprod.inr_snd]
      exact zero_add _

end Equivs

section AllAffine

variable [M.IsQuasicoherent] [N.IsQuasicoherent]

theorem isZero_iff_forall_affine :
    IsZero M ↔ ∀ U, IsAffineOpen U → Subsingleton Γ(M, U) :=
  (isZero_iff_affineCover (fun i : X.affineOpens ↦ i.1) (iSup_affineOpens_eq_top X)
    fun i ↦ i.2).trans Subtype.forall

theorem epi_iff_forall_affine (φ : M ⟶ N) :
    Epi φ ↔ ∀ U, IsAffineOpen U → Function.Surjective (φ.app U) :=
  (epi_iff_affineCover (fun i : X.affineOpens ↦ i.1) (iSup_affineOpens_eq_top X)
    (fun i ↦ i.2) φ).trans Subtype.forall

theorem isIso_iff_forall_affine (φ : M ⟶ N) :
    IsIso φ ↔ ∀ U, IsAffineOpen U → Function.Bijective (φ.app U) :=
  (isIso_iff_affineCover (fun i : X.affineOpens ↦ i.1) (iSup_affineOpens_eq_top X)
    (fun i ↦ i.2) φ).trans Subtype.forall

variable (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
  [S.X₃.IsQuasicoherent]

theorem exact_iff_forall_affine :
    S.Exact ↔ ∀ U, IsAffineOpen U → Function.Exact (S.f.app U) (S.g.app U) :=
  (exact_iff_affineCover (fun i : X.affineOpens ↦ i.1) (iSup_affineOpens_eq_top X)
    (fun i ↦ i.2) S).trans Subtype.forall

end AllAffine

theorem hom_eq_zero_iff_affineCover {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰)
    (haff : ∀ i, IsAffineOpen (𝒰 i)) [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    φ = 0 ↔ ∀ i s, φ.app (𝒰 i) s = 0 := by
  refine ⟨fun h i s ↦ by rw [h]; rfl, fun h ↦ ?_⟩
  have : Epi (kernel.ι φ) := (epi_iff_affineCover 𝒰 hcov haff _).mpr fun i s ↦
    (exact_kernel_ι_app φ _ s).mp (h i s)
  rw [← cancel_epi (kernel.ι φ), kernel.condition, comp_zero]

end GlobalTheory.QCoh
