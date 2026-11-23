module

public import Development.EtaleCohomology.TateTwists.Bundle0002
public import Development.EtaleCohomology.TateTwists.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafInjectiveResolutionInitialShortComplex
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ResSecPf

variable (R : Type) [CommRing R]

noncomputable abbrev secF (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)

lemma exact_pos (F : Shv R) (m n k : ℤ) (hn : 0 < n) (hm : m + 1 = n) (hk : n + 1 = k) :
    (ShortComplex.mk ((res R F).d m n) ((res R F).d n k) (by simp)).Exact := by
  have h1 : (res R F).ExactAt n := by
    unfold res
    rw [← quasiIsoAt_iff_exactAt (injectiveResolution F).ι' n
      (HomologicalComplex.exactAt_single_obj _ _ _ _ (by omega))]
    infer_instance
  exact (HomologicalComplex.exactAt_iff' _ m n k (by simp; omega) (by simp; omega)).1 h1

lemma subsing (F : Shv R) (U : Scheme.{0}) (n : ℤ) (hn : n < 0) :
    Subsingleton (Sec ((res R F).X n) U) := by
  have hz : IsZero ((res R F).X n) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have := (hz.of_iso (Iso.refl _)).eq_of_src (𝟙 _) 0
  constructor
  intro a b
  have e : ∀ x : Sec ((res R F).X n) U, x = 0 := by
    intro x
    have := congrArg (fun f => Sec.map f x) (hz.eq_of_src (𝟙 _) 0)
    simpa [Sec.map] using this
  rw [e a, e b]

lemma resι_e (F : Shv R) :
    resι R F ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom = (injectiveResolution F).ι.f 0 := by
  unfold resι
  rw [InjectiveResolution.ι'_f_zero]
  erw [Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

lemma d01' (F : Shv R) : ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom ≫
    (injectiveResolution F).cocomplex.d 0 1 = (injectiveResolution F).cochainComplex.d 0 1 ≫
      ((injectiveResolution F).cochainComplexXIso 1 1 rfl).hom := by
  rw [InjectiveResolution.cochainComplex_d _ 0 1 0 1 rfl rfl]
  simp

lemma etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  have h := (injectiveResolution F).ι'.comm 0 1
  unfold resι res
  refine (Category.assoc _ _ _).trans ?_
  erw [h]
  simp
  rfl

noncomputable abbrev S0 (F : Shv R) : ShortComplex (Shv R) := ShortComplex.mk _ _ (etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero R F)

lemma etaleSheaf_injectiveResolution_initial_shortComplex_exact (F : Shv R) : (S0 R F).Exact := by
  let I := injectiveResolution F
  have hN : (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact :=
    ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelFork
  refine (ShortComplex.exact_iff_of_iso ?_).2 hN
  refine ShortComplex.isoMk (Iso.refl _) (I.cochainComplexXIso 0 0 rfl) (I.cochainComplexXIso 1 1 rfl) ?_ ?_
  · exact (Category.id_comp _).trans (resι_e R F).symm
  · exact d01' R F

lemma mono_resι_var (F : Shv R) : Mono (resι R F) := by
  have : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  have h := resι_e R F
  have : Mono (resι R F ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom) := by
    rw [h]; assumption
  exact mono_of_mono _ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom

def exact_loc : Prop := ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact →
  ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b

lemma part1 (F : Shv R) (U : Scheme.{0}) (z : Sec ((res R F).X 0) U) :
    Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z := by
  constructor
  · intro hz
    have hE : ((S0 R F).map (secF R U)).Exact :=
      (etaleSheaf_injectiveResolution_initial_shortComplex_exact R F).map_of_mono_of_preservesKernel _ (mono_resι_var R F) inferInstance
    rw [ShortComplex.moduleCat_exact_iff] at hE
    exact hE z hz
  · rintro ⟨a, rfl⟩
    have := congrArg (fun f => Sec.map f a) (etaleSheaf_injectiveResolution_initial_shortComplex_comp_zero R F)
    simpa [Sec.map] using this

lemma part2 (F : Shv R) (U : Scheme.{0}) : Function.Injective (Sec.map (resι R F) (U := U)) := by
  have := mono_resι_var R F
  have : Mono ((secF R U).map (resι R F)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

end LateralTheory.EtaleFoundations.ResSecPf

open LateralTheory.EtaleFoundations.ResSecPf in
theorem LateralTheory.EtaleFoundations.etaleSheaf_injectiveResolution_sections_exact_of_local_exactness (hL : exact_loc) : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionSectionsLocallyExact := by
  intro R _ F U
  refine ⟨part1 R F U, part2 R F U, ?_, fun n hn => subsing R F U n hn⟩
  intro m n k hn hm z hk hz
  exact hL R _ (exact_pos R F m n k hn hm hk) U z hz
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafInjectiveResolutionPropertiesOfMathlib
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ResBasicPf

variable {R : Type} [CommRing R]

noncomputable def descH {F G : Shv R} (φ : F ⟶ G) :
    InjectiveResolution.Hom (injectiveResolution F) (injectiveResolution G) φ :=
  ⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
    HomologicalComplex.congr_hom (InjectiveResolution.desc_commutes φ (injectiveResolution G) (injectiveResolution F)) 0⟩

lemma resMap_eq {F G : Shv R} (φ : F ⟶ G) : resMap R φ = (descH φ).hom' := rfl

lemma resι_eq (F : Shv R) : resι R F =
    (injectiveResolution F).ι.f 0 ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).inv := by
  simp [resι, InjectiveResolution.ι'_f_zero]
  rfl

lemma kinj (F : Shv R) : (res R F).IsKInjective :=
  isKInjective_of_injective (injectiveResolution F).cochainComplex 0

lemma inj (F : Shv R) (n : ℤ) : Injective ((res R F).X n) :=
  inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))

lemma ge (F : Shv R) : (res R F).IsStrictlyGE 0 :=
  inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)

lemma qis (F : Shv R) : QuasiIso (resAug F) :=
  inferInstanceAs (QuasiIso (injectiveResolution F).ι')

lemma mono (F : Shv R) : Mono (resι R F) := by
  have h0 : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  have h2 : Mono ((injectiveResolution F).cochainComplexXIso 0 0 rfl).inv := inferInstance
  rw [resι_eq]; exact @mono_comp _ _ _ _ _ _ h0 _ h2

lemma dzero (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  rw [resι_eq]
  change _ ≫ (injectiveResolution F).cochainComplex.d 0 1 = 0
  rw [InjectiveResolution.cochainComplex_d _ 0 1 0 1 rfl rfl]
  erw [Category.assoc, Iso.inv_hom_id_assoc, InjectiveResolution.ι_f_zero_comp_complex_d_assoc, zero_comp]
  rfl

lemma aug_nat {F G : Shv R} (φ : F ⟶ G) :
    resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G := by
  rw [resMap_eq]; exact InjectiveResolution.Hom.ι'_comp_hom' _

lemma ι_nat {F G : Shv R} (φ : F ⟶ G) : resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G := by
  have h := congrArg (fun f => sglι F ≫ HomologicalComplex.Hom.f f 0) (aug_nat φ)
  simp only [HomologicalComplex.comp_f] at h
  change resι R F ≫ _ = _ at h
  rw [h]
  simp [sglι, resι, resAug, CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self]

end LateralTheory.EtaleFoundations.ResBasicPf

open LateralTheory.EtaleFoundations.ResBasicPf in
theorem LateralTheory.EtaleFoundations.etaleSheaf_injectiveResolution_properties_of_mathlib : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties := by
  intro R _ F
  exact ⟨kinj F, inj F, ge F, qis F, rfl, mono F, dzero F, fun G φ => ⟨aug_nat φ, ι_nat φ⟩⟩
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafMonoEpiIffSectionsOfSeparation
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MonoEpiPf

variable {R : Type} [CommRing R]

theorem sep {F : Shv R} {U : Scheme.{0}} (a : Sec F U)
    (h : Loc U fun _ g => Sec.res g a = 0) : a = 0 := by
  obtain ⟨S, hS, hP⟩ := h
  have key := Presheaf.IsSheaf.hom_ext F.property ⟨S, hS⟩
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ a)) 0 (by
      intro I
      ext
      have := hP _ I.f I.hf
      simp only [Sec.res] at this
      simp [LinearMap.toSpanSingleton_apply, this])
  have := congrArg (fun f => f.hom (1 : ULift.{1} R)) key
  simpa using this

theorem mono_iff_inj {F G : Shv R} (φ : F ⟶ G) :
    Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U)) := by
  constructor
  · intro h U
    have : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
    have : Mono (φ.hom.app (op U)) := (NatTrans.mono_iff_mono_app _).1 this _
    exact (ModuleCat.mono_iff_injective _).1 this
  · intro h
    have : Mono φ.hom := by
      rw [NatTrans.mono_iff_mono_app]
      intro U
      induction U using Opposite.rec with | op U => ?_
      exact (ModuleCat.mono_iff_injective _).2 (h U)
    exact (sheafToPresheaf _ _).mono_of_mono_map this

theorem inj_iff_loc {F G : Shv R} (φ : F ⟶ G) :
    (∀ U, Function.Injective (Sec.map φ (U := U))) ↔
      ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  constructor
  · intro h U a ha
    have : a = 0 := h U (by rw [ha]; simp [Sec.map])
    subst this
    exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => by simp [Sec.res]⟩
  · intro h U
    have hk : ∀ a : Sec F U, Sec.map φ a = 0 → a = 0 := fun a ha => sep a (h U a ha)
    intro a b hab
    have : Sec.map φ (a - b) = 0 := by simp only [Sec.map] at hab ⊢; rw [map_sub, hab, sub_self]
    exact sub_eq_zero.1 (hk _ this)

theorem epi_iff {F G : Shv R} (φ : F ⟶ G) :
    Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b := by
  rw [← Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{1} (ULift.{1} R))]
  constructor
  · intro h U b
    refine ⟨Presheaf.imageSieve φ.hom b, h.imageSieve_mem b, fun V g hg => ?_⟩
    rw [Presheaf.imageSieve_apply] at hg
    exact hg
  · intro h
    refine ⟨fun {U} b => ?_⟩
    obtain ⟨S, hS, hP⟩ := h U b
    refine Scheme.etaleTopology.superset_covering (fun V g hg => ?_) hS
    rw [Presheaf.imageSieve_apply]
    exact hP V g hg

theorem ext_sec {F G : Shv R} (φ ψ : F ⟶ G)
    (h : ∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) : φ = ψ := by
  apply Sheaf.hom_ext
  ext U a
  induction U using Opposite.rec with | op U => ?_
  exact h U a

end LateralTheory.EtaleFoundations.MonoEpiPf

open LateralTheory.EtaleFoundations.MonoEpiPf in
theorem LateralTheory.EtaleFoundations.etale_sheaf_mono_epi_iff_sections_of_separation : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria := by
  intro R _ F G φ
  exact ⟨mono_iff_inj φ, (mono_iff_inj φ).trans (inj_iff_loc φ), epi_iff φ,
    fun ψ h => ext_sec φ ψ h⟩
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafRestrictScalarsInjectiveResolutionHomE
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafRestrictScalarsInjectiveResolutionHomExists : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S),
    ∃ m : ∀ n : ℤ, (restr φ).obj ((res S F).X n) ⟶ (res R ((restr φ).obj F)).X n,
      (∀ i j : ℤ, (restr φ).map ((res S F).d i j) ≫ m j = m i ≫ (res R ((restr φ).obj F)).d i j) ∧
      (restr φ).map (resι S F) ≫ m 0 = resι R ((restr φ).obj F)

namespace LateralTheory.EtaleFoundations

theorem etaleSheaf_restrictScalars_resolution_comparison_of_hom (hH : EtaleSheafRestrictScalarsInjectiveResolutionHomExists) : EtaleRestrictScalarsResolutionCompatible := by
  intro R S _ _ φ F U a
  obtain ⟨m, hc, h0⟩ := hH R S φ F
  have hex : ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)), ∀ (U : Scheme.{0}) (a : Sec F U),
      ρ.app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
    refine ⟨⟨fun U s => ((m s).hom.app (op U)).hom.toAddMonoidHom, ?_, ?_⟩, ?_⟩
    · intro V U g s x
      have h := (m s).hom.naturality g.op
      exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x).symm
    · intro U s t x
      have h := congrArg (fun f : (restr φ).obj ((res S F).X s) ⟶ (res R ((restr φ).obj F)).X t => (f.hom.app (op U)).hom x) (hc s t)
      exact h.symm
    · intro U x
      exact congrArg (fun f : (restr φ).obj F ⟶ (res R ((restr φ).obj F)).X 0 => (f.hom.app (op U)).hom x) h0
  exact pick_spec hex U a

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafSectionLocallyIffOfPresheafFacts
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_sheaf_section_locally_iff_of_presheaf_facts : EtaleLocalIffAffineEtaleCoverPointwise := by
  intro U P hP
  constructor
  · rintro ⟨S, hS, hSP⟩ x
    obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := (@Etale : MorphismProperty Scheme.{0}))).mp hS
    obtain ⟨i, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).mp 𝒰.mem₀).1 x
    let 𝒱 := (𝒰.X i).affineCover
    obtain ⟨z, hz⟩ := 𝒱.covers y
    refine ⟨𝒱.X (𝒱.idx y), 𝒱.f (𝒱.idx y) ≫ 𝒰.f i, inferInstance, ?_, ⟨z, ?_⟩, ?_⟩
    · have : Etale (𝒰.f i) := 𝒰.map_prop i
      infer_instance
    · simp only [Scheme.Hom.comp_apply, hz, hy]
    · exact hSP _ _ (S.downward_closed (hle _ _ (Presieve.ofArrows.mk i)) _)
  · intro h
    choose V g hA hE hx hPg using h
    refine ⟨{ arrows := fun W k => P W k, downward_closed := fun {Y Z f} hf k => hP Y Z f k hf }, ?_, ?_⟩
    · refine (Scheme.mem_grothendieckTopology_iff (P := (@Etale : MorphismProperty Scheme.{0}))).mpr ⟨Scheme.Cover.mkOfCovers (P := (@Etale : MorphismProperty Scheme.{0})) U V g (fun x => ⟨x, hx x⟩) (fun x => hE x), ?_⟩
      rintro W k ⟨x⟩
      exact hPg x
    · intro W k hk
      exact hk

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafSectionsEqOfLocallyEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ShfLocPf

theorem etale_sheaf_sections_eq_of_locally_eq : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := by
  intro R _ P
  refine ⟨?_, ?_, ?_⟩
  · intro U y
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) y, ?_⟩
    intro V g hg
    obtain ⟨t, ht⟩ := hg
    exact ⟨t, ht⟩
  · intro U x hx
    have h : ((toSheafify Scheme.etaleTopology P).app (op U)).hom x =
        ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0 := by rw [hx, map_zero]
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) x 0 h, ?_⟩
    intro V g hg
    have hg' : (P.map g.op).hom x = (P.map g.op).hom 0 := hg
    rw [hg', map_zero]
  · intro F φ
    refine ⟨ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology φ F.property), ?_, ?_⟩
    · exact toSheafify_sheafifyLift Scheme.etaleTopology φ F.property
    · intro ψ hψ
      ext1
      exact sheafifyLift_unique Scheme.etaleTopology φ F.property ψ.hom hψ

end LateralTheory.EtaleFoundations.ShfLocPf
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafSectionsGlueOfForgetIsSheaf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem sec_glue_forget_isSheaf (R : Type) [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
  have : PreservesLimitsOfSize.{0, 1} (forget (ModuleCat.{1} (ULift.{1} R))) :=
    preservesLimitsOfSize_shrink.{1, 0, 0, 1} _
  exact (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf Scheme.etaleTopology.{0} F.obj
      (forget (ModuleCat.{1} (ULift.{1} R))) F.property)

theorem etale_sheaf_sections_glue_of_forget_isSheaf : EtaleSheafSectionsSeparatedAndGlue := by
  intro R _ F U
  have hT := sec_glue_forget_isSheaf R F
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨S, hS, h⟩ := hab
    exact (hT S hS).isSeparatedFor.ext (fun V g hg => h V g hg)
  · intro S hS s hs
    let x : Presieve.FamilyOfElements (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) S.arrows :=
      fun V g hg => s V g hg
    have hc : x.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro V W g k hg
      exact (hs V W g k hg).symm
    obtain ⟨t, ht, -⟩ := hT S hS x hc
    exact ⟨t, fun V g hg => ht g hg⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafShortComplexExactIffLocalLiftsHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExactIffPf

variable {R : Type} [CommRing R]

theorem inj_of_mono {F G : Shv R} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (Sec.map φ (U := U)) := by
  have : Mono φ.hom := inferInstance
  have : Mono (φ.hom.app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem ker_sec {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) (b : Sec F U) (hb : Sec.map φ b = 0) :
    ∃ k : Sec (kernel φ) U, Sec.map (kernel.ι φ) k = b := by
  let E := sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙
    (evaluation _ _).obj (op U)
  have hl : IsLimit (Fork.ofι (E.map (kernel.ι φ))
      (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero, comp_zero]) :
      Fork (E.map φ) 0) := isLimitOfHasKernelOfPreservesLimit E φ
  let M := LinearMap.ker (φ.hom.app (op U)).hom
  let s : ModuleCat.of (ULift.{1} R) M ⟶ E.obj F := ModuleCat.ofHom M.subtype
  have hs : s ≫ E.map φ = s ≫ 0 := by
    ext x
    simp [s, E]
  obtain ⟨l, hl'⟩ := Fork.IsLimit.lift' hl s hs
  refine ⟨l.hom ⟨b, hb⟩, ?_⟩
  have := congrArg (fun m => m.hom (⟨b, hb⟩ : M)) hl'
  simpa [s, E] using this

theorem exact_iff (S : ShortComplex (Shv R)) : S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 →
    Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  rw [S.exact_iff_epi_kernel_lift, ← Sheaf.isLocallySurjective_iff_epi' (φ := kernel.lift S.g S.f S.zero)]
  set φ := kernel.lift S.g S.f S.zero with hφ
  have hfac : ∀ V (a : Sec S.X₁ V), Sec.map (kernel.ι S.g) (Sec.map φ a) = Sec.map S.f a := by
    intro V a
    show ((φ ≫ kernel.ι S.g).hom.app (op V)).hom a = _
    rw [hφ, kernel.lift_ι]
  have hnat : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (k : Sec (kernel S.g) U),
      Sec.map (kernel.ι S.g) (Sec.res g k) = Sec.res g (Sec.map (kernel.ι S.g) k) := by
    intro V U g k
    have := congrArg (fun m => m.hom k) ((kernel.ι S.g).hom.naturality g.op)
    simp [Sec.map, Sec.res] at this ⊢
  constructor
  · intro h U b hb
    obtain ⟨k, rfl⟩ := ker_sec S.g U b hb
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} φ.hom k, ?_⟩
    rintro V g ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← hfac]
    rw [show Sec.map φ t = Sec.res g k from ht, hnat]
  · intro h
    constructor
    intro U k
    obtain ⟨T, hT, hTk⟩ := h U (Sec.map (kernel.ι S.g) k) (by
      show ((kernel.ι S.g ≫ S.g).hom.app (op U)).hom k = 0
      rw [kernel.condition]; rfl)
    refine Scheme.etaleTopology.superset_covering ?_ hT
    intro V g hg
    obtain ⟨a, ha⟩ := hTk V g hg
    refine ⟨a, ?_⟩
    apply inj_of_mono (kernel.ι S.g) V
    change Sec.map (kernel.ι S.g) (Sec.map φ a) = Sec.map (kernel.ι S.g) (Sec.res g k)
    rw [hfac, hnat, ha]

end LateralTheory.EtaleFoundations.ExactIffPf

theorem LateralTheory.EtaleFoundations.etale_sheaf_short_complex_exact_iff_local_lifts_holds : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts := by
  intro R _ S
  exact LateralTheory.EtaleFoundations.ExactIffPf.exact_iff S
end

