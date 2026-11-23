module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenSpread

set_option backward.isDefEq.respectTransparency false

section Bundles

variable {W X Y : Scheme.{0}}

theorem lbIso_pullback {L M : LB X} (h : LBIso L M) (j : Y ⟶ X) : LBIso (L.pull j) (M.pull j) :=
  LBIso.chartPull (GlobalTheory.chartPullPull L j) (GlobalTheory.chartPullPull M j) h

theorem lbIso_pull_pull {L : LB X} (hL : L.IsLB) {a : Y ⟶ X} (j : W ⟶ Y) {a' : W ⟶ X} (ha : a' = j ≫ a) :
    LBIso (L.pull a') ((L.pull a).pull j) :=
  LBIso.chartPull (chartPullSame L _ _ _ j fun _ => ha) (GlobalTheory.chartPullPull _ j) (lbIso_refl (pull_isLB hL a))

theorem lbIso_pull_comp {Z : Scheme.{0}} {L : LB X} {M : LB Z} {a : Y ⟶ X} {b : Y ⟶ Z} (j : W ⟶ Y) {a' : W ⟶ X}
    {b' : W ⟶ Z} (ha : a' = j ≫ a) (hb : b' = j ≫ b) (h : LBIso (L.pull a) (M.pull b)) :
    LBIso (L.pull a') (M.pull b') :=
  LBIso.chartPull (chartPullSame L _ _ _ j fun _ => ha) (chartPullSame M _ _ _ j fun _ => hb) h

theorem lbIso_pull_of_lbIso {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : W ⟶ Y) {a' : W ⟶ X}
    (ha : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (GlobalTheory.chartPullPull M j) (chartPullSame L _ _ _ j fun _ => ha) h

end Bundles

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_forall_mem {V : (Sp R).Opens} (hV : genericPoint (Sp R) ∈ V) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ z : Sp R', spMap g z ∈ V := by
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hV V.isOpen
  refine ⟨a, ?_, fun R' _ g hg z => hle ?_⟩
  · rintro rfl
    simp at ha
  · exact fun h => z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hg)

theorem exists_forall_notMem {C : Set (Sp R)} (hC : IsClosed C)
    (h : ∀ z : Sp K, spMap (algebraMap R K) z ∉ C) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ z : Sp R', spMap g z ∉ C := by
  have hg : genericPoint (Sp R) ∈ Set.range (spMap (algebraMap R K)) := by
    rw [(IsGenericPointHom.fractionField R K).range_eq]; rfl
  obtain ⟨z, hz⟩ := hg
  exact exists_forall_mem (V := ⟨Cᶜ, hC.isOpen_compl⟩) (hz ▸ h z)

theorem exists_isPullback_stalk {Y Y₀ : Scheme.{0}} {p : Y ⟶ Sp R} {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K}
    (h : IsPullback φ p₀ p (spMap (algebraMap R K))) :
    ∃ p₁, IsPullback φ p₁ p ((Sp R).fromSpecStalk (genericPoint (Sp R))) := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  refine ⟨p₀ ≫ e.hom, h.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp) ?_⟩
  simpa using he.symm

theorem exists_lift_open {S S' Y Y' : Scheme.{0}} (p : Y ⟶ S) (V : S.Opens) {π : Y' ⟶ Y} {p' : Y' ⟶ S'}
    {t : S' ⟶ S} (w : π ≫ p = p' ≫ t) (ht : ∀ z, t z ∈ V) :
    ∃ l : Y' ⟶ pullback p V.ι, l ≫ pullback.fst p V.ι = π := by
  refine ⟨pullback.lift π (IsOpenImmersion.lift V.ι (p' ≫ t) ?_) ?_, pullback.lift_fst _ _ _⟩
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact ht _
  · exact w.trans (IsOpenImmersion.lift_fac _ _ _).symm

theorem exists_hom {Y X Y₀ : Scheme.{0}} (p : Y ⟶ Sp R) [QuasiCompact p] [QuasiSeparated p] (q : X ⟶ Sp R)
    [LocallyOfFinitePresentation q] {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K}
    (h : IsPullback φ p₀ p (spMap (algebraMap R K))) (u₀ : Y₀ ⟶ X) (hu : u₀ ≫ q = φ ≫ p) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (Y' : Scheme.{0}) (π : Y' ⟶ Y) (p' : Y' ⟶ Sp R'), π ≫ p = p' ≫ spMap g →
        ∃ u : Y' ⟶ X, u ≫ q = π ≫ p ∧ ∀ φ' : Y₀ ⟶ Y', φ' ≫ π = φ → φ' ≫ u = u₀ := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨V, hV, -, w, u, hw, hwu, hq⟩ := StalkLimit.exists_spread h₁ q u₀ hu
  obtain ⟨a, ha, H⟩ := exists_forall_mem hV
  refine ⟨a, ha, fun R' _ g hg Y' π p' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open p V e (H R' g hg)
  refine ⟨l ≫ u, by rw [Category.assoc, hq, reassoc_of% hl], fun φ' hφ' => ?_⟩
  have : φ' ≫ l = w := by
    rw [← cancel_mono (pullback.fst p V.ι), Category.assoc, hl, hφ', hw]
  rw [reassoc_of% this, hwu]

theorem exists_lbIso {Y Y₀ : Scheme.{0}} (p : Y ⟶ Sp R) [QuasiCompact p] [QuasiSeparated p]
    {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K} (h : IsPullback φ p₀ p (spMap (algebraMap R K))) {M N : LB Y}
    (hM : M.IsLB) (hN : N.IsLB) (H : LBIso (M.pull φ) (N.pull φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (Y' : Scheme.{0}) (π : Y' ⟶ Y) (p' : Y' ⟶ Sp R'), π ≫ p = p' ≫ spMap g →
        LBIso (M.pull π) (N.pull π) := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit h₁
  obtain ⟨V₀⟩ : Nonempty (StalkLimit.AffNhd (genericPoint (Sp R))) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((StalkLimit.diagram _ p).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V₀.1.ι)
  have : QuasiSeparatedSpace ((StalkLimit.diagram _ p).obj V₀) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V₀.1.ι)
  let ι₀ : (StalkLimit.diagram _ p).obj V₀ ⟶ Y := pullback.fst p V₀.1.ι
  have e₀ : φ = (StalkLimit.cone h₁).π.app V₀ ≫ ι₀ := (StalkLimit.cone_π_fst h₁ V₀).symm
  obtain ⟨V, i, HV⟩ := exists_lbIso_of_isLimit (StalkLimit.diagram _ p) (fun V => (StalkLimit.cone h₁).π.app V)
    (fun i => (StalkLimit.cone h₁).w i) hc (M.pull ι₀) (N.pull ι₀) (pull_isLB hM _) (pull_isLB hN _)
    (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _)
      (lbIso_pull_pull hM _ e₀).symm
      (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) H (lbIso_pull_pull hN _ e₀)))
  have e₁ : pullback.fst p V.1.ι = (StalkLimit.diagram _ p).map i ≫ ι₀ := (StalkLimit.diagram_map_fst _ p i).symm
  have HV' : LBIso (M.pull (pullback.fst p V.1.ι)) (N.pull (pullback.fst p V.1.ι)) :=
    LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _) (lbIso_pull_pull hM _ e₁)
      (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) HV
        (lbIso_pull_pull hN _ e₁).symm)
  obtain ⟨a, ha, Ha⟩ := exists_forall_mem V.2.1
  refine ⟨a, ha, fun R' _ g hg Y' π p' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open p V.1 e (Ha R' g hg)
  exact lbIso_pull_comp l hl.symm hl.symm HV'

theorem exists_projective_model {X₀ : Scheme.{0}} (f₀ : X₀ ⟶ Sp K) [IsProper f₀] {L₀ : LB X₀}
    (hL : IsAmpleLB L₀) (hL' : L₀.IsLB) :
    ∃ (X : Scheme.{0}) (f : X ⟶ Sp R) (φ : X₀ ⟶ X) (H : LB X) (N : ℕ), IsProper f ∧
      IsPullback φ f₀ f (spMap (algebraMap R K)) ∧ H.IsLB ∧ IsAmpleLB H ∧ 1 ≤ N ∧ LBIso (lbPow L₀ N) (H.pull φ) := by
  obtain ⟨N, hN, M, s, hs⟩ := hL.exists_veryAmpleBy f₀
  obtain ⟨hs, hc⟩ := (ProjSpace.veryAmpleBy_iff f₀ s).1 hs
  let c := ProjSpace.toProj f₀ s hs
  let u := ProjSpace.baseChange M (algebraMap R K)
  have hu := ProjSpace.isPullback_baseChange M (algebraMap R K)
  have : Flat (spMap (algebraMap R K)) := flat_specMap_localization (nonZeroDivisors R) K
  have : Mono (spMap (algebraMap R K)) := mono_specMap_localization (nonZeroDivisors R) K
  have : Flat u := MorphismProperty.of_isPullback (P := @Flat) hu.flip inferInstance
  have : Mono u := MorphismProperty.of_isPullback (P := .monomorphisms _) hu.flip
    (inferInstanceAs (Mono (spMap (algebraMap R K))))
  have : QuasiCompact u := MorphismProperty.of_isPullback (P := @QuasiCompact) hu.flip inferInstance
  have hp := isPullback_toImage_of_isClosedImmersion (c ≫ u) c u rfl
  have := isProper_str R M
  refine ⟨(c ≫ u).image, (c ≫ u).imageι ≫ PSpace.str R M, (c ≫ u).toImage,
    (ProjSpace.O1 R M).pull (c ≫ u).imageι, N, inferInstance, ?_, pull_isLB (ProjSpace.O1_isLB R M) _,
    (isAmple_projective_O_one R M).pull_of_isClosedImmersion _, hN, ?_⟩
  · have := hp.flip.paste_vert hu
    rwa [ProjSpace.toProj_str] at this
  · have h1 {Y : Scheme.{0}} (F : Y ⟶ PSpace R M) := pull_isLB (ProjSpace.O1_isLB R M) F
    refine LBIso.trans (isLB_lbPow hL' _) (pull_isLB (ProjSpace.O1_isLB K M) c) (pull_isLB (h1 _) _)
      (ProjSpace.lbIso_pullback_O1_toProj f₀ s hs).symm ?_
    refine LBIso.trans (pull_isLB (ProjSpace.O1_isLB K M) c) (h1 (c ≫ u)) (pull_isLB (h1 _) _)
      (lbIso_pull_of_lbIso (ProjSpace.lbIso_pull_O1 M (algebraMap R K)).symm c rfl) ?_
    exact lbIso_pull_pull (ProjSpace.O1_isLB R M) _ (Scheme.Hom.toImage_imageι _).symm

theorem exists_isAmpleLB {X X₀ : Scheme.{0}} (f : X ⟶ Sp R) [QuasiCompact f] [QuasiSeparated f]
    {φ : X₀ ⟶ X} {f₀ : X₀ ⟶ Sp K} (h : IsPullback φ f₀ f (spMap (algebraMap R K))) {L H : LB X} {L₀ : LB X₀}
    (hL : L.IsLB) (hH : H.IsLB) (hL₀ : L₀.IsLB) (hA : IsAmpleLB H) {N : ℕ} (hN : 1 ≤ N)
    (e : LBIso L₀ (L.pull φ)) (e' : LBIso (lbPow L₀ N) (H.pull φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) →
        IsAmpleLB (L.pull π) := by
  obtain ⟨a, ha, Ha⟩ := exists_lbIso f h (isLB_lbPow hL N) hH
    (LBIso.trans (pull_isLB (isLB_lbPow hL N) _) (isLB_lbPow (pull_isLB hL _) N) (pull_isLB hH _)
      (lbIso_lbPow_pull hL φ N).symm
      (LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (isLB_lbPow hL₀ N) (pull_isLB hH _) (lbIso_lbPow e N).symm e'))
  refine ⟨a, ha, fun R' _ g hg X' π f' hp => ?_⟩
  have : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) hp.flip inferInstance
  refine (isAmpleLB_pow_iff (pull_isLB hL π) hN).1 ((hA.pull_of_isAffineHom π).of_lbIso
    (isLB_lbPow (pull_isLB hL _) N) ?_)
  exact LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow hL N) _) (pull_isLB hH _)
    (lbIso_lbPow_pull hL π N) (Ha R' g hg X' π f' hp.w)

end GlobalTheory.GenSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSplitTorusExtensionDescentGaloisInvariant
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem exists_splitExt_of_galois_invariant :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] [GrpObj B₀], IsAbelianScheme B₀ → ∀ (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap (algebraMap k K)) φG → IsGrpPullback B B₀ (spMap (algebraMap k K)) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G), IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → (∀ (τ : K ≃ₐ[k] K) (s : G.left ⟶ G.left), s ≫ φG = φG → s ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) → s ≫ q.left ≫ φ = q.left ≫ φ ∧ GlobalTheory.SplitTorus.bcMap (spMap (τ : K →+* K)) X ≫ i.left = i.left ≫ s) → ∃ S : SplitExt (Sp k), S.IsGt G₀ := by
  intro k K _ _ _ _ _ G₀ B₀ _ _ _ hB₀ G B _ _ X _ _ _ φG φ hG hB q i hq hfl hsu hqc hi H hinv
  have spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
      spMap (g.comp f) = spMap g ≫ spMap f := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl

  have spMap_surjective' {A B : Type} [CommRing A] [CommRing B] (y : Sp B ⟶ Sp A) :
      ∃ f : A →+* B, spMap f = y :=
    ⟨(Spec.preimage y).hom, by simp [spMap]⟩

  have spMap_inj_lemma_3 {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
      f = g := by
    have h' := Spec.map_injective h
    exact congrArg CommRingCat.Hom.hom h'

  have hc : GlobalTheory.ZM.IsGaloisCover (K ≃ₐ[k] K) (fun σ => spMap (σ : K →+* K)) (spMap (algebraMap k K)) := by
    refine
      { finite := inferInstance
        one := ?_
        mul := ?_
        inv := ?_
        fin := ?_
        etale := ?_
        onto := ?_
        fibre := ?_ }
    · show Spec.map _ = _
      convert Spec.map_id (CommRingCat.of K)
      rfl
    · intro a c
      show spMap (((a * c : K ≃ₐ[k] K) : K →+* K)) = _
      rw [← spMap_comp_moduli_spaces]
      rfl
    · intro a
      rw [← spMap_comp_moduli_spaces]
      congr 1
      ext r
      exact a.commutes r
    · show IsFinite (Spec.map _)
      rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr inferInstance
    · show Etale (Spec.map _)
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      show (algebraMap k K).Etale
      rw [RingHom.etale_algebraMap]
      exact ⟨Algebra.FormallyEtale.of_isSeparable k K, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    · exact ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
    · intro k' _ _ y y' h
      obtain ⟨f, rfl⟩ := spMap_surjective' y
      obtain ⟨f', rfl⟩ := spMap_surjective' y'
      rw [← spMap_comp_moduli_spaces, ← spMap_comp_moduli_spaces] at h
      have hfa := spMap_inj_lemma_3 h
      let _ : Algebra k k' := (f.comp (algebraMap k K)).toAlgebra
      let φ : K →ₐ[k] k' := { f with commutes' := fun _ => rfl }
      let φ' : K →ₐ[k] k' :=
        { f' with commutes' := fun r => (RingHom.congr_fun hfa r).symm }
      let Φ : (K ≃ₐ[k] K) → (K →ₐ[k] k') := fun a => φ.comp a.toAlgHom
      have hinj : Function.Injective Φ := by
        intro a b hab
        ext x
        exact f.injective (AlgHom.congr_fun hab x)
      have hcard : Nat.card (K →ₐ[k] k') ≤ Nat.card (K ≃ₐ[k] K) := by
        rw [IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, AlgHom.card]
      obtain ⟨a, ha⟩ := (hinj.bijective_of_nat_card_le hcard).2 φ'
      refine ⟨a, ?_, fun b hb => ?_⟩
      · show spMap f ≫ spMap (a : K →+* K) = spMap f'
        rw [← spMap_comp_moduli_spaces]
        congr 1
        ext x
        exact AlgHom.congr_fun ha x
      · have hb' : f.comp (b : K →+* K) = f' := by
          have hb0 : spMap f ≫ spMap (b : K →+* K) = spMap f' := hb
          rw [← spMap_comp_moduli_spaces] at hb0
          exact spMap_inj_lemma_3 hb0
        apply hinj
        ext x
        exact (RingHom.congr_fun hb' x).trans (AlgHom.congr_fun ha x).symm
  have coverPull {A B A' B' : Scheme} {p : A ⟶ B} {p' : A' ⟶ B'}
      {Γ : Type} [Group Γ] {ρ : Γ → (A ⟶ A)} {ρ' : Γ → (A' ⟶ A')}
      {u : A' ⟶ A} {v : B' ⟶ B} (h : GlobalTheory.ZM.IsGaloisCover Γ ρ p)
      (hp : IsPullback u p' p v) (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
      (hin : ∀ a, ρ' a ≫ p' = p') : GlobalTheory.ZM.IsGaloisCover Γ ρ' p' :=
    ((GlobalTheory.ZM.galoisCover_descent A B p Γ ρ h).2.2 A' B' p' ρ' u v hu hp.w).2 hp hin
  have coverDesc {A B : Scheme} {p : A ⟶ B} {Γ : Type} [Group Γ]
      {ρ : Γ → (A ⟶ A)} (h : GlobalTheory.ZM.IsGaloisCover Γ ρ p)
      {Z : Scheme} (f : A ⟶ Z) (hf : ∀ a, ρ a ≫ f = f) :
      ∃! f' : B ⟶ Z, p ≫ f' = f :=
    (GlobalTheory.ZM.galoisCover_descent A B p Γ ρ h).1 Z f hf
  let s : (K ≃ₐ[k] K) → (G.left ⟶ G.left) := fun τ =>
    hG.1.lift φG (G.hom ≫ spMap (τ : K →+* K)) (by rw [Category.assoc, hc.inv, hG.1.w])
  have hs₁ : ∀ τ, s τ ≫ φG = φG := fun τ => hG.1.lift_fst _ _ _
  have hs₂ : ∀ τ, s τ ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) := fun τ => hG.1.lift_snd _ _ _
  have hcG := coverPull hc (ρ' := s) hG.1.flip hs₂ hs₁
  have bcFst {S S' : Scheme} (f : S' ⟶ S) :
      SplitTorus.bcMap f X ≫ Rosenlicht.torusFst S X = Rosenlicht.torusFst S' X :=
    pullback.lift_fst _ _ _
  have hT := SplitTorus.isPullback_bcMap (spMap (algebraMap k K)) X
  have hcT := coverPull hc
    (ρ' := fun τ : K ≃ₐ[k] K => SplitTorus.bcMap (spMap (τ : K →+* K)) X) hT.flip
    (fun τ => SplitTorus.bcMap_hom _ X) (fun τ => pullback.hom_ext
      (by
        have e := bcFst (spMap (algebraMap k K))
        exact (Category.assoc _ _ _).trans ((congrArg _ e).trans
          ((bcFst _).trans e.symm)))
      (by
        have e := SplitTorus.bcMap_hom (spMap (algebraMap k K)) X
        refine (Category.assoc _ _ _).trans ((congrArg _ e).trans (Eq.trans ?_ e.symm))
        rw [SplitTorus.bcMap_hom_assoc, hc.inv]))
  obtain ⟨q', hq', -⟩ := coverDesc hcG (q.left ≫ φ) fun τ => (hinv τ _ (hs₁ τ) (hs₂ τ)).1
  obtain ⟨i', hi', -⟩ := coverDesc hcT (i.left ≫ φG) fun τ => by
    rw [← Category.assoc, (hinv τ _ (hs₁ τ) (hs₂ τ)).2, Category.assoc, hs₁]
  have wq : q' ≫ B₀.hom = G₀.hom :=
    (coverDesc hcG (φG ≫ G₀.hom) fun τ => by rw [← Category.assoc, hs₁]).unique
      (by rw [← Category.assoc, hq', Category.assoc, hB.1.w, ← Category.assoc, Over.w, hG.1.w]) rfl
  have wi : i' ≫ G₀.hom = (splitTorus (Sp k) X).hom :=
    (coverDesc hcT (SplitTorus.bcMap (spMap (algebraMap k K)) X ≫ (splitTorus (Sp k) X).hom)
      fun τ => by rw [← Category.assoc, hcT.inv]).unique
      (by rw [← Category.assoc, hi', Category.assoc, hG.1.w, ← Category.assoc, Over.w, hT.w]) rfl
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := splitTorus_extension_descends k K (algebraMap k K) G B G₀ B₀ X
    φG φ hG hB q i (Over.homMk q' wq) (Over.homMk i' wi) hq' hi' hq hfl hsu hqc hi H
  obtain ⟨O, a, b, c, h⟩ := exists_gtDatum_of_splitTorus_extension (Sp k) X G₀ B₀ hB₀ _ _
    h₁ h₅ h₂ h₃ h₄ h₆
  obtain ⟨d, -⟩ := h hB₀
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory

end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointSpecialFibreSectionNeZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorsionNonzero

section Pull
variable {X Y : Scheme.{0}}

abbrev one (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)

theorem chart_le (L : LB X) {V : X.Opens} (F : Y ⟶ X) (h : ⊤ ≤ F ⁻¹ᵁ V) (k : PUnit → L.ι) :
    (L.pull F).U k ≤ F ⁻¹ᵁ (V ⊓ (one L).U (fun _ => k PUnit.unit)) := fun x hx =>
  ⟨h (x := x) trivial, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx PUnit.unit⟩

theorem appLE_res (F : Y ⟶ X) {U V : X.Opens} {W : Y.Opens} (e : V ≤ U) (h : W ≤ F ⁻¹ᵁ V) (h' : W ≤ F ⁻¹ᵁ U)
    (a : Γ(X, U)) : (F.appLE V W h).hom (resG X e a) = (F.appLE U W h').hom a := by
  rw [← Scheme.Hom.map_appLE F h (homOfLE e).op]
  rfl

theorem res_appLE (F : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens} (e : W' ≤ W) (h : W ≤ F ⁻¹ᵁ U) (h' : W' ≤ F ⁻¹ᵁ U)
    (a : Γ(X, U)) : resG Y e ((F.appLE U W h).hom a) = (F.appLE U W' h').hom a := by
  rw [← Scheme.Hom.appLE_map F h (homOfLE e).op]
  rfl

theorem g_eq {K : Type} [Fintype K] [Unique K] (L : LB X) (F : Y ⟶ X) (i j : K → L.ι)
    (h : _ ≤ F ⁻¹ᵁ (L.U (i default) ⊓ L.U (j default))) :
    ((LB.LinComb L (K := K) (fun _ => F) (fun _ => 1)).g i j).val =
      (F.appLE _ _ h).hom (L.g (i default) (j default)).val := by
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

def pullSec (L : LB X) {V : X.Opens} (σ : ∀ j, Γ(X, V ⊓ (one L).U j)) (hσ : σ ∈ secOn (one L) V) (F : Y ⟶ X)
    (h : ⊤ ≤ F ⁻¹ᵁ V) : (L.pull F).Sec where
  f k := (F.appLE _ _ (chart_le L F h k)).hom (σ fun _ => k PUnit.unit)
  compat i j := by
    have hi := (inf_le_left : (L.pull F).U i ⊓ (L.pull F).U j ≤ _).trans (chart_le L F h i)
    have hj := (inf_le_right : (L.pull F).U i ⊓ (L.pull F).U j ≤ _).trans (chart_le L F h j)
    have hj' : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (one L).U (fun _ => j PUnit.unit) :=
      hj.trans (F.preimage_mono inf_le_right)
    have hi' : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (one L).U (fun _ => i PUnit.unit) :=
      hi.trans (F.preimage_mono inf_le_right)
    have hW : (L.pull F).U i ⊓ (L.pull F).U j ≤
        F ⁻¹ᵁ (V ⊓ (one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit)) := le_inf hi hj'
    have h₁ : (one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit) ≤
        𝟙 X ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      inf_le_inf (LB.wchart_le L _ _ 0) (LB.wchart_le L _ _ 0)
    have h₂ : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      inf_le_inf (LB.wchart_le L _ _ PUnit.unit) (LB.wchart_le L _ _ PUnit.unit)
    have hU : (L.pull F).U i ⊓ (L.pull F).U j ≤
        F ⁻¹ᵁ ((one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit)) := le_inf hi' hj'
    have e := congrArg (F.appLE _ _ hW).hom (hσ (fun _ => i PUnit.unit) (fun _ => j PUnit.unit))
    rw [map_mul, appLE_res F _ hW hi, appLE_res F _ hW hj, appLE_res F _ hW hU] at e
    refine (res_appLE F _ _ hi _).trans (e.trans (congrArg₂ (· * ·) ?_ (res_appLE F _ _ hj _).symm))
    refine (congrArg (F.appLE _ _ hU).hom (g_eq L (𝟙 X) _ _ h₁)).trans (Eq.trans ?_ (g_eq L F i j h₂).symm)
    exact congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val)
      (Scheme.Hom.appLE_comp_appLE F (𝟙 X) _ _ _ h₁ hU)

theorem le_nonzeroLocus_iff (L : LB X) {V : X.Opens} (σ : ∀ j, Γ(X, V ⊓ (one L).U j)) (hσ : σ ∈ secOn (one L) V)
    (F : Y ⟶ X) (h : ⊤ ≤ F ⁻¹ᵁ V) {K : Type} [Field K] (x : Sp K ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (pullSec L σ hσ F h) ↔ ∃ j, valF (x ≫ F) _ (σ j) ≠ 0 := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((Points.le_preimage_iff x _).1 hx)
    have h₁ := (Points.le_preimage_iff x _).2 hk
    have h₂ := Points.le_preimage_mono x (Y.basicOpen_le _) h₁
    have h₃ := (Points.le_preimage_basicOpen_iff x h₂ _).1 h₁
    refine ⟨fun _ => k PUnit.unit, ?_⟩
    rw [Points.valF_eq_valR, ← Points.valR_appLE x F (chart_le L F h k) h₂]
    exact h₃.ne_zero
  · rintro ⟨j, hj⟩
    obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim _ _)⟩
    have h₁ : ⊤ ≤ (x ≫ F) ⁻¹ᵁ (V ⊓ (one L).U fun _ => a) := by
      by_contra hc
      exact hj (dif_neg hc)
    have h₂ : ⊤ ≤ x ⁻¹ᵁ (L.pull F).U (fun _ => a) := fun z hz =>
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (h₁ hz).2 0
    rw [Points.valF_eq_valR, ← Points.valR_appLE x F (chart_le L F h fun _ => a) h₂] at hj
    exact Points.le_preimage_mono x (le_iSup (fun k => Y.basicOpen ((pullSec L σ hσ F h).f k)) fun _ => a)
      ((Points.le_preimage_basicOpen_iff x h₂ _).2 hj.isUnit)

end Pull

theorem exists_torsion_valF_ne_zero : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L → ∀ (N : M.Z.Opens) (σ : Q.SecFam N), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.FibNe N σ → y (cPt p) ∈ N → ∃ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV) ⟶ u.G, t ^ (S.r * S.N) = 1 ∧ ∃ j, valF (X := Q.G.left) (t.left ≫ F) _ (σ j) ≠ 0 := by
  intro laws laws₂ o Ω _ _ _ _ S ρ M U₀ Q hbig p _ y y₀ u jV yV yK hfac F ψ hmap hiso N σ hσ hne hy
  obtain ⟨hj, hyV, -, -⟩ := hfac
  have hloc := ZHPre.isLocalHom_of_test u jV hj
  have hK : IsAlgClosed (IsLocalRing.ResidueField (OO p)) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hsq := hmap.1.1
  set r : Sp (IsLocalRing.ResidueField (OO p)) ⟶ Sp u.V :=
    spMap (IsLocalRing.residue (OO p)) ≫ spMap jV with hr
  have key : ∀ x, r x = IsLocalRing.closedPoint u.V := fun x => by
    have hx : x = IsLocalRing.closedPoint _ :=
      Subsingleton.elim (α := PrimeSpectrum (IsLocalRing.ResidueField (OO p))) _ _
    subst hx
    exact (congrArg (PrimeSpectrum.comap jV)
      (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans (IsLocalRing.comap_closedPoint jV)
  have hrange : Set.range r = {IsLocalRing.closedPoint u.V} := by
    ext x
    exact ⟨fun ⟨a, ha⟩ => ha ▸ key a, fun h => ⟨IsLocalRing.closedPoint _, (key _).trans h.symm⟩⟩
  have hyN : ⊤ ≤ yV ⁻¹ᵁ N := by
    refine (Points.le_preimage_iff yV N).2 ?_
    rw [← hyV] at hy
    rw [← IsLocalRing.comap_closedPoint jV]
    exact hy
  have hF : ⊤ ≤ F ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N) := by
    rw [← Scheme.Hom.comp_preimage, hsq.w]
    exact fun z _ => hyN (x := u.G.hom z) trivial
  let θ := pullSec Q.L.L σ hσ F hF
  have hθ : ∃ x ∈ nonzeroLocus θ, u.G.hom x = IsLocalRing.closedPoint u.V := by
    obtain ⟨g, j, hg, hv⟩ := hne _ (r ≫ yV) (by
      rintro _ ⟨z, rfl⟩
      exact hyN (x := r z) trivial)
    have h₁ := (le_nonzeroLocus_iff Q.L.L σ hσ F hF (hsq.lift g r hg)).2 ⟨j, by rwa [hsq.lift_fst]⟩
    refine ⟨hsq.lift g r hg (IsLocalRing.closedPoint _), h₁ (x := IsLocalRing.closedPoint _) trivial, ?_⟩
    exact (congrArg (fun φ : Sp _ ⟶ Sp u.V => φ (IsLocalRing.closedPoint _)) (hsq.lift_snd g r hg)).trans (key _)
  have hg : u.A.g = S.g := (H1.dim_unique u.A.A.hom u.A.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 ρ.P.smoothDim)
    (eSec u.A.A (IsLocalRing.closedPoint (FractionRing u.V)))).trans ρ.g_eq
  have hN : 4 ≤ S.N := by
    rw [ρ.N_eq]
    have h₂ : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (two_pos.trans_le ρ.two_le).ne' _)
    exact Nat.pow_le_pow_left h₂ 2
  have hn : ((S.r * S.N : ℕ) : IsLocalRing.ResidueField (OO p)) ≠ 0 := by
    have := S.unit.map (Spec.preimage (r ≫ yV ≫ M.s)).hom
    rw [map_natCast] at this
    exact this.ne_zero
  have hlt : 6 * (S.N ^ u.A.g * u.A.g.factorial) < (S.r * S.N) ^ 2 := by
    rw [hg]
    exact hbig.2.2.trans_le (Nat.le_self_pow two_ne_zero _)
  have hc := GlobalTheory.FewZeros.card_torsion_translate_zeros_lt laws laws₂ u.V u.complete u.D u.A u.G u.U (Q.L.L.pull F) θ
    (pull_isLB Q.L.isLB F) hiso hθ _ r S.N (S.r * S.N) hrange hN hn hlt 1
  by_contra hcon
  have heq : Nat.card {h : Over.mk r ⟶ u.G // h ^ (S.r * S.N) = 1 ∧ ¬ ⊤ ≤ (1 * h).left ⁻¹ᵁ nonzeroLocus θ} =
      Nat.card {h : Over.mk r ⟶ u.G // h ^ (S.r * S.N) = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun h => and_iff_left_of_imp fun hh hle => hcon ⟨h, hh, ?_⟩)
    rw [_root_.one_mul] at hle
    exact (le_nonzeroLocus_iff Q.L.L σ hσ F hF h.left).1 hle
  omega

end GlobalTheory.ZH.TorsionNonzero
end
end

