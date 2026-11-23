module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfIsClosedImmersionOfThickeningsOfIsProper
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ThickeningClosed in
theorem isIso_of_isClosedImmersion_of_thickenings_of_isProper {R : Type} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (Y : Over (Spec (CommRingCat.of R))) [IsProper Y.hom] {Z : Scheme.{0}} (j : Z ⟶ Y.left)
    [IsClosedImmersion j]
    (h : ∀ n : ℕ, ∃ l : (thickObj R I n Y).left ⟶ Z, l ≫ j = (fstG I n Y).left) : IsIso j := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have h' : ∀ n : ℕ, ∃ l : pullback Y.hom (thick R I n) ⟶ Z, l ≫ j = pullback.fst Y.hom (thick R I n) :=
    fun n => h n
  have hnear : ∀ x : Y.left, x ∈ zeroLocusOpen j.ker := by
    by_contra hne
    simp only [not_forall] at hne
    obtain ⟨x₀, hx₀⟩ := hne
    have hSc : IsClosed (zeroLocusOpen j.ker)ᶜ := (isOpen_zeroLocusOpen j.ker).isClosed_compl
    have hT : IsClosed (Y.hom '' (zeroLocusOpen j.ker)ᶜ) := Y.hom.isClosedMap _ hSc
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal (Y.hom x₀).asIdeal (Y.hom x₀).isPrime.ne_top
    have hcl : (⟨m, hm.isPrime⟩ : PrimeSpectrum (CommRingCat.of R)) ∈ closure {Y.hom x₀} :=
      (PrimeSpectrum.le_iff_mem_closure _ _).mp hpm
    obtain ⟨x, hxS, hx⟩ :=
      closure_minimal (Set.singleton_subset_iff.mpr
        (Set.mem_image_of_mem _ hx₀ : Y.hom x₀ ∈ Y.hom '' (zeroLocusOpen j.ker)ᶜ)) hT hcl
    apply hxS
    refine ThickeningClosed.mem_of_thickenings I Y.hom j h' x ?_
    rw [hx]
    exact hI.trans (sInf_le ⟨bot_le, hm⟩)
  have hker : j.ker = ⊥ := by
    ext U a
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Submodule.mem_bot]
    constructor
    · intro ha
      have hJ : LinearMap.ker (LinearMap.toSpanSingleton Γ(Y.left, U) Γ(Y.left, U) a) = ⊤ := by
        by_contra hJ
        obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal _ hJ
        obtain ⟨s, hs, hsa⟩ :=
          ThickeningClosed.exists_mul_eq_zero_of_mem j.ker U ⟨q, hq.isPrime⟩ (hnear _) ha
        exact hs (hJq (by simp [LinearMap.mem_ker, hsa]))
      have h1 : (1 : Γ(Y.left, U)) ∈ LinearMap.ker (LinearMap.toSpanSingleton Γ(Y.left, U) Γ(Y.left, U) a) :=
        hJ ▸ Submodule.mem_top
      simpa using h1
    · rintro rfl
      exact zero_mem _
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker

theorem hom_eq_of_thickenings_of_isProper : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (Y Z : Over (Spec (CommRingCat.of R))) [IsProper Y.hom] [IsSeparated Z.hom] (f g : Y ⟶ Z), (∀ e, (fstG I e Y).left ≫ f.left = (fstG I e Y).left ≫ g.left) → f = g := by
  intro R _ _ _ I hI Y Z _ _ f g hfg
  have hf : f.left ≫ Z.hom = Y.hom := Over.w f
  have hg : g.left ≫ Z.hom = Y.hom := Over.w g
  obtain ⟨φ, hφ⟩ : ∃ φ : Y.left ⟶ pullback Z.hom Z.hom,
      φ = pullback.lift f.left g.left (hf.trans hg.symm) := ⟨_, rfl⟩
  have hφ1 : φ ≫ pullback.fst Z.hom Z.hom = f.left := by rw [hφ, pullback.lift_fst]
  have hφ2 : φ ≫ pullback.snd Z.hom Z.hom = g.left := by rw [hφ, pullback.lift_snd]
  have hι : IsIso (pullback.fst φ (pullback.diagonal Z.hom)) := by
    refine isIso_of_isClosedImmersion_of_thickenings_of_isProper I hI Y _ fun n => ?_
    refine ⟨pullback.lift (fstG I n Y).left ((fstG I n Y).left ≫ f.left) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · simp [hφ1]
    · simp [hφ2, hfg n]
  have key : φ = inv (pullback.fst φ (pullback.diagonal Z.hom)) ≫
      pullback.snd φ (pullback.diagonal Z.hom) ≫ pullback.diagonal Z.hom := by
    rw [← pullback.condition, IsIso.inv_hom_id_assoc]
  apply Over.OverMorphism.ext
  rw [← hφ1, ← hφ2, key]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndGeometricallyConnectedOfIsNilpotent
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilProper

theorem isSeparated_of_comp_surjective {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  let m := pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 S) (by simp) (by simp)
  have hm : UniversallyClosed m :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹_› ‹_› rfl rfl
  have hcomm : pullback.diagonal (j ≫ f) ≫ m = j ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.diagonal_fst_assoc]
      simp
    · rw [Category.assoc, pullback.lift_snd, pullback.diagonal_snd_assoc]
      simp
  have key : m '' Set.range (pullback.diagonal (j ≫ f)) = Set.range (pullback.diagonal f) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨j x, by rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := j.surjective y
      exact ⟨_, ⟨x, rfl⟩, by rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]⟩
  refine ⟨IsClosedImmersion.of_isPreimmersion _ ?_⟩
  rw [← key]
  exact m.isClosedMap _ (pullback.diagonal (j ≫ f)).isClosedEmbedding.isClosed_range

theorem surjective_specMap_mk (A : Type) [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) :
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
  obtain ⟨n, hn⟩ := hJ
  have hle : J ≤ nilradical A := fun x hx ↦ by
    rw [mem_nilradical]
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hle).2⟩

theorem isProper_and_geometricallyConnected_of_isNilpotent :
    ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (Y : Over (Spec (CommRingCat.of A))) [LocallyOfFiniteType Y.hom], (IsProper (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) → IsProper Y.hom) ∧ (GeometricallyConnected (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) → GeometricallyConnected Y.hom) := by
  intro A _ J hJ Y _
  have hsq : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    surjective_specMap_mk A J hJ
  have hci : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨fun hP ↦ ?_, fun hG ↦ ?_⟩
  · have hcomp : IsProper (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
        ≫ Y.hom) := by
      rw [pullback.condition]
      infer_instance
    have : IsSeparated Y.hom :=
      isSeparated_of_comp_surjective (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) Y.hom
    have : UniversallyClosed Y.hom :=
      UniversallyClosed.of_comp_surjective (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) Y.hom
    exact { toIsSeparated := ‹_›, toUniversallyClosed := ‹_›, toLocallyOfFiniteType := ‹_› }
  · rw [geometricallyConnected_iff] at hG ⊢
    intro K _ y Z fst snd h
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    have hker : ∀ x ∈ J, φ.hom x = 0 := by
      obtain ⟨n, hn⟩ := hJ
      intro x hx
      have hx' : x ^ n = 0 := by
        have := Ideal.pow_mem_pow hx n
        rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      exact (IsNilpotent.map ⟨n, hx'⟩ φ.hom).eq_zero
    let ψ := Ideal.Quotient.lift J φ.hom hker
    have hφ : φ = CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom ψ := by
      ext x
      simp [ψ]
    rw [hφ, Spec.map_comp] at h
    let p : Z ⟶ pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
      pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [h.w, Category.assoc])
    apply hG (Spec.map (CommRingCat.ofHom ψ)) p snd
    have e : p ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) = fst :=
      pullback.lift_fst _ _ _
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [e]
    exact h

end GlobalTheory.NilProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackPullbackMap
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorusExtBaseChange

theorem isPullback_pullback_map {S S' : Scheme.{0}} (f : S' ⟶ S) {G B : Over S} (q : G ⟶ B) :
    IsPullback (pullback.fst G.hom f) ((Over.pullback f).map q).left q.left (pullback.fst B.hom f) := by
  have h1 : ((Over.pullback f).map q).left ≫ pullback.fst B.hom f = pullback.fst G.hom f ≫ q.left :=
    pullback.lift_fst _ _ _
  have h2 : ((Over.pullback f).map q).left ≫ pullback.snd B.hom f = pullback.snd G.hom f :=
    pullback.lift_snd _ _ _
  refine IsPullback.of_bot ?_ h1.symm (IsPullback.of_hasPullback B.hom f)
  rw [h2, Over.w q]
  exact IsPullback.of_hasPullback _ _

theorem exists_extension {S S' : Scheme.{0}} (f : S' ⟶ S) {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    {T' G' B' : Over S'} [GrpObj T'] [GrpObj G'] [GrpObj B']
    (eT : T' ≅ (Over.pullback f).obj T) (eG : G' ≅ (Over.pullback f).obj G)
    (eB : B' ≅ (Over.pullback f).obj B) [IsMonHom eT.hom] [IsMonHom eG.hom] [IsMonHom eB.hom]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] (hf : Flat q.left) (hs : Surjective q.left)
    (ha : IsAffineHom q.left) (hk : IsPullback i (toUnit _) q η[B]) :
    ∃ (q' : G' ⟶ B') (i' : T' ⟶ G'), IsMonHom q' ∧ Flat q'.left ∧ Surjective q'.left ∧
      IsAffineHom q'.left ∧ IsMonHom i' ∧ IsPullback i' (toUnit _) q' η[B'] ∧
      q'.left ≫ eB.hom.left ≫ pullback.fst B.hom f = (eG.hom.left ≫ pullback.fst G.hom f) ≫ q.left ∧
      i'.left ≫ eG.hom.left ≫ pullback.fst G.hom f = (eT.hom.left ≫ pullback.fst T.hom f) ≫ i.left := by
  have pq := isPullback_pullback_map f q
  have pi := isPullback_pullback_map f i
  have iG : IsIso eG.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eG.hom))
  have iB : IsIso eB.inv.left := inferInstanceAs (IsIso ((Over.forget _).map eB.inv))
  have hf' : Flat ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq hf
  have hs' : Surjective ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq hs
  have ha' : IsAffineHom ((Over.pullback f).map q).left := MorphismProperty.of_isPullback pq ha
  refine ⟨eG.hom ≫ (Over.pullback f).map q ≫ eB.inv, eT.hom ≫ (Over.pullback f).map i ≫ eG.inv,
    inferInstance, ?_, ?_, ?_, inferInstance, ?_, ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · rw [Over.comp_left, Over.comp_left]; infer_instance
  · refine (hk.map (Over.pullback f)).of_iso eT.symm eG.symm
      (Functor.Monoidal.εIso (Over.pullback f)).symm eB.symm ?_ (toUnit_unique _ _) ?_ ?_
    · simp
    · simp
    · have : η[(Over.pullback f).obj B] ≫ eB.inv = η[B'] := IsMonHom.one_hom _
      rw [← this, Functor.obj.η_def]
      simp
  · rw [← Over.comp_left_assoc, Category.assoc, Category.assoc, eB.inv_hom_id, Category.comp_id,
      Over.comp_left, Category.assoc, Category.assoc, pq.w]
  · rw [← Over.comp_left_assoc, Category.assoc, Category.assoc, eG.inv_hom_id, Category.comp_id,
      Over.comp_left, Category.assoc, Category.assoc, pi.w]

theorem exists_iso_of_square {S S' S₀ S₀' : Scheme.{0}} (f : S' ⟶ S) (f₀ : S₀' ⟶ S₀) (j : S₀ ⟶ S)
    (j' : S₀' ⟶ S') (w : j' ≫ f = f₀ ≫ j) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G']
    (bc : G' ≅ (Over.pullback f).obj G) [IsMonHom bc.hom] :
    ∃ e : (Over.pullback j').obj G' ≅ (Over.pullback f₀).obj ((Over.pullback j).obj G), IsMonHom e.hom ∧
      e.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom f₀ ≫ pullback.fst G.hom j =
        pullback.fst G'.hom j' ≫ bc.hom.left ≫ pullback.fst G.hom f :=
  Geo.Tor.grpPullback_iso
    (((Geo.Tor.isGrpPullback_pullback G' j').comp
      (((Geo.Tor.isGrpPullback_of_iso bc).comp (Geo.Tor.isGrpPullback_pullback G f)).congr
        (Category.id_comp _) rfl)).congr w rfl)
    ((Geo.Tor.isGrpPullback_pullback _ f₀).comp (Geo.Tor.isGrpPullback_pullback G j))

theorem exists_splitTorus_iso {S S' : Scheme.{0}} (f : S' ⟶ S) {X X' : Type} [AddCommGroup X]
    [AddCommGroup X'] (xe : X' ≃+ X) :
    ∃ e : splitTorus S' X' ≅ (Over.pullback f).obj (splitTorus S X), IsMonHom e.hom ∧
      ∀ x : X', (e.hom.left ≫ pullback.fst (splitTorus S X).hom f).appTop.hom (charUnit S X (xe x)).val =
        (charUnit S' X' x).val := by
  obtain ⟨e, he, hc⟩ := splitTorus_baseChange S S' f X
  let e₀ : splitTorus S' X' ≅ splitTorus S' X :=
    { hom := SplitTorus.torusMap S' xe.symm.toAddMonoidHom
      inv := SplitTorus.torusMap S' xe.toAddMonoidHom
      hom_inv_id := by
        rw [← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_id]; congr 1; ext; simp
      inv_hom_id := by
        rw [← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_id]; congr 1; ext; simp }
  have : IsMonHom e₀.hom := SplitTorus.isMonHom_torusMap _
  refine ⟨e₀ ≪≫ e, inferInstanceAs (IsMonHom (e₀.hom ≫ e.hom)), fun x => ?_⟩
  rw [Iso.trans_hom, Over.comp_left, Category.assoc, Rosenlicht.appTop_comp_apply, hc,
    SplitTorus.charUnit_val, SplitTorus.charUnit_val]
  refine (SplitTorus.torusMap_appTop_chi xe.symm.toAddMonoidHom (xe x)).trans ?_
  simp

end TorusExtBaseChange


open TorusExtBaseChange in
theorem gtCoord_baseChange_maps : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (I : Ideal R) (I' : Ideal R'), I.map φ ≤ I' → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (e : ℕ) (g : GtCoord I D e G), ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left) (q' : thickObj R' I' e G' ⟶ thickObj R' I' e D'.P.A) (i' : splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X ⟶ thickObj R' I' e G'), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ IsMonHom q' ∧ Flat q'.left ∧ Surjective q'.left ∧ IsAffineHom q'.left ∧ IsMonHom i' ∧ IsPullback i' (toUnit _) q' (η[thickObj R' I' e D'.P.A]) ∧ ((Over.map (thick R' I' e)).map q' ≫ D'.prBe I' e).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ g.pG.left ∧ ∃ hT : (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) D'.X).left ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left, i'.left ≫ h = hT ≫ g.i.left ∧ ∀ x : D'.X, hT.appTop.hom (charUnit _ D.X (hD.xe x)).val = (charUnit _ D'.X x).val := by
  intro R R' _ _ _ _ φ D D' hD I I' hI G _ _ G' _ _ bc hbc e g
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hI _
  let f₀ : Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ hle))
  have w : thick R' I' e ≫ specOf φ = f₀ ≫ thick R I e := by
    simp only [f₀, thick, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
  have := hD.e_hom
  have := g.q_hom
  have := g.i_hom
  obtain ⟨eG, mG, hG⟩ := exists_iso_of_square _ f₀ _ _ w G G' bc
  obtain ⟨eB, mB, hB⟩ := exists_iso_of_square _ f₀ _ _ w D.P.A D'.P.A hD.e
  obtain ⟨eT, mT, hT⟩ := exists_splitTorus_iso f₀ hD.xe
  obtain ⟨q', i', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_extension f₀ eT eG eB g.i g.q g.q_flat g.q_surj g.q_affine g.isKernel
  refine ⟨eG.hom.left ≫ pullback.fst _ f₀, q', i', ?_, h1, h2, h3, h4, h5, h6, ?_, _, h8, hT⟩
  · exact (Category.assoc _ _ _).trans hG
  · change (q'.left ≫ pullback.fst D'.P.A.hom (thick R' I' e)) ≫ _ =
      _ ≫ g.q.left ≫ pullback.fst D.P.A.hom (thick R I e)
    rw [Category.assoc, ← hB, ← Category.assoc _ g.q.left, ← h7]
    simp only [Category.assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPushoutQuotientMap
section
namespace GlobalTheory.NilpotentLift

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.NilpotentLift.isPushout_quotient_map {A : Type} [CommRing A] (J : Ideal A) {B : CommRingCat.{0}}
    (σ : CommRingCat.of A ⟶ B) :
    IsPushout σ (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap (J.map σ.hom) σ.hom Ideal.le_comap_map)) := by
  refine IsPushout.of_isColimit' (CommSq.mk ?_) ?_
  · ext a
    simp [Ideal.quotientMap_mk]
  · have key : ∀ s : PushoutCocone σ (CommRingCat.ofHom (Ideal.Quotient.mk J)),
        J.map σ.hom ≤ RingHom.ker s.inl.hom := by
      intro s
      rw [Ideal.map_le_iff_le_comap]
      intro j hj
      have h := congrArg (fun φ => φ.hom j) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      simp [RingHom.mem_ker, h, Ideal.Quotient.eq_zero_iff_mem.mpr hj]
    refine PushoutCocone.IsColimit.mk _
      (fun s => CommRingCat.ofHom (Ideal.Quotient.lift _ s.inl.hom (fun a ha => key s ha)))
      (fun s => ?_) (fun s => ?_) (fun s m h₁ _ => ?_)
    · ext b
      exact Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)
    · ext a
      have h := congrArg (fun φ => φ.hom a) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      exact (Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)).trans h
    · ext b
      have h := congrArg (fun φ => φ.hom b) h₁
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      exact h.trans (Ideal.Quotient.lift_mk (J.map σ.hom) s.inl.hom (fun a ha => key s ha)).symm


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.NilpotentLift.main : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J →
    ∀ (G Y : Over (Spec (CommRingCat.of A))) [Smooth G.hom] [IsAffine Y.left]
      (f₀ : pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⟶ G.left),
      f₀ ≫ G.hom = pullback.fst _ _ ≫ Y.hom →
      (∃ W : G.left.Opens, IsAffineOpen W ∧ f₀ ⁻¹ᵁ W = ⊤) →
      ∃ f : Y ⟶ G, pullback.fst _ _ ≫ f.left = f₀ := by
  intro A _ J hJ G Y _ _ f₀ hf₀ hW
  obtain ⟨W, hWaff, hWtop⟩ := hW
  set e := Y.left.isoSpec with he
  obtain ⟨σ, hσdef⟩ : ∃ σ : CommRingCat.of A ⟶ Γ(Y.left, ⊤),
      σ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ Y.hom.appTop := ⟨_, rfl⟩
  have hσ : e.hom ≫ Spec.map σ = Y.hom := by
    have h1 := Scheme.isoSpec_hom_naturality Y.hom
    rw [Scheme.isoSpec_Spec_hom] at h1
    rw [hσdef, Spec.map_comp, ← Category.assoc, he, h1, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  have hσ' : e.inv ≫ Y.hom = Spec.map σ := by
    rw [← hσ, Iso.inv_hom_id_assoc]
  have hPB := isPullback_SpecMap_of_isPushout _ _ _ _ (_root_.GlobalTheory.NilpotentLift.isPushout_quotient_map J σ)
  have hPB' : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) ≫ e.inv)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J.map σ.hom) σ.hom Ideal.le_comap_map)))
      Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsPullback.of_iso hPB (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, hσ'])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
  have hx₀ : (hPB'.isoPullback.hom ≫ f₀) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) ≫ Spec.map σ := by
    rw [Category.assoc, hf₀, IsPullback.isoPullback_hom_fst_assoc, Category.assoc, hσ']
  obtain ⟨x, hx, hxs⟩ := _root_.GlobalTheory.exists_lift_of_smooth_of_isAffineOpen G.hom
    (isAffineOpen_top (Spec (CommRingCat.of A))) hWaff le_top
    (CommRingCat.ofHom (Ideal.Quotient.mk (J.map σ.hom))) (Spec.map σ) (hPB'.isoPullback.hom ≫ f₀) hx₀
    (by simp)
    (by
      rintro _ ⟨y, rfl⟩
      have : hPB'.isoPullback.hom y ∈ f₀ ⁻¹ᵁ W := by rw [hWtop]; trivial
      simpa using this)
    (by
      intro R' A' _ _ _ _ _ _ π' hπ' φ
      have hsurj : Function.Surjective π' := by
        intro c
        obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective c
        exact ⟨b, (hπ' b).trans hb⟩
      have hnil : IsNilpotent (RingHom.ker π'.toRingHom) := by
        obtain ⟨n, hn⟩ := hJ
        refine ⟨n, eq_bot_iff.mpr ?_⟩
        have hle : RingHom.ker π'.toRingHom ≤ J.map σ.hom := fun b hb =>
          Ideal.Quotient.eq_zero_iff_mem.mp ((hπ' b).symm.trans hb)
        calc _ ≤ (J.map σ.hom) ^ n := Ideal.pow_right_mono hle n
          _ = ⊥ := by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
      exact ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective φ π' hsurj hnil⟩)
  refine ⟨Over.homMk (e.hom ≫ x) (by rw [Category.assoc, hxs, hσ]), ?_⟩
  rw [← cancel_epi hPB'.isoPullback.hom]
  show hPB'.isoPullback.hom ≫ pullback.fst _ _ ≫ e.hom ≫ x = hPB'.isoPullback.hom ≫ f₀
  rw [IsPullback.isoPullback_hom_fst_assoc, Category.assoc, Iso.inv_hom_id_assoc, hx]

end GlobalTheory.NilpotentLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WchartCompLePull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

lemma wchart_comp_le_pull {X X' Y : Scheme.{0}} (L : LB X) {J : Type} [Fintype J]
    (F : J → (X' ⟶ X)) (q : Y ⟶ X') (jN : J → L.ι) :
    LB.wchart L (fun i => q ≫ F i) jN ≤
      LB.wchart (LB.LinComb L F (fun _ => 1)) (fun _ : PUnit => q) (fun _ => jN) :=
  fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy i

end GlobalTheory
end

