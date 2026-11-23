module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleApprox

theorem relAmple_of_lbIso_self {S : Scheme.{0}} {A : Over S} [IsProper A.hom] {L L' : LB A.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (e : LBIso L' L) (hA : Out.RelAmple A L) : Out.RelAmple A L' := by
  have e' : LBIso L' (L.pull (𝟙 _)) := e.chartPull (chartPullId _) (Geo.Tor.chartPullPull L _ _ rfl)
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (f := 𝟙 S) (φ := 𝟙 A.left)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) hL hL' e' hA

variable {R : Type} [CommRing R] {R₁ : Subring R} [IsNoetherianRing R₁] {A₀ : Over (Sp R₁)} [IsProper A₀.hom]
  [Flat A₀.hom] {M : LB A₀.left} {B : Over (Sp R)} {φ : B.left ⟶ A₀.left} {N : LB B.left}

theorem exists_basicOpen (hM : M.IsLB) (hφ : IsPullback φ B.hom A₀.hom (spMap R₁.subtype)) (hN : N.IsLB)
    (e : LBIso N (M.pull φ)) (hB : Out.RelAmple B N) (x : PrimeSpectrum R) :
    ∃ r : R₁, (r : R) ∉ x.asIdeal ∧
      Out.RelAmple ((Over.pullback (Scheme.Opens.ι (X := Sp R₁) (PrimeSpectrum.basicOpen r))).obj A₀)
        (M.pull (pullback.fst A₀.hom (Scheme.Opens.ι (X := Sp R₁) (PrimeSpectrum.basicOpen r)))) := by
  let k := x.asIdeal.ResidueField
  let xr : R₁ →+* k := (algebraMap R k).comp R₁.subtype
  let p : Ideal R₁ := RingHom.ker xr
  have : p.IsPrime := RingHom.ker_isPrime xr
  let g := algebraMap R₁ p.ResidueField
  let i : p.ResidueField →+* k := Ideal.ResidueField.lift p xr le_rfl fun a ha => IsUnit.mk0 _ ha
  have hi : i.comp g = xr := RingHom.ext fun a => Ideal.ResidueField.lift_algebraMap p xr le_rfl
    (fun a ha => IsUnit.mk0 _ ha) a
  have hu : spMap (algebraMap R k) ≫ spMap R₁.subtype = spMap i ≫ spMap g := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi]
  have h₂ := IsPullback.of_hasPullback A₀.hom (spMap i ≫ spMap g)
  have hfib : Out.RelAmple ((Over.pullback (spMap g)).obj A₀) (M.pull (pullback.fst A₀.hom (spMap g))) :=
    FibreAmple.relAmple_of_fieldExtension hM i (IsPullback.of_hasPullback A₀.hom (spMap g)) h₂
      (LB.isLB_pull hM _) (GlobalTheory.lbIso_refl (LB.isLB_pull hM _))
      (FibreAmple.relAmple_of_factor hM hφ h₂ _ hu hN e hB)
  obtain ⟨r, hr, hA⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre A₀ hM g (FibreAmple.residueField_fraction p) hfib
  refine ⟨r, fun hx => hr (Ideal.algebraMap_residueField_eq_zero.2 (RingHom.mem_ker.2 ?_)), hA⟩
  exact Ideal.algebraMap_residueField_eq_zero.2 hx

theorem relAmple_spread_subring (hM : M.IsLB) (hφ : IsPullback φ B.hom A₀.hom (spMap R₁.subtype)) (hN : N.IsLB)
    (e : LBIso N (M.pull φ)) (hB : Out.RelAmple B N) :
    ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (B₂ : Over (Sp R₂))
      (π : B₂.left ⟶ A₀.left), IsPullback π B₂.hom A₀.hom (spMap (Subring.inclusion h)) →
        Out.RelAmple B₂ (M.pull π) := by
  classical
  choose r hr hA using exists_basicOpen hM hφ hN e hB
  have hspan : Ideal.span (Set.range fun x => (r x : R)) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hr ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  have h1 : (1 : R) ∈ Submodule.span R (Set.range fun x => (r x : R)) := by
    change (1 : R) ∈ Ideal.span _
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h1
  refine ⟨c.support.image c, fun R₂ h hF B₂ π hπ => ?_⟩
  have hcR : ∀ x ∈ c.support, c x ∈ R₂ := fun x hx => hF (Finset.mem_image_of_mem c hx)
  have : IsProper B₂.hom := MorphismProperty.of_isPullback (P := @IsProper) hπ ‹_›
  refine GlobalTheory.AmpleLocal.relAmple_of_locally _ B₂ (M.pull π) (pull_isLB hM π) inferInstance inferInstance
    fun s => ?_
  obtain ⟨x, -, hxs⟩ : ∃ x ∈ c.support, Subring.inclusion h (r x) ∉ (s : PrimeSpectrum R₂).asIdeal := by
    by_contra hne
    push_neg at hne
    have key : (∑ y ∈ c.support.attach, (⟨c y, hcR y y.2⟩ : R₂) * Subring.inclusion h (r y)) = 1 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one, ← hc, Finsupp.sum]
      exact Finset.sum_attach c.support (fun y => c y • (r y : R))
    apply (s : PrimeSpectrum R₂).isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← key]
    exact Ideal.sum_mem _ fun y _ => Ideal.mul_mem_left _ _ (hne y y.2)
  let D : (Sp R₁).Opens := PrimeSpectrum.basicOpen (r x)
  let U : (Sp R₂).Opens := PrimeSpectrum.basicOpen (Subring.inclusion h (r x))
  refine ⟨U, hxs, ?_⟩
  have sq : IsPullback ((B₂.hom ⁻¹ᵁ U).ι ≫ π) (B₂.hom ∣_ U) A₀.hom (U.ι ≫ spMap (Subring.inclusion h)) :=
    (isPullback_morphismRestrict B₂.hom U).flip.paste_horiz hπ
  have hrange : Set.range (U.ι ≫ spMap (Subring.inclusion h)) ⊆ Set.range D.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have hz : U.ι z ∈ (U : Set (Sp R₂)) := by
      first
        | exact (Scheme.Opens.range_ι U) ▸ ⟨z, rfl⟩
        | (rw [← Scheme.Opens.range_ι U]; exact ⟨z, rfl⟩)
        | exact z.2
    exact hz
  have hA' := FibreAmple.relAmple_of_factor hM (IsPullback.of_hasPullback A₀.hom D.ι) sq
    (IsOpenImmersion.lift D.ι _ hrange) (IsOpenImmersion.lift_fac _ _ _) (LB.isLB_pull hM _)
    (GlobalTheory.lbIso_refl (LB.isLB_pull hM _)) (hA x)
  have : IsProper (Over.mk (B₂.hom ∣_ U)).hom := inferInstanceAs (IsProper (B₂.hom ∣_ _))
  exact relAmple_of_lbIso_self (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _)
    (FibreAmple.lbIso_pull_pull hM _ _) hA'

end GlobalTheory.AmpleApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidSymmetricBundleDescendsToSubringFinset
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RigSymDescent

theorem axes_sq {S' S : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {ψ : G'.left ⟶ G.left} {ψ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hG : IsGrpPullback G' G f ψ)
    (sq : Geo.Tor.IsSquare ψ ψ₂) :
    (lift (1 : G' ⟶ G') (𝟙 G')).left ≫ ψ₂ = ψ ≫ (lift (1 : G ⟶ G) (𝟙 G)).left ∧
    (lift (𝟙 G') (1 : G' ⟶ G')).left ≫ ψ₂ = ψ ≫ (lift (𝟙 G) (1 : G ⟶ G)).left ∧
    (lift (snd G' G') (fst G' G')).left ≫ ψ₂ = ψ₂ ≫ (lift (snd G G) (fst G G)).left := by
  let U : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk ψ hG.1.w
  have o₁ : (1 : G' ⟶ G').left ≫ ψ = ψ ≫ (1 : G ⟶ G).left :=
    congrArg (fun q => q.left) ((map_one (pushHom hG G')).trans (MonObj.comp_one U).symm)
  have e : ∀ (x y : G' ⟶ G') (x₀ y₀ : G ⟶ G), x.left ≫ ψ = ψ ≫ x₀.left → y.left ≫ ψ = ψ ≫ y₀.left →
      (lift x y).left ≫ ψ₂ = ψ ≫ (lift x₀ y₀).left := fun x y x₀ y₀ hx hy =>
    (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (G'.hom ≫ f)) (𝟙 G'.left) x y ψ x₀ y₀
      ((Category.id_comp _).trans hx) ((Category.id_comp _).trans hy))
  refine ⟨e _ _ _ _ o₁ (by simp), e _ _ _ _ (by simp) o₁, ?_⟩
  exact (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk ((G' ⊗ G').hom ≫ f))
    (𝟙 (G' ⊗ G').left) _ _ ψ₂ _ _ ((Category.id_comp _).trans sq.2.symm) ((Category.id_comp _).trans sq.1.symm))

end GlobalTheory.RigSymDescent

namespace GlobalTheory


open GlobalTheory.CechPic in
theorem rigSym_descends_to_subring_containing_finset : ∀ (R : Type) [CommRing R] (R₁ : Subring R) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₁ → P.IsLB → P₁.IsLB → IsGrpPullback A A₁ (spMap R₁.subtype) φ → Geo.Tor.IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → IsTrivial (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → IsTrivial (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (A₂ : Over (Sp R₂)) [GrpObj A₂] (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π → Geo.Tor.IsSquare π π₂ → IsTrivial ((P₁.pull π₂).pull (lift (1 : A₂ ⟶ A₂) (𝟙 A₂)).left) ∧ IsTrivial ((P₁.pull π₂).pull (lift (𝟙 A₂) (1 : A₂ ⟶ A₂)).left) ∧ LBIso (P₁.pull π₂) ((P₁.pull π₂).pull (lift (snd A₂ A₂) (fst A₂ A₂)).left) := by
  intro R _ R₁ A _ P A₁ _ P₁ φ φ₂ hab hP hP₁ hA sq hiso h1 h2 hs
  classical
  have := hab.proper
  haveI : QuasiCompact (A₁ ⊗ A₁).hom := inferInstanceAs (QuasiCompact (pullback.fst A₁.hom A₁.hom ≫ A₁.hom))
  haveI : QuasiSeparated (A₁ ⊗ A₁).hom :=
    inferInstanceAs (QuasiSeparated (pullback.fst A₁.hom A₁.hom ≫ A₁.hom))
  obtain ⟨e₁, e₂, e₃⟩ := GlobalTheory.RigSymDescent.axes_sq hA sq
  have hc : cls P hP = pull φ₂ (cls P₁ hP₁) := (cls_eq_iff hP (pull_isLB hP₁ _)).2 hiso
  have hT := LB.isLB_triv A₁.left
  have z : ∀ {Y : Scheme.{0}} (g : Y ⟶ A₁.left), pull g (cls _ hT) = 0 := fun g => map_zero (pull g)

  have d₁ : LBIso ((P₁.pull (lift (1 : A₁ ⟶ A₁) (𝟙 A₁)).left).pull φ) ((LB.triv A₁.left).pull φ) := by
    refine (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).1 ?_
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp, ← e₁, pull_comp, ← hc,
      ← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_zero_iff _).2 h1
  have d₂ : LBIso ((P₁.pull (lift (𝟙 A₁) (1 : A₁ ⟶ A₁)).left).pull φ) ((LB.triv A₁.left).pull φ) := by
    refine (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).1 ?_
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp, ← e₂, pull_comp, ← hc,
      ← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_zero_iff _).2 h2
  have d₃ : LBIso (P₁.pull φ₂) ((P₁.pull (lift (snd A₁ A₁) (fst A₁ A₁)).left).pull φ₂) := by
    refine (cls_eq_iff (pull_isLB hP₁ _) (pull_isLB (pull_isLB hP₁ _) _)).1 ?_
    rw [cls_pull hP₁, cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, ← e₃, pull_comp, ← hc,
      ← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_iff hP (pull_isLB hP _)).2 hs
  obtain ⟨F₁, H₁⟩ := lbIso_descends_to_subring_containing_finset R R₁ A.left A₁.left A.hom A₁.hom φ _ _ hA.1
    (pull_isLB hP₁ _) hT d₁
  obtain ⟨F₂, H₂⟩ := lbIso_descends_to_subring_containing_finset R R₁ A.left A₁.left A.hom A₁.hom φ _ _ hA.1
    (pull_isLB hP₁ _) hT d₂
  obtain ⟨F₃, H₃⟩ := lbIso_descends_to_subring_containing_finset R R₁ (A ⊗ A).left (A₁ ⊗ A₁).left (A ⊗ A).hom
    (A₁ ⊗ A₁).hom φ₂ _ _ (SiegDesc.isPullback_of_isSquare hA.1 sq) hP₁ (pull_isLB hP₁ _) d₃
  refine ⟨F₁ ∪ F₂ ∪ F₃, fun R₂ h hF A₂ _ π π₂ hB sqB => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.RigSymDescent.axes_sq hB sqB
  have k₁ := H₁ R₂ h hF.1.1 A₂.left A₂.hom π hB.1
  have k₂ := H₂ R₂ h hF.1.2 A₂.left A₂.hom π hB.1
  have k₃ := H₃ R₂ h hF.2 (A₂ ⊗ A₂).left (A₂ ⊗ A₂).hom π₂ (SiegDesc.isPullback_of_isSquare hB.1 sqB)
  refine ⟨(cls_eq_zero_iff (pull_isLB (pull_isLB hP₁ _) _)).1 ?_, (cls_eq_zero_iff (pull_isLB (pull_isLB hP₁ _) _)).1 ?_,
    (cls_eq_iff (pull_isLB hP₁ _) (pull_isLB (pull_isLB hP₁ _) _)).1 ?_⟩
  · have := (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).2 k₁
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp] at this
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, f₁]
    exact this
  · have := (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).2 k₂
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp] at this
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, f₂]
    exact this
  · have := (cls_eq_iff (pull_isLB hP₁ _) (pull_isLB (pull_isLB hP₁ _) _)).2 k₃
    rw [cls_pull hP₁, cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp] at this
    rw [cls_pull hP₁, cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, f₃]
    exact this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericPointIntegralSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.IntEval
open GlobalTheory.UT.CoefBasic GlobalTheory.BoxExpansion GlobalTheory.UT.EvalZero

theorem alg_value_at {M K : Type} [CommRing M] [Fintype K] {k : ℕ} {P E Fv : Mˣ} {Sσ sA cv cl : M} {u d : K → M}
    (h₁ : Sσ = (P ^ k).val * sA) (h₂ : Sσ = ∑ i, u i) (h₃ : sA = cv * (E ^ k).val) (h₄ : P.val * E.val = cl * Fv.val)
    (h₅ : ∀ i, u i = d i * (Fv ^ k).val) : cv * cl ^ k = ∑ i, d i := by
  refine (Fv ^ k).mul_left_inj.1 ?_
  rw [Finset.sum_mul, ← Finset.sum_congr rfl fun i _ => h₅ i, ← h₂, h₁, h₃]
  simp only [Units.val_pow_eq_pow_val]
  calc cv * cl ^ k * Fv.val ^ k = cv * (cl * Fv.val) ^ k := by ring
    _ = cv * (P.val * E.val) ^ k := by rw [h₄]
    _ = _ := by ring

theorem value_at_section : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp R)) ⟶ G) (l : FractionRing R) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))), IntTerm.Ext U x h → (∀ (z : (TF (R := R) (FractionRing R)).left) (JA : ((TF (R := R) (FractionRing R)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := R) (FractionRing R)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (Geo.Tor.gw (Y := (TF (R := R) (FractionRing R)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG (toUnit (TF (R := R) (FractionRing R)) ≫ h).left) (fun _ => JA x.left)).val * (val (Z := (TF (R := R) (FractionRing R)).left) e (𝟙 _) z JA).val = GlobalTheory.UT.cst (FractionRing R) z l * (val f (toUnit (TF (R := R) (FractionRing R))).left z JG).val) → ∀ (k : ℕ) (s : SecA A (FractionRing R) k) (σ' : U.SecGF (FractionRing R) k), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) (FractionRing R)) A.A).left (U.genF (FractionRing R)).left s (UnifPre.gFK (G := G) (FractionRing R)) (𝟙 _) σ' → ∀ (n : ℕ) (c : Fin n → FractionRing R) (σ : Fin n → H0 U.LG.L k), GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) (FractionRing R)) (fun _ => (k : ℤ)) σ' (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) (FractionRing R)) (fun i => scal (fst (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left (c i)) → ∀ xs : Fin n → R, (∀ (i : Fin n) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι), Good U.LG.L z J → sval (σ i) (r ≫ h.left) z J = Geo.Tor.cst r z (xs i) * (val f r z J ^ k).val) → ∀ v : FractionRing R, ValAt s x e v → v * l ^ k = ∑ i, c i * algebraMap R (FractionRing R) (xs i) := by
  intro R _ _ I D A G _ _ U w₀ x e h l f hExt hF k s σ' hR n c σ hσ xs hxs v hv
  obtain ⟨z⟩ := exists_pt (R := R) (F := FractionRing R)
  obtain ⟨JA, hA⟩ := exists_good' (Z := (TFK (R := R) (FractionRing R)).left) A.isLB z
  obtain ⟨JG, hG⟩ := exists_good' (Z := (TFK (R := R) (FractionRing R)).left) U.LG.isLB z
  let r : TFK (R := R) (FractionRing R) ⟶ UnifPre.GF (G := G) (FractionRing R) := lift (𝟙 _) (x ≫ U.gen.inv)
  have e₁ : r.left ≫ (snd (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left =
      x.left ≫ U.gen.inv.left := by
    rw [← Over.comp_left, lift_snd]; rfl
  have e₂ : r.left ≫ (U.genF (FractionRing R)).left = (ptSecT A.A x).left := by
    rw [← Over.comp_left]
    congr 1
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp [r, ptSecT]
    · simp [r, ptSecT]
  have e₀ : (toUnit (TF (R := R) (FractionRing R))).left = jFK (R := R) (FractionRing R) ≫ jK R := by
    simpa using Over.w (toUnit (TF (R := R) (FractionRing R)))
  have e₃ : r.left ≫ UnifPre.gFK (G := G) (FractionRing R) = (toUnit (TF (R := R) (FractionRing R)) ≫ h).left := by
    rw [← Category.assoc, e₁, Category.assoc]; exact hExt
  have e₄ : r.left ≫ (fst (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have e₅ : (x.left ≫ U.gen.inv.left) ≫ U.gen.hom.left = x.left := by
    rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id]; exact Category.comp_id _
  have e₆ : (x.left ≫ U.gen.inv.left) ≫ pullback.fst G.hom (jK R) = (toUnit (TF (R := R) (FractionRing R)) ≫ h).left := by
    rw [Category.assoc]; exact hExt
  have a₁ := isoRel_val hR r.left z hA hG
  rw [Category.comp_id, e₁, e₂, e₅, e₆] at a₁
  have a₂ := secLin_val hσ r.left z hG
  rw [e₃] at a₂
  have a₃ := hv z JA hA
  rw [GlobalTheory.UT.NonVan.val_powFrame, zpow_natCast] at a₃
  have a₄ := hF z JA JG hA hG

  rw [cst_eq] at a₃ a₄
  apply cstH_inj (R := R) z
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_pow, map_sum]
  refine alg_value_at a₁ a₂ a₃ a₄ (fun i => ?_)
  have b : gs r.left z ⊤ (scal (fst (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left (c i)) =
      cstH (R := R) z (c i) :=
    ((gs_pull _ _ z ⊤ trivial _).trans (by rw [e₄]; rfl)).trans (cst_eq (R := R) z _)
  have cb : Geo.Tor.cst (toUnit (TF (R := R) (FractionRing R))).left z (xs i) =
      cstH (R := R) z (algebraMap (FractionRing R) (FractionRing R) (algebraMap R _ (xs i))) := by
    rw [e₀]; exact cst_base (R := R) (FractionRing R) z (xs i)
  rw [b, Over.comp_left, hxs i _ _ z JG hG, cb, map_mul, _root_.mul_assoc]
  simp

end GlobalTheory.Poinc.IntEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointCongruentTermSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntEval

theorem value_sub_sum_mem_hRed : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (h : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g → ∀ (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, g.b.left] (DegPre.lineε 1))) (e k : ℕ), GlobalTheory.Poinc.IntEval.TRel U h g.b f t e → ∀ (σ : H0 U.LG.L k) (fs : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt e k σ fs → ∀ x : R, (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι), Good U.LG.L z J → sval σ (r ≫ h.left) z J = Geo.Tor.cst r z x * (val f r z J ^ k).val) → ∀ a : D.toPre.X → R, (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → sval (fs α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a α) * (val (L := D.toPre.P.L) D.toPre.rig r z J ^ k).val) → ∃ S : Finset D.toPre.X, ∀ T : Finset D.toPre.X, S ⊆ T → x - ∑ α ∈ T, a α ∈ I ^ (e + 1) := by
  intro R _ _ I D A G _ _ U h g hF f t e k hT σ fs hE x hx a ha
  let s : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e (𝟙_ (Over (Sp R)))).left :=
    pullback.lift (thick R I e) (𝟙 _) (by simp)
  have hs1 : s ≫ (fstG I e (𝟙_ (Over (Sp R)))).left = thick R I e := pullback.lift_fst _ _ _
  have hs2 : s ≫ ((Over.pullback (thick R I e)).map h).left = hRed I h e := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
    · rw [Category.assoc]
      erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  obtain ⟨hb, hχ⟩ := hF e
  have hp : hRed I h e ≫ pGl U e = thick R I e ≫ g.b.left := by
    rw [← hs2, Category.assoc, ← hb, ← Category.assoc, hs1]
  have hf : hRed I h e ≫ fGl I G e = thick R I e ≫ h.left := hRed_fst h e
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ fs hE
  have hc : ∀ (z : Sp (R ⧸ I ^ (e + 1))) (c : R),
      cst (thick R I e) z c = cst (𝟙 _) z (Ideal.Quotient.mk (I ^ (e + 1)) c) := fun z c => H1.gs_spec _ z c
  refine ⟨S, fun T hT' => ?_⟩
  rw [← Ideal.Quotient.eq]
  refine H1.cst_ext fun z => ?_
  rw [← hc, ← hc, GlobalTheory.ExpansionValueZero.cst_sum]
  choose J hJ using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
  choose J' hJ' using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ G.left => exists_chart U.LG.isLB (ψ z)
  have hJ : Good D.toPre.P.L z J := hJ
  have hJ' : Good U.LG.L z J' := hJ'
  obtain ⟨h₀, h₁⟩ := hS _ (hRed I h e) z J hJ
  have h₂ := h₁ (J' (hRed I h e ≫ fGl I G e)) (hJ' (hRed I h e ≫ fGl I G e))
  have hsv : sv U k σ (hRed I h e ≫ fGl I G e) z (J' (hRed I h e ≫ fGl I G e)) =
      cst (thick R I e) z x * (val f (thick R I e) z J' ^ k).val := by
    rw [hf]
    exact (sval_of σ _ z J' (fun _ => J' (thick R I e ≫ h.left)) (fun _ => by rw [Category.comp_id])).symm.trans
      (hx _ _ z J' hJ')
  have ht : ∀ α, val (tG U e α) (hRed I h e) z J = val (g.s α) (thick R I e) z J := fun α => by
    have e₁ := (val_pull hJ (tG U e α) ((Over.pullback (thick R I e)).map h).left s).symm
    have e₂ := (val_corr hJ (hχ α) s).symm
    have e₃ := val_pull hJ (g.s α) (fstG I e (𝟙_ (Over (Sp R)))).left s
    rw [hs2] at e₁
    rw [hs1] at e₃
    exact e₁.trans (e₂.trans e₃)
  have hg : ∀ α, sval (fs α) (hRed I h e ≫ pGl U e) z J = sval (fs α) (thick R I e ≫ g.b.left) z J := fun α => by
    rw [hp]
  have hTR := hT _ (𝟙 _) z J J' hJ hJ'
  simp only [Category.id_comp] at hTR
  refine (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).mul_left_inj.1 ?_
  rw [Finset.sum_mul, ← Finset.sum_subset hT' (fun α _ hα => (ha α _ _ z J hJ).symm.trans
    (by rw [← hg, h₀ α hα, zero_mul, zero_mul]))]
  have L₁ : cst (thick R I e) z x * (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).val =
      ((wv U e (hRed I h e) z (J (hRed I h e ≫ pGl U e)) (J' (hRed I h e ≫ fGl I G e)) ^ k).val *
        sv U k σ (hRed I h e ≫ fGl I G e) z (J' (hRed I h e ≫ fGl I G e))) *
        (val t (thick R I e) z J ^ k).val := by
    rw [hsv, ← hTR]
    simp only [mul_pow, Units.val_mul]
    ring
  rw [L₁, h₂, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [ht, hg]
  exact ha α _ _ z J hJ

end GlobalTheory.Poinc.IntEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsAdjointNefSeparateEtaleFibreStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_adjointNef_separate_etaleFibre : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)], IsProjOver p → IsProjOver (f ≫ p) → 1 ≤ n → letI := algebraΓOfHom p; letI := algebraΓOfHom (f ≫ p); ∀ (K : CanonLB (f ≫ p) n) (N : LB W) (hN : N.IsLB) (N' B : LB M) (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (x : Sp ℂ ⟶ W) (U : W.Opens), IsNef ℂ N → IsBig ℂ N → IsNef ℂ (N.pull f) → IsBig ℂ (N.pull f) → IsNef ℂ N' → (n + 1).choose 2 < m → cls B hB = m • CechPic.pull f (cls N hN) + cls N' hN' → x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → Etale (f ∣_ U) → (∀ (Z : Closeds W) (e : ℕ), IsIrreducible (Z : Set W) → Set.range x ⊆ Z → 1 ≤ e → topologicalKrullDim (Z : Set W) = e → 0 < interNumRed ℂ Z fun _ : Fin e => N) → ∀ (J : Type) [Fintype J] (z : J → (Sp ℂ ⟶ M)), Function.Injective z → (∀ j, z j ≫ f = x) → ∀ (k : J → (tens K.bundle B).ι) (hk : ∀ j, ⊤ ≤ z j ⁻¹ᵁ (tens K.bundle B).U (k j)) (a : J → ℂ), (∀ g : H0 (f ≫ p) (tens K.bundle B) ⊤, ∑ j, a j * H0.val (z j) (k j) le_top (hk j) g = 0) → a = 0 := by
  first | exact @GlobalTheory.EtaleSep.sections_separate_fibre | exact GlobalTheory.EtaleSep.sections_separate_fibre | (intros; apply GlobalTheory.EtaleSep.sections_separate_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqOfSpMapSubtypeCompEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory

theorem sections_eq_of_spMap_subtype_comp_eq : ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X : Scheme.{0})
    (p : X ⟶ Sp R₀) [IsSeparated p] (x y : Sp R₀ ⟶ X), x ≫ p = y ≫ p →
    spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y → x = y := by
  intro R _ R₀ X p _ x y hp hR
  let l : Sp R₀ ⟶ pullback p p := pullback.lift x y hp
  let c : pullback (pullback.diagonal p) l ⟶ Sp R₀ := pullback.snd _ _
  haveI : IsClosedImmersion c := inferInstance
  have e1 : l ≫ pullback.fst p p = x := pullback.lift_fst _ _ _
  have e2 : l ≫ pullback.snd p p = y := pullback.lift_snd _ _ _
  have hc : c ≫ x = c ≫ y := by
    have h1 : c ≫ l ≫ pullback.fst p p = c ≫ l ≫ pullback.snd p p := by
      rw [← Category.assoc c l, ← Category.assoc c l]
      change (pullback.snd (pullback.diagonal p) l ≫ l) ≫ _ = (pullback.snd (pullback.diagonal p) l ≫ l) ≫ _
      rw [← pullback.condition, Category.assoc, Category.assoc,
        pullback.diagonal_fst, pullback.diagonal_snd]
    rwa [e1, e2] at h1
  let k : Sp R ⟶ pullback (pullback.diagonal p) l :=
    pullback.lift (spMap R₀.subtype ≫ x) (spMap R₀.subtype) (by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc, e1]
      · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc, e2, hR])
  have hk : k ≫ c = spMap R₀.subtype := pullback.lift_snd _ _ _
  obtain ⟨hZ, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine c
  have hinj0 : Function.Injective (spMap R₀.subtype).appTop := by
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom R₀.subtype)
    have : (spMap R₀.subtype).appTop = (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom ≫
        CommRingCat.ofHom R₀.subtype ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
      rw [← Category.assoc, ← e]; simp
    rw [this]
    intro a b hab
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hab
    have := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective hab
    exact (Scheme.ΓSpecIso (CommRingCat.of R₀)).commRingCatIsoToRingEquiv.injective (Subtype.val_injective this)
  have hinj : Function.Injective c.appTop := by
    rw [← hk, Scheme.Hom.comp_appTop] at hinj0
    simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hinj0
    exact hinj0.of_comp
  haveI : IsIso c.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  haveI : IsIso c :=
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine c)).mpr
      (inferInstanceAs (IsIso (Spec.map c.appTop)))
  rw [← cancel_epi c]
  exact hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapCompEqOfCompInjectiveLocalSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specMap_comp_eq_of_comp_injective_localScheme : ∀ {Y : Scheme.{0}} {W R' V : Type} [CommRing W] [IsLocalRing W] [CommRing R'] [CommRing V] (u : Sp W ⟶ Y) (g₁ g₂ : W →+* R') (η' : R' →+* V), Function.Injective η' → spMap (η'.comp g₁) ≫ u = spMap (η'.comp g₂) ≫ u → spMap g₁ ≫ u = spMap g₂ ≫ u := by
  first | exact @GlobalTheory.TInj.spMap_comp_eq_of_injective | exact GlobalTheory.TInj.spMap_comp_eq_of_injective | (intros; apply GlobalTheory.TInj.spMap_comp_eq_of_injective <;> assumption)
end

