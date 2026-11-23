module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TorEnd

theorem exists_lift_valuationSubring {F : Type} [Field F] (O : ValuationSubring F) {M : Type} [CommGroup M]
    (τ : M →* Fˣ) {k : ℕ} (hk : k ≠ 0) (hτ : τ ^ k = 1) :
    ∃ σ : M →* Oˣ, σ ^ k = 1 ∧ ∀ x, ((σ x : O) : F) = τ x := by
  have hp : ∀ x, (τ x : F) ^ k = 1 := fun x => by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hτ, MonoidHom.one_apply, Units.val_one]
  have hm : ∀ x, (τ x : F) ∈ O := fun x => by
    rw [← O.valuation_le_one_iff]
    have := congrArg O.valuation (hp x)
    rw [map_pow, map_one] at this
    exact ((pow_eq_one_iff_of_nonneg zero_le hk).1 this).le
  let σ₀ : M →* O :=
    { toFun := fun x => ⟨τ x, hm x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  refine ⟨σ₀.toHomUnits, MonoidHom.ext fun x => Units.ext (Subtype.ext ?_), fun x => rfl⟩
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  exact hp x

theorem chV_comp_torusMap {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z : Over S}
    (z : Z ⟶ splitTorus S X) (m : Y →+ X) (χ : Y) :
    GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap S m) χ = GlobalTheory.UU.chV z (m χ) := by
  refine Units.ext ?_
  rw [GlobalTheory.UU.chV_val, GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val,
    ← GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_comp_torusMap]

theorem torMatch_of_endChar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G), IsMonHom f → ∀ m, EndChar U f m → TorMatch U U (RingHom.id R) f.left m := by
  intro R _ _ _ hR G _ _ hG D A U f hf m hm F _ _ i₁ i₂ hi k hk τ τ' q q' x x' hτ' hτ hq hqt hq' hqt' hx hx'
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  obtain ⟨s, s₁, s₂, s₃, s₄⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k (Nat.one_le_iff_ne_zero.2 hk0)
  let a : R →+* F := (@algebraMap (FractionRing R) F _ _ i₁).comp (algebraMap R (FractionRing R))
  have ha₂ : a = (@algebraMap (FractionRing R) F _ _ i₂).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun r => hi r
  let ν : Multiplicative D.toPre.X →* Multiplicative D.toPre.X := AddMonoidHom.toMultiplicative m
  have pw : ∀ {B : Type} [CommRing B] (σ : Multiplicative D.toPre.X →* Bˣ), σ ^ k = 1 → σ.comp ν ^ k = 1 :=
    fun σ h => MonoidHom.ext fun χ => DFunLike.congr_fun h (ν χ)
  obtain rfl : τ = τ'.comp ν := MonoidHom.ext fun χ => hτ χ.toAdd
  have e₁ := @s₄ F _ _ i₁ a _ (pw τ' hτ') q x rfl hq hqt hx
  have e₂ := @s₄ F _ _ i₂ a _ hτ' q' x' ha₂ hq' hqt' hx'
  rw [e₁, reassoc_of% e₂]
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing a
  let c : R →+* O := a.codRestrict O.toSubring hO
  have hc : IsLocalHom c := hloc
  obtain ⟨σ, hσ, hστ⟩ := exists_lift_valuationSubring O τ' hk0 hτ'
  have n₁ := s₂ O F c a O.subtype _ (pw σ hσ) _ (pw τ' hτ') rfl fun χ => (hστ (ν χ)).symm
  have n₂ := s₂ O F c a O.subtype _ hσ _ hτ' rfl fun χ => (hστ χ).symm
  suffices key : s O c _ (pw σ hσ) = s O c σ hσ ≫ f by
    rw [n₁, n₂, key, Over.comp_left, Category.assoc]
  have hkO : IsUnit (k : O) := by simpa using hk.map c
  refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap c) k hkO _ _ ?_
    (ResidueField O) (residue O) inferInstance ?_
  · rw [s₁, ← MonObj.pow_comp, s₁, MonObj.one_comp]
  let a₀ : R →+* ResidueField O := (residue O).comp c
  have ha₀ : ∀ r ∈ maximalIdeal R ^ (0 + 1), a₀ r = 0 := fun r hr => by
    rw [zero_add, pow_one] at hr
    exact (residue_eq_zero_iff _).2 (map_nonunit c r hr)
  let σ₀ : Multiplicative D.toPre.X →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp σ
  have hσ₀ : σ₀ ^ k = 1 := MonoidHom.ext fun χ => by
    have := DFunLike.congr_fun hσ χ
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this ⊢
    simp only [σ₀, MonoidHom.comp_apply, ← map_pow, this, map_one]
  have r₁ := s₂ O _ c a₀ (residue O) _ (pw σ hσ) _ (pw σ₀ hσ₀) rfl fun χ => rfl
  have r₂ := s₂ O _ c a₀ (residue O) _ hσ _ hσ₀ rfl fun χ => rfl
  have h₀ := isGrpPullback_pullback G (spMap a₀)
  let z : Over.mk (spMap (RingHom.id (ResidueField O))) ⟶ splitTorus (Sp (ResidueField O)) D.toPre.X :=
    (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
      ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp σ₀)
  have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (σ₀ (Multiplicative.ofAdd χ)) := fun χ => by
    simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]
    rfl
  have t₁ := s₃ _ _ a₀ ha₀ a₀ (RingHom.id _) _ _ h₀ _ (pw σ₀ hσ₀) (z ≫ GlobalTheory.SplitTorus.torusMap _ m) rfl
    fun χ => (chV_comp_torusMap z m χ).trans (hz _)
  have t₂ := s₃ _ _ a₀ ha₀ a₀ (RingHom.id _) _ _ h₀ _ hσ₀ z rfl hz
  have hf₀ : ((Over.pullback (spMap a₀)).map f).left ≫ pullback.fst G.hom (spMap a₀) =
      pullback.fst G.hom (spMap a₀) ≫ f.left := pullback.lift_fst _ _ _
  have hE := hm _ a₀ ha₀ _ _ h₀ _ hf₀
  rw [Over.comp_left, ← r₁, ← reassoc_of% r₂, t₁, t₂, Category.assoc z, ← hE, Category.assoc, ← hf₀]
  simp only [Over.comp_left, Category.assoc]

end GlobalTheory.Poinc.TorEnd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionGenericFibre
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.ConjSeq
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBExtDVR

theorem isOpenImmersion_spMap_fractionRing (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K := by
    refine IsLocalization.Away.mk ϖ ?_ ?_ ?_
    · exact IsUnit.mk0 _ (by
        simpa using (IsFractionRing.injective R K).ne_iff.2 hϖ.ne_zero)
    · intro z
      obtain ⟨⟨x, y, hy⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) z
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (nonZeroDivisors.ne_zero hy) hϖ
      refine ⟨n, x * ↑u⁻¹, ?_⟩
      simp only at h
      rw [map_mul, ← h, hu, _root_.mul_assoc, ← map_mul, ← map_pow]
      congr 2
      rw [mul_right_comm, Units.mul_inv, _root_.one_mul]
    · intro x y h
      exact ⟨0, by rw [IsFractionRing.injective R K h]⟩
  exact IsOpenImmersion.of_isLocalization ϖ

theorem exists_lineBundle_extension_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X Y : Scheme.{0}) (s : X ⟶ Sp R) (t : Y ⟶ Sp K) (a : Y ⟶ X), Smooth s → QuasiCompact s → IsPullback a t s (spMap (algebraMap R K)) → ∀ L : LB Y, L.IsLB → ∃ M : LB X, M.IsLB ∧ LBIso (M.pull a) L := by
  intro R K _ _ _ _ _ _ X Y s t a hs hq hpb L hL
  haveI := isOpenImmersion_spMap_fractionRing R K
  have ha : IsOpenImmersion a := MorphismProperty.of_isPullback hpb.flip this
  haveI : IsRegularRing R := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have key : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      UniqueFactorizationMonoid (X.presheaf.stalk x) := fun x => by
    haveI : IsRegularRing (X.presheaf.stalk x) :=
      GlobalTheory.ExtendRig.isRegularRing_stalk GlobalTheory.isRegularRing_of_smooth R s x
    haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
      IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
    haveI : IsDomain (X.presheaf.stalk x) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
    exact ⟨inferInstance, GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _⟩
  exact GlobalTheory.exists_lineBundle_extension_of_isDomain X Y a ha (fun x => (key x).1)
    (fun x => (key x).2) L hL

end GlobalTheory.LBExtDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameOfSectionUnitsOnClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem isUnit_gs_id_iff {X : Scheme.{0}} (z : X) (U : X.Opens) (h : z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs (𝟙 X) z U a) ↔ z ∈ X.basicOpen a := by
  rw [gs_eq (𝟙 X) z U h, X.mem_basicOpen a z h]
  rfl

theorem exists_frame_of_isUnit_on_fibre : ∀ (X Y : Scheme.{0}) (β : X ⟶ Y), IsClosedMap β.base → ∀ (L : LB X), L.IsLB → ∀ (V : Y.Opens) (s : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V ⊓ L.U k)), IsSecOver L (β ⁻¹ᵁ V) s → ∀ y : Y, y ∈ V → (∀ (z : X) (k : L.ι), β z = y → z ∈ L.U k → IsUnit (gs (𝟙 X) z (β ⁻¹ᵁ V ⊓ L.U k) (s k))) → ∃ V' : Y.Opens, y ∈ V' ∧ V' ≤ V ∧ ∃ T : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V' ⊓ L.U k)ˣ, IsFrameOver L (β ⁻¹ᵁ V') T ∧ ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), SecCarriedOver L (β ⁻¹ᵁ V) s f w → FrameCarried L (β ⁻¹ᵁ V') T f w := by
  intro X Y β hβ L hL V s hs y hy hu
  let N : X.Opens := ⨆ k, X.basicOpen (s k)
  have hN : ∀ z : X, β z = y → z ∈ N := by
    intro z hz
    obtain ⟨k, hk⟩ := exists_chart hL z
    have hm : z ∈ β ⁻¹ᵁ V ⊓ L.U k := ⟨show β z ∈ V from hz ▸ hy, hk⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (isUnit_gs_id_iff z _ hm _).1 (hu z k hz hk)⟩
  let V₀ : Y.Opens := ⟨(β '' (N : Set X)ᶜ)ᶜ, (hβ _ N.2.isClosed_compl).isOpen_compl⟩
  have hy₀ : y ∈ V₀ := by
    rintro ⟨p, hp, e⟩
    exact hp (hN p e)
  have hV₀ : ∀ p : X, β p ∈ V₀ → p ∈ N := by
    intro p hp
    by_contra h
    exact hp ⟨p, h, rfl⟩
  have hle : ∀ k, β ⁻¹ᵁ (V ⊓ V₀) ⊓ L.U k ≤ β ⁻¹ᵁ V ⊓ L.U k := fun k z hz => ⟨hz.1.1, hz.2⟩
  have hunit : ∀ k, IsUnit ((X.presheaf.map (homOfLE (hle k)).op).hom (s k)) := by
    intro k
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV₀ z hz.1.2)
    have hm' : z ∈ β ⁻¹ᵁ V ⊓ L.U k' := X.basicOpen_le _ hk'
    have h1 : IsUnit (gs (𝟙 X) z _ (s k)) := by
      rw [hs z k k' hm'.1 hz.2 hm'.2]
      exact (Units.isUnit _).mul ((isUnit_gs_id_iff z _ hm' _).2 hk')
    rw [← gs_res (𝟙 X) z (hle k) hz, gs_eq (𝟙 X) z _ hz] at h1
    exact h1
  have key : ∀ (f : X ⟶ X) (z : X) (k : L.ι), f z ∈ β ⁻¹ᵁ (V ⊓ V₀) → f z ∈ L.U k →
      (gm f z _ (hunit k).unit : X.presheaf.stalk z) = gs f z _ (s k) := by
    intro f z k h1 h2
    have hm : f z ∈ β ⁻¹ᵁ (V ⊓ V₀) ⊓ L.U k := ⟨h1, h2⟩
    rw [← gs_unit f z _ hm, IsUnit.unit_spec, gs_res f z (hle k) hm]
  refine ⟨V ⊓ V₀, ⟨hy, hy₀⟩, inf_le_left, fun k => (hunit k).unit, ?_, ?_⟩
  · intro k k'
    refine unit_ext fun z hz => ?_
    rw [map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz]
    apply Units.ext
    rw [Units.val_mul, key (𝟙 X) z k hz.1.1 hz.1.2, key (𝟙 X) z k' hz.2.1 hz.2.2]
    exact hs z k k' hz.1.1.1 hz.1.2 hz.2.2
  · intro f w hw z j k hz hfz hk hj
    apply Units.ext
    rw [Units.val_mul, key f z j hfz hj, key (𝟙 X) z k hz hk]
    exact hw z j k hz.1 hfz.1 hk hj

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGlueMilnorPatchingArtinLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ArtinPatch

theorem elem_of_isPullback {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {i : C ⟶ D}
    (H : IsPullback f g h i) :
    (∀ x y, f.hom x = f.hom y → g.hom x = g.hom y → x = y) ∧
      ∀ b c, h.hom b = i.hom c → ∃ a, f.hom a = b ∧ g.hom a = c := by
  have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
  exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩

theorem isPushout_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀}
    {g₂ : R₂ ⟶ R₀} (H : IsPullback f₁ f₂ g₁ g₂) (hg₁ : Function.Surjective g₁.hom) :
    IsPushout f₁ f₂ g₁ g₂ := by
  obtain ⟨-, hex⟩ := elem_of_isPullback H
  have key : ∀ s : PushoutCocone f₁ f₂, RingHom.ker g₁.hom ≤ RingHom.ker s.inl.hom := by
    intro s r hr
    rw [RingHom.mem_ker] at hr ⊢
    obtain ⟨a, ha1, ha2⟩ := hex r 0 (by rw [hr, map_zero])
    have e := congrArg (fun φ => φ.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    rw [← ha1, e, ha2, map_zero]
  let d : ∀ s : PushoutCocone f₁ f₂, R₀ ⟶ s.pt := fun s =>
    CommRingCat.ofHom (RingHom.liftOfRightInverse g₁.hom (Function.surjInv hg₁)
      (Function.rightInverse_surjInv hg₁) ⟨s.inl.hom, key s⟩)
  have hd : ∀ (s : PushoutCocone f₁ f₂) (r : R₁), (d s).hom (g₁.hom r) = s.inl.hom r := fun s r => by
    simp only [d, CommRingCat.hom_ofHom]
    exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ r
  refine IsPushout.of_isColimit (c := PushoutCocone.mk g₁ g₂ H.w) ?_
  refine PushoutCocone.IsColimit.mk _ d ?_ ?_ ?_
  · intro s
    ext r
    exact hd s r
  · intro s
    ext r₂
    obtain ⟨r₁, hr₁⟩ := hg₁ (g₂.hom r₂)
    obtain ⟨a, ha1, ha2⟩ := hex r₁ r₂ hr₁
    have e := congrArg (fun φ => φ.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    change (d s).hom (g₂.hom r₂) = s.inr.hom r₂
    rw [← hr₁, hd, ← ha1, e, ha2]
  · intro s m h1 _
    ext y
    obtain ⟨r, rfl⟩ := hg₁ y
    have e := congrArg (fun φ => φ.hom r) h1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    change m.hom (g₁.hom r) = (d s).hom (g₁.hom r)
    rw [hd]
    exact e

theorem spec_eq_of_artinian (P : CommRingCat.{0}) [IsLocalRing P] [IsArtinianRing P] (x y : Spec P) :
    x = y := by
  have h : ∀ z : PrimeSpectrum P, z.asIdeal = IsLocalRing.maximalIdeal P := fun z =>
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime z.asIdeal)
  exact PrimeSpectrum.ext ((h x).trans (h y).symm)

end GlobalTheory.ArtinPatch

namespace GlobalTheory.ArtinPatch

theorem glues_spec {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀}
    (H : IsPullback f₁ f₂ g₁ g₂) (hP : ∀ x y : Spec P, x = y) :
    GlobalTheory.PinchLift.Glues (Spec.map f₂) (Spec.map f₁) (Spec.map g₂) (Spec.map g₁) := by
  obtain ⟨hinj, hex⟩ := elem_of_isPullback H
  have inj : ∀ {R : CommRingCat.{0}} (u v : Γ(Spec R, ⊤)),
      (Scheme.ΓSpecIso R).hom.hom u = (Scheme.ΓSpecIso R).hom.hom v → u = v := by
    intro R u v h
    simpa using congrArg (Scheme.ΓSpecIso R).inv.hom h
  have nat : ∀ {R S : CommRingCat.{0}} (f : R ⟶ S) (u : Γ(Spec R, ⊤)),
      (Scheme.ΓSpecIso S).hom.hom ((Spec.map f).appTop.hom u) = f.hom ((Scheme.ΓSpecIso R).hom.hom u) := by
    intro R S f u
    exact congrArg (fun φ => φ.hom u) (Scheme.ΓSpecIso_naturality f)
  refine GlobalTheory.PinchLift.glues_of_basis _ _ _ _ {⊤} ?_ ?_
  · intro W x hx
    refine ⟨⊤, rfl, trivial, fun y _ => ?_⟩
    rw [hP y x]
    exact hx
  · rintro W rfl a b hab
    set V := Spec.map g₂ ⁻¹ᵁ Spec.map f₂ ⁻¹ᵁ (⊤ : (Spec P).Opens) ⊓
      Spec.map g₁ ⁻¹ᵁ Spec.map f₁ ⁻¹ᵁ (⊤ : (Spec P).Opens) with hVdef
    have hV : V = ⊤ := top_le_iff.1 (fun x _ => ⟨trivial, trivial⟩)
    have hiso : IsIso (homOfLE (le_top : V ≤ ⊤)) := by
      rw [show homOfLE (le_top : V ≤ ⊤) = (eqToIso hV).hom from Subsingleton.elim _ _]
      infer_instance
    set ρ := (Spec R₀).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    have hρ : ∀ u v, ρ.hom u = ρ.hom v → u = v := by
      intro u v h
      simpa using congrArg (inv ρ).hom h
    have e : (Spec.map g₂).appTop.hom a = (Spec.map g₁).appTop.hom b := by
      apply hρ
      exact hab
    have key : g₁.hom ((Scheme.ΓSpecIso R₁).hom.hom b) = g₂.hom ((Scheme.ΓSpecIso R₂).hom.hom a) := by
      rw [← nat g₁ b, ← nat g₂ a, e]
    obtain ⟨x, hx1, hx2⟩ := hex _ _ key
    refine ⟨(Scheme.ΓSpecIso P).inv.hom x, ⟨?_, ?_⟩, ?_⟩
    · apply inj
      change (Scheme.ΓSpecIso R₂).hom.hom ((Spec.map f₂).appTop.hom _) = _
      rw [nat]
      simpa using hx2
    · apply inj
      change (Scheme.ΓSpecIso R₁).hom.hom ((Spec.map f₁).appTop.hom _) = _
      rw [nat]
      simpa using hx1
    · rintro s ⟨hs2, hs1⟩
      apply inj
      simp only [Iso.inv_hom_id_apply]
      apply hinj
      · rw [← nat]
        change (Scheme.ΓSpecIso R₁).hom.hom (((Spec.map f₁).app ⊤).hom s) = _
        rw [hs1, hx1]
      · rw [← nat]
        change (Scheme.ΓSpecIso R₂).hom.hom (((Spec.map f₂).app ⊤).hom s) = _
        rw [hs2, hx2]

end GlobalTheory.ArtinPatch

namespace GlobalTheory.ArtinPatch

theorem exists_lb_glue : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (X : Over (Spec P)) (X₁ : Over (Spec R₁)) (X₂ : Over (Spec R₂)) (X₀ : Over (Spec R₀)) (j₁ : X₁.left ⟶ X.left) (j₂ : X₂.left ⟶ X.left) (i₁ : X₀.left ⟶ X₁.left) (i₂ : X₀.left ⟶ X₂.left), Flat X.hom → IsPullback j₁ X₁.hom X.hom (Spec.map f₁) → IsPullback j₂ X₂.hom X.hom (Spec.map f₂) → IsPullback i₁ X₀.hom X₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ X₂.hom = X₀.hom ≫ Spec.map g₂ → ∀ (L₁ : LB X₁.left) (L₂ : LB X₂.left), L₁.IsLB → L₂.IsLB → LBIso (L₁.pull i₁) (L₂.pull i₂) → ∃ L : LB X.left, L.IsLB ∧ LBIso L₁ (L.pull j₁) ∧ LBIso L₂ (L.pull j₂) := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hg₁ hg₂ X X₁ X₂ X₀ j₁ j₂ i₁ i₂ hflat h₁ h₂ h₀ hc hc₂ L₁ L₂ hL₁ hL₂ hiso
  haveI := hloc
  haveI := hart
  obtain ⟨-, hex⟩ := elem_of_isPullback hpb
  have hf₁ : Function.Surjective f₁.hom := fun r => by
    obtain ⟨r₂, hr₂⟩ := hg₂ (g₁.hom r)
    obtain ⟨a, ha, -⟩ := hex r r₂ hr₂.symm
    exact ⟨a, ha⟩
  have hw : Spec.map g₂ ≫ Spec.map f₂ = Spec.map g₁ ≫ Spec.map f₁ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hpb.w]

  let O : Over (Spec P) := Over.mk (𝟙 (Spec P))
  let O₂ : Over (Spec P) := Over.mk (Spec.map f₂)
  let O₁ : Over (Spec P) := Over.mk (Spec.map f₁)
  let O₀ : Over (Spec P) := Over.mk (Spec.map g₁ ≫ Spec.map f₁)
  let q : O₂ ⟶ O := Over.homMk (Spec.map f₂) (Category.comp_id _)
  let r : O₁ ⟶ O := Over.homMk (Spec.map f₁) (Category.comp_id _)
  let r' : O₀ ⟶ O₂ := Over.homMk (Spec.map g₂) hw
  let q' : O₀ ⟶ O₁ := Over.homMk (Spec.map g₁) rfl
  have hcomm : r' ≫ q = q' ≫ r := by
    ext1
    simpa [q, r, q', r'] using hw
  have hsq : IsPullback r'.left q'.left q.left r.left :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_of_isPullback hpb hg₁).flip)
  haveI hcl : IsClosedImmersion r.left := IsClosedImmersion.spec_of_surjective f₁ hf₁
  have haff : IsAffineHom q.left := by
    change IsAffineHom (Spec.map f₂)
    infer_instance
  have hgl : GlobalTheory.PinchLift.Glues q.left r.left r'.left q'.left :=
    glues_spec hpb (spec_eq_of_artinian P)
  obtain ⟨hpb', haff', hcl', hgl'⟩ :=
    GlobalTheory.PinchLift.glues_whiskerLeft (Spec P) X O O₂ O₁ O₀ q r r' q' hflat hcomm hsq haff hcl hgl

  have hT : ∀ U : Over (Spec P), IsPullback (fst X U).left (snd X U).left X.hom U.hom :=
    fun U => IsPullback.of_hasPullback X.hom U.hom
  have h₀' : IsPullback (i₁ ≫ j₁) X₀.hom X.hom (Spec.map g₁ ≫ Spec.map f₁) := h₀.paste_horiz h₁
  let ψ₂ := IsPullback.isoIsPullback _ _ h₂ (hT O₂)
  let ψ₁ := IsPullback.isoIsPullback _ _ h₁ (hT O₁)
  let ψ₀ := IsPullback.isoIsPullback _ _ h₀' (hT O₀)
  have p₂f : ψ₂.hom ≫ (fst X O₂).left = j₂ := IsPullback.isoIsPullback_hom_fst _ _ h₂ (hT O₂)
  have p₂s : ψ₂.hom ≫ (snd X O₂).left = X₂.hom := IsPullback.isoIsPullback_hom_snd _ _ h₂ (hT O₂)
  have p₁f : ψ₁.hom ≫ (fst X O₁).left = j₁ := IsPullback.isoIsPullback_hom_fst _ _ h₁ (hT O₁)
  have p₁s : ψ₁.hom ≫ (snd X O₁).left = X₁.hom := IsPullback.isoIsPullback_hom_snd _ _ h₁ (hT O₁)
  have p₀f : ψ₀.hom ≫ (fst X O₀).left = i₁ ≫ j₁ := IsPullback.isoIsPullback_hom_fst _ _ h₀' (hT O₀)
  have p₀s : ψ₀.hom ≫ (snd X O₀).left = X₀.hom := IsPullback.isoIsPullback_hom_snd _ _ h₀' (hT O₀)
  let s : X.left ⟶ (X ⊗ O).left := (hT O).lift (𝟙 _) X.hom (by simp [O])
  have wf : ∀ {U V : Over (Spec P)} (k : U ⟶ V), (X ◁ k).left ≫ (fst X V).left = (fst X U).left := by
    intro U V k
    rw [← Over.comp_left, whiskerLeft_fst]
  have ws : ∀ {U V : Over (Spec P)} (k : U ⟶ V), (X ◁ k).left ≫ (snd X V).left = (snd X U).left ≫ k.left := by
    intro U V k
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have E₂ : j₂ ≫ s = ψ₂.hom ≫ (X ◁ q).left := by
    apply (hT O).hom_ext
    · rw [Category.assoc, Category.assoc, wf, (hT O).lift_fst, p₂f, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ws, (hT O).lift_snd, ← Category.assoc, p₂s]
      exact h₂.w
  have E₁ : j₁ ≫ s = ψ₁.hom ≫ (X ◁ r).left := by
    apply (hT O).hom_ext
    · rw [Category.assoc, Category.assoc, wf, (hT O).lift_fst, p₁f, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ws, (hT O).lift_snd, ← Category.assoc, p₁s]
      exact h₁.w
  have E₀₂ : ψ₀.hom ≫ (X ◁ r').left = i₂ ≫ ψ₂.hom := by
    apply (hT O₂).hom_ext
    · rw [Category.assoc, Category.assoc, wf, p₀f, p₂f, hc]
    · rw [Category.assoc, Category.assoc, ws, ← Category.assoc, p₀s, p₂s]
      exact hc₂.symm
  have E₀₁ : ψ₀.hom ≫ (X ◁ q').left = i₁ ≫ ψ₁.hom := by
    apply (hT O₁).hom_ext
    · rw [Category.assoc, Category.assoc, wf, p₀f, p₁f]
    · rw [Category.assoc, Category.assoc, ws, ← Category.assoc, p₀s, p₁s]
      exact h₀.w.symm

  have hab0 : GlobalTheory.CechPic.pull i₂ (GlobalTheory.CechPic.cls L₂ hL₂) = GlobalTheory.CechPic.pull i₁ (GlobalTheory.CechPic.cls L₁ hL₁) := by
    rw [← GlobalTheory.CechPic.cls_pull hL₂ i₂ (pull_isLB hL₂ i₂), ← GlobalTheory.CechPic.cls_pull hL₁ i₁ (pull_isLB hL₁ i₁)]
    exact ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hiso).symm
  have e2 : (X ◁ r').left ≫ ψ₂.inv = ψ₀.inv ≫ i₂ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, E₀₂, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e1 : (X ◁ q').left ≫ ψ₁.inv = ψ₀.inv ≫ i₁ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, E₀₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hab : GlobalTheory.CechPic.pull (X ◁ r').left (GlobalTheory.CechPic.pull ψ₂.inv (GlobalTheory.CechPic.cls L₂ hL₂)) =
      GlobalTheory.CechPic.pull (X ◁ q').left (GlobalTheory.CechPic.pull ψ₁.inv (GlobalTheory.CechPic.cls L₁ hL₁)) := by
    rw [← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, e2, e1, GlobalTheory.CechPic.pull_comp,
      GlobalTheory.CechPic.pull_comp, hab0]
  obtain ⟨e', he2, he1⟩ := GlobalTheory.PinchLift.exists_pic_patch _ _ _ _ _ _ _ _ hpb' haff' hcl' hgl' _ _ hab
  obtain ⟨L, hL, hLe⟩ := GlobalTheory.CechPic.cls_surj (GlobalTheory.CechPic.pull s e')
  refine ⟨L, hL, ?_, ?_⟩
  · have h : GlobalTheory.CechPic.cls (L.pull j₁) (pull_isLB hL j₁) = GlobalTheory.CechPic.cls L₁ hL₁ := by
      rw [GlobalTheory.CechPic.cls_pull hL j₁, hLe, ← GlobalTheory.CechPic.pull_comp, E₁, GlobalTheory.CechPic.pull_comp, he1,
        ← GlobalTheory.CechPic.pull_comp, Iso.hom_inv_id, GlobalTheory.CechPic.pull_id]
    exact LBIso.symm ((GlobalTheory.CechPic.cls_eq_iff _ _).1 h)
  · have h : GlobalTheory.CechPic.cls (L.pull j₂) (pull_isLB hL j₂) = GlobalTheory.CechPic.cls L₂ hL₂ := by
      rw [GlobalTheory.CechPic.cls_pull hL j₂, hLe, ← GlobalTheory.CechPic.pull_comp, E₂, GlobalTheory.CechPic.pull_comp, he2,
        ← GlobalTheory.CechPic.pull_comp, Iso.hom_inv_id, GlobalTheory.CechPic.pull_id]
    exact LBIso.symm ((GlobalTheory.CechPic.cls_eq_iff _ _).1 h)

end GlobalTheory.ArtinPatch
end

