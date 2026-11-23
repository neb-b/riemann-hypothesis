module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroUniformisedModelDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ModelNZ

theorem exists_sec_nz : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal W) D A G), ∃ σ : SecAt G U.LG.L (𝟙 (Sp W)), NZ G U.LG.L (𝟙 (Sp W)) σ := by
  intro R _ _ _ _ _ D A G _ _ hsemi U
  haveI : GeometricallyConnected G.hom := hsemi.geomConnected
  have hLaws := GlobalTheory.abelianSchemeLaws_all

  obtain ⟨th, hth, -⟩ := GlobalTheory.PsiRing.exists_basis_fibNZ hLaws.2.secTwist R D.toPre
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : D.toPre.SecB 1 0, ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good D.toPre.P.L z J →
      sval th r z J = sval f₀ (r ≫ (snd (𝟙_ _) D.toPre.P.A).left) z J := by
    refine GlobalTheory.PsiExpansion.exists_sec_of_retract D.toPre.P.isLB _ _
      (GlobalTheory.PsiExpansion.snd_lift_unit D.toPre.P.A) (fun i => ?_) th
    fin_cases i
    · exact congrArg CommaMorphism.left (lift_snd (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A))
    · refine congrArg CommaMorphism.left (show lift (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A) ≫
        padd D.toPre.P.A (snd _ _) (toUnit _ ≫ D.toPre.c 0) = padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c 0) from ?_)
      simp only [padd, ← Category.assoc, comp_lift, lift_snd, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A) ≫ toUnit _ ≫ D.toPre.c 0 = toUnit _ ≫ D.toPre.c 0 from ?_)
      rw [← Category.assoc, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.toPre.P.A) (𝟙 D.toPre.P.A) ≫ toUnit _ ≫ η[D.toPre.P.A] = toUnit _ ≫ η[D.toPre.P.A] from ?_)
      rw [← Category.assoc, comp_toUnit]
  obtain ⟨z₀, hz₀, hn₀⟩ := hth (IsLocalRing.closedPoint R)
  have hx : D.toPre.P.A.hom ((snd (𝟙_ (Over (Sp R))) D.toPre.P.A).left z₀) = IsLocalRing.closedPoint R :=
    (congrArg (fun q => q z₀) (Over.w (snd (𝟙_ (Over (Sp R))) D.toPre.P.A))).trans hz₀
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' D.toPre.P.isLB z₀
  have hu : IsUnit (sval th (𝟙 _) z₀ J) := (isUnit_sval_iff th (𝟙 _) z₀ hJ).2 hn₀
  rw [hf₀ _ _ z₀ J hJ, Category.id_comp] at hu
  have hxn := (isUnit_sval_iff f₀ _ z₀ hJ).1 hu

  obtain ⟨σ, fam, hfam0, hσ, hmem, -⟩ := GlobalTheory.ThetaUnit.exists_theta hLaws.1.globalFns hLaws.1.secBaseChange
    le_rfl U f₀ ⟨_, hx, hxn⟩
  obtain ⟨g, hg, hn⟩ : ∃ g, G.hom g = IsLocalRing.closedPoint R ∧ g ∈ nonzeroLocus σ :=
    GlobalTheory.ThetaUnit.exists_mem_nonzeroLocus le_rfl U.toUnifPre (hσ 0)
      (by rw [hfam0]; exact ⟨_, hx, hxn⟩) hmem
  refine ⟨GlobalTheory.TorRef.upSec G σ, GlobalTheory.Ex.OnModel.toBase G g, ?_, ?_⟩
  · have a : GlobalTheory.Ex.OnModel.toBase G ≫ (fst (Over.mk (𝟙 (Sp R))) G).left = G.hom := by
      rw [GlobalTheory.Ex.OnModel.toBase, ← Over.comp_left, lift_fst]; rfl
    rw [← Scheme.Hom.comp_apply, a]
    exact hg
  · refine GlobalTheory.Ex.OnModel.mem_nonzeroLocus_pullTo σ _ _ ?_
    rw [← Scheme.Hom.comp_apply, GlobalTheory.Ex.OnModel.toBase_snd]
    exact hn

end GlobalTheory.UMin.ModelNZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfGaloisFixed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GaloisFixedSectionExtension

theorem extend_section {V : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] (X : Scheme.{0})
    (p : X ⟶ Spec (CommRingCat.of V)) [IsFinite p] (g : Spec (CommRingCat.of (FractionRing V)) ⟶ X)
    (hg : g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) :
    ∃ s : Spec (CommRingCat.of V) ⟶ X, s ≫ p = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ s = g := by
  haveI : IsAffine X := isAffine_of_isAffineHom p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ X.isoSpec.hom)
  obtain ⟨π, hπ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  have hfin : π.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hπ]
    infer_instance
  have hcomp : π ≫ φ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hπ, Category.assoc, Iso.hom_inv_id_assoc, hg]
  have hc : ∀ v : V, φ.hom (π.hom v) = algebraMap V (FractionRing V) v := fun v =>
    congrArg (fun f => f.hom v) hcomp
  have hmem : ∀ a, φ.hom a ∈ (algebraMap V (FractionRing V)).range := by
    intro a
    obtain ⟨q, hq, hqa⟩ := hfin.to_isIntegral a
    have hint : IsIntegral V (φ.hom a) := by
      refine ⟨q, hq, ?_⟩
      have h1 := Polynomial.hom_eval₂ q π.hom φ.hom a
      rw [hqa, map_zero] at h1
      have h2 : φ.hom.comp π.hom = algebraMap V (FractionRing V) := RingHom.ext hc
      rw [h2] at h1
      exact h1.symm
    exact IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective V _
  let e := RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap V (FractionRing V)).rangeRestrict_surjective⟩
  let ψ : Γ(X, ⊤) →+* V := e.symm.toRingHom.comp (φ.hom.codRestrict _ hmem)
  have hψ : ∀ a, algebraMap V (FractionRing V) (ψ a) = φ.hom a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply (φ.hom.codRestrict _ hmem a))
  have hψφ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V (FractionRing V)) = φ := by
    ext a
    exact hψ a
  have hπψ : π ≫ CommRingCat.ofHom ψ = 𝟙 _ := by
    ext v
    exact hinj ((hψ _).trans (hc v))
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hπ, ← Spec.map_comp, hπψ, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hψφ, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem exists_section_of_galoisFixed : ∀ (V : Type) [inst : CommRing V] [inst_1 : IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : CategoryTheory.Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V)), AlgebraicGeometry.IsFinite (CategoryTheory.Over.hom N) → ∀ (nb : ReciprocityTheory.ChartRestriction.G.Out.TF (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ (σ : Gal(AlgebraicClosure (FractionRing V)/FractionRing V)), CategoryTheory.CategoryStruct.comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (AlgHom.toRingHom (↑σ : AlgebraicClosure (FractionRing V) →ₐ[FractionRing V] AlgebraicClosure (FractionRing V)))) (CategoryTheory.Over.Hom.left nb) = CategoryTheory.Over.Hom.left nb) → ∃ (s : CategoryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V)) ⟶ N), nb = CategoryTheory.CategoryStruct.comp (CategoryTheory.SemiCartesianMonoidalCategory.toUnit (ReciprocityTheory.ChartRestriction.G.Out.TF (AlgebraicClosure (FractionRing V)))) s := by
  intro V _ _ _ hV N hN nb hfix
  haveI := hV
  haveI := hN
  haveI : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨g, hg⟩ := GlobalTheory.TorsDescent.descend_point (K := FractionRing V) N.left nb.left hfix
  have hg' : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫ g =
      nb.left := hg
  have hw : nb.left ≫ N.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := Over.w nb
  have hgp : g ≫ N.hom = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (g ≫ N.hom)
    rw [← hχ]
    congr 1
    have h1 : χ ≫ CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) =
        CommRingCat.ofHom (algebraMap V (FractionRing V)) ≫
          CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp, hχ, ← hw, ← hg', Category.assoc]
    ext v
    exact (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective
      (congrArg (fun f => f.hom v) h1)
  obtain ⟨s, hs, hsg⟩ := extend_section N.left N.hom g hgp
  refine ⟨Over.homMk s hs, ?_⟩
  apply Over.OverMorphism.ext
  show nb.left = (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) ≫ s
  rw [Category.assoc, hsg, hg']

end GlobalTheory.GaloisFixedSectionExtension
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackTwoTorsionTranslation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TwoTorsTr

theorem tr_tr {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (a : 𝟙_ (Over (Sp R)) ⟶ G)
    (ha : a ^ 2 = 1) : ((toUnit G ≫ a) * 𝟙 G) ≫ ((toUnit G ≫ a) * 𝟙 G) = 𝟙 G := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (((toUnit G ≫ a) * 𝟙 G) ≫ toUnit G) (toUnit G),
    Category.comp_id, ← _root_.mul_assoc, ← MonObj.comp_mul, ← pow_two, ha, MonObj.comp_one, _root_.one_mul]

end GlobalTheory.TwoTorsTr

namespace GlobalTheory.TwoTorsTr

theorem secPull_invol {X : Scheme.{0}} (L L₂ : LB X) (hL : L.IsLB) (hL₂ : L₂.IsLB) (τ : X ⟶ X) (ττ : τ ≫ τ = 𝟙 X)
    (wL : LB.Iso L₂ (L.pull τ)) (hw : wL.IsGen) (σ : H0 L 1) : ∃ σ₂ : H0 L₂ 1,
    (∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (N : (Z ⟶ X) → L.ι) (N' : (Z ⟶ X) → L₂.ι),
      Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' →
      Geo.Tor.sval σ (r ≫ τ) z N = (Geo.Tor.gw wL r z (N (r ≫ τ)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧
    ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  have hc : ∀ κ : Fin 1, (fun _ : Fin 1 => 𝟙 X) κ ≫ τ = τ ≫ (fun _ : Fin 1 => 𝟙 X) κ := fun _ => by
    simp only [Category.id_comp, Category.comp_id]
  obtain ⟨σ₂, hσ₂, -⟩ := SecPull.existsUnique_secPull _ _ _ _ L L₂ τ hL hL₂ wL hw (Fin 1)
    (fun _ => 𝟙 X) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) τ hc σ
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (N : (Z ⟶ X) → L.ι) (N' : (Z ⟶ X) → L₂.ι),
      Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' →
      Geo.Tor.sval σ (r ≫ τ) z N = (Geo.Tor.gw wL r z (N (r ≫ τ)) (N' r)).val * Geo.Tor.sval σ₂ r z N' := by
    intro Z r z N N' hN hN'
    have := ExpTrans.sec_val wL (fun _ : Fin 1 => 𝟙 X) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) τ hc σ σ₂
      r z (hσ₂ Z r z) hN hN'
    rw [this, Fin.prod_univ_one, zpow_natCast, pow_one, ExpTrans.om, Category.comp_id]
  refine ⟨σ₂, key, fun h0 j => ?_⟩
  refine ThetaScalar.eq_zero_of_sval hL σ (fun y J hJ => ?_) j
  choose J' hJ' using fun ψ : X ⟶ X => exists_chart hL₂ (ψ y)
  have e := key X τ y J J' hJ hJ'
  rw [ττ, ThetaScalar.sval_eq_zero σ₂ h0 τ y hJ', MulZeroClass.mul_zero] at e
  exact e

end GlobalTheory.TwoTorsTr

namespace GlobalTheory

theorem twoTors_secPull : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L L₂ : LB G.left), L.IsLB → L₂.IsLB → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ wL : LB.Iso L₂ (L.pull ((toUnit G ≫ a) * 𝟙 G).left), wL.IsGen → ∀ σ : H0 L 1, ∃ σ₂ : H0 L₂ 1, (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → L.ι) (N' : (Z ⟶ G.left) → L₂.ι), Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  intro R _ G _ _ L L₂ hL hL₂ a ha wL hw σ
  exact TwoTorsTr.secPull_invol L L₂ hL hL₂ _
    (by rw [← Over.comp_left, TwoTorsTr.tr_tr G a ha, Over.id_left]) wL hw σ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiPosFubiniStudyPowerAddSmoothFn
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeightShift

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB Y}

theorem exists_semiPosReg_pow_addFn [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    (R : AnRead p σ D) {φ : Weight p σ B} (h : φ.IsSmooth R) (hp : φ.StrictPos R)
    {v : CxPts p σ → ℝ} (hv : ∀ y, CInfAt v y) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((φ.pow m).addFn v).SemiPosReg D := by
  have hA : IsAlgAtlas R.finAtlas := R.isAlgAtlas_finAtlas
  have hv' : R.SmoothOn univ v := (cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hv y
  have hw : R.finAtlas.Smooth fun y => v y / 2 :=
    (hA.smooth_iff R).2 fun c => (hv' c).div_const 2
  have hΩ := h.isPotential hA
  have hpos := (h.isPosPot_iff hA).2 hp
  have hpsh : IsPsh R.finAtlas φ.locPot := fun x j z hz w => by
    by_cases h0 : w = 0
    · rw [h0, ReciprocityTheory.AnForm.levi_zero]
    · exact (hpos x j z hz w h0).le
  obtain ⟨C, hC⟩ := pshShift R.finAtlas φ.locPot hΩ hpos _ hw
  refine ⟨⌈C⌉₊, fun m hm i c y hy ξ => ?_⟩
  have hmC : 0 ≤ (m : ℝ) - C := sub_nonneg.2 (Nat.ceil_le.1 hm)
  have hχ : ((φ.pow m).addFn v).IsSmooth R := (h.zpow m).addFn hv'
  obtain ⟨j, hj⟩ := R.finAtlas.cover y
  obtain ⟨c', hc'⟩ := hA j
  rw [hc'] at hj
  have hb : y ∈ ptsIn p σ ((lbPow B m).U fun _ => pick φ.isLB y) :=
    mem_pow_iff.2 (mem_pick φ.isLB y)
  obtain ⟨w, -, e⟩ := hχ.exists_levi_eq c c' hy.1 hj hy.2 hb ξ
  rw [hχ.leviV_re_eq c hy.1 hy.2, e]
  have hz : c'.finChart y ∈ c'.finChart.target ∩ c'.finChart.symm ⁻¹' φ.locPot.U y :=
    mem_over c'.e hj (φ.locPot.mem_U y)
  have h₁ := hC y j (c'.finChart y) (by rw [hc']; exact ⟨hz.1, trivial, hz.2⟩) w
  have h₂ := hpsh y j (c'.finChart y) (by rw [hc']; exact hz) w
  rw [hc'] at h₁ h₂
  have d₁ : ContDiffAt ℝ 2 (((φ.pow m).addFn v).φ (fun _ => pick φ.isLB y) ∘ c'.finChart.symm)
      (c'.finChart y) := hχ.contDiffAt_finChart c' hj hb
  have d₂ : ContDiffAt ℝ 2 (φ.locPot.φ y ∘ c'.finChart.symm) (c'.finChart y) :=
    (h.contDiffAt_finChart c' hj (mem_pick φ.isLB y)).div_const 2
  have e₁ := ReciprocityTheory.AnForm.levi_add_smul (w := w) (C - m) (d₁.div_const 2) d₂
  rw [FinChart.levi_half] at e₁
  have e₂ : (LocPot.ofFun (fun y => v y / 2) + φ.locPot.rsmul C).φ y ∘ c'.finChart.symm =
      fun z => (((φ.pow m).addFn v).φ (fun _ => pick φ.isLB y) ∘ c'.finChart.symm) z / 2 +
        (C - m) * (φ.locPot.φ y ∘ c'.finChart.symm) z := by
    funext z
    have := φ.zpow_φ (m : ℤ) (fun _ => pick φ.isLB y) (c'.finChart.symm z)
    change v (c'.finChart.symm z) / 2 + C * (φ.φ (pick φ.isLB y) (c'.finChart.symm z) / 2) =
      ((φ.zpow (m : ℤ)).φ (fun _ => pick φ.isLB y) (c'.finChart.symm z) + v (c'.finChart.symm z)) / 2 +
        (C - m) * (φ.φ (pick φ.isLB y) (c'.finChart.symm z) / 2)
    rw [this]
    push_cast
    ring
  rw [e₂, e₁] at h₁
  nlinarith [mul_nonneg hmC h₂]

theorem strictPos_fsO1 (N : ℕ) (R : AnRead (PSpace.str k N) σ N) :
    (ProjAn.fsO1 k σ N).StrictPos R := fun i c y hy ξ h0 => by
  have := ProjPos.fubiniStudy_weight_pullback_closed_immersion_strictPos (σ := σ) (𝟙 _) (Category.id_comp (PSpace.str k N)) R
    (fun _ => i) c y ⟨hy.1, mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hy.2)⟩ ξ h0
  have e (z) : ((ProjAn.fsO1 k σ N).pull (𝟙 _) (Category.id_comp (PSpace.str k N))).φ (fun _ => i) z =
      (ProjAn.fsO1 k σ N).φ i z := by
    refine (Weight.pull_φ _ _ _ _ _).trans ?_
    have e : PtsOver.map (𝟙 _) (Category.id_comp (PSpace.str k N)) _ z = z :=
      Subtype.ext (Category.comp_id _)
    erw [e]
  simpa only [e] using this

theorem exists_semiPosReg_fubiniStudy : ∀ (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) (v : CxPts (PSpace.str k N) σ → ℝ), (∀ y, CInfAt v y) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).pow m).addFn v).SemiPosReg N := fun k _ σ N v hv =>
  haveI : T2Space (CxPts (PSpace.str k N) σ) :=
    CxPts.t2Space_cxPts_of_isProjOver σ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  exists_semiPosReg_pow_addFn (AnRead.all _ σ N)
    ((Weight.isCInf_iff_isSmooth _).1 ((ProjSpace.hermitianTwistingSheaf k N).cInf σ)) (strictPos_fsO1 N _) hv

end GlobalTheory.WeightShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiabelianExtensionModelAboveThetaSetup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open Classical

theorem GlobalTheory.Poinc.Sep.Cmp.exists_zhAbove : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ)
    (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i),
    ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY := by
  intro g n F W Z i X₁
  obtain ⟨m, c, hc⟩ := RatModel.exists_isCl_of_isProjOver X₁.projM
  have hc0 : ∃ j, c j ≠ 0 := by
    obtain ⟨j, hj⟩ := hc.1 (genericPoint X₁.M.Z)
    exact ⟨j, hj.1⟩
  obtain ⟨Y, U₀, EE, hO, hdiv, hE, ⟨G⟩⟩ := GlobalTheory.zhSt_holds X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big (Fin (m + 1)) c hc0
    (GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl X₁.o₁ X₁.Ω₁ X₁.S X₁.M (Fin (m + 1)) c hc)
  obtain ⟨q, hq⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id X₁.o₁ X₁.Ω₁) hdiv
  have hYp : IsProper Y.s := ((GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hO.proj).1
  have hsep : IsSeparated X₁.M.s := X₁.M.sep
  have hqp : IsProper q := by
    haveI : IsProper (q ≫ X₁.M.s) := by rw [hq.inducedModelMorphism_comp_structureMap]; exact hYp
    exact IsProper.of_comp q X₁.M.s
  exact ⟨Y, q, U₀, EE, ⟨G⟩, hO, hE, hq, hqp⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSemipositiveWeightOfGenerated
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory

theorem weight_cInf_semiPos_of_generated : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (B : LB X), B.IsLB → (∃ (n : ℕ) (u : Fin n → B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → ∃ (φ : Weight p σ B), φ.IsCInf ∧ ∀ D : ℕ, φ.SemiPosReg D := by
  intro k _ X p σ B hB ⟨n, u, hu⟩
  exact ⟨Weight.fsBasis p σ hB u hu 1 (by simp), Weight.isCInf_fsBasis hB u hu 1 (by simp),
    fun D => Weight.semiPosReg_fsBasis hB u hu 1 (by simp)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSemiAbelianModelAfterExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SplitSemiAbModel

theorem exists_split_model : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (P : PolAV (Sp (FractionRing V))), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W) (f : V →+* W) (fK : FractionRing V →+* FractionRing W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ f.IsIntegral ∧ Function.Injective f ∧ (∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) ∧ ∃ (A : PolAV (Sp (FractionRing W))) (β : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap fK) β ∧ LBIso A.L (P.L.pull β) ∧ ∃ (G : Over (Sp W)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK W)).obj G ≅ A.A), IsSemiAbelian G ∧ IsMonHom gen.hom ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField W)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj G) := by
  intro V _ _ _ hV P
  obtain ⟨V₁, _, _, _, f₁, fK₁, hV₁, hinj₁, -, hfin₁, hK₁, A₁, β₁, hpb₁, -, G₁, _, _, gen₁, hG₁, hgen₁⟩ :=
    GlobalTheory.PolSemiAbModel.exists_model V hV P
  obtain ⟨hdvr, hcpl, hch⟩ := (GlobalTheory.LN.cDvr_iff V₁).1 hV₁
  obtain ⟨W, _, _, _, _, g, hcW, hgi, hginj, -, E, hE⟩ :=
    GlobalTheory.SplitExtDVR.exists_complete_dvr_split_ext V₁ hcpl G₁ hG₁
  have hj : Function.Injective ((algebraMap W (FractionRing W)).comp g) :=
    (IsFractionRing.injective W (FractionRing W)).comp hginj
  obtain ⟨fK₂, hK₂'⟩ : ∃ fK₂ : FractionRing V₁ →+* FractionRing W,
      ∀ a, fK₂ (algebraMap V₁ (FractionRing V₁) a) = algebraMap W (FractionRing W) (g a) :=
    ⟨IsFractionRing.lift (A := V₁) (K := FractionRing V₁) hj,
      fun a => IsFractionRing.lift_algebraMap (K := FractionRing V₁) hj a⟩
  have hK₂ : fK₂.comp (algebraMap V₁ (FractionRing V₁)) = (algebraMap W (FractionRing W)).comp g :=
    RingHom.ext hK₂'
  obtain ⟨A, β, hpb, -, hLB⟩ := GlobalTheory.KeyFam.SameLam.exists_polPB P (fK₂.comp fK₁)
  have hG : IsSemiAbelian ((Over.pullback (spMap g)).obj G₁) := IsSemiAbelian.pullback _ G₁ hG₁
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, g.comp f₁, fK₂.comp fK₁, hcW,
    RingHom.IsIntegral.trans _ _ hfin₁.to_isIntegral hgi, hginj.comp hinj₁, ?_, A, β, hpb, hLB, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hK₁]
    exact hK₂' _
  · let G := (Over.pullback (spMap g)).obj G₁
    let X := (Over.pullback (jK V₁)).obj G₁
    let T := (Over.pullback (spMap fK₂)).obj X
    have h₁ := (isGrpPullback_pullback G (jK W)).comp (isGrpPullback_pullback G₁ (spMap g))
    have hTX := isGrpPullback_pullback X (spMap fK₂)
    have hXG := isGrpPullback_pullback G₁ (jK V₁)
    have hsq : spMap fK₂ ≫ jK V₁ = jK W ≫ spMap g := by
      show spMap fK₂ ≫ spMap (algebraMap V₁ _) = spMap (algebraMap W _) ≫ spMap g
      rw [GlobalTheory.PolSemiAbModel.spMap_comp', GlobalTheory.PolSemiAbModel.spMap_comp', hK₂]
    have hTG := (hTX.comp hXG).congr hsq rfl
    obtain ⟨e₁, he₁, -⟩ := grpPullback_iso h₁ hTG
    have hXY := isGrpPullback_of_iso gen₁
    have hTP := (hTX.comp (hXY.comp hpb₁)).congr
      (by rw [Category.id_comp, GlobalTheory.PolSemiAbModel.spMap_comp']) rfl
    obtain ⟨e₂, he₂, -⟩ := grpPullback_iso hTP hpb
    exact ⟨G, inferInstance, hG.comm, e₁ ≪≫ e₂, hG, by simp only [Iso.trans_hom]; infer_instance, E, hE⟩

end GlobalTheory.SplitSemiAbModel
end

