module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2399
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackThickeningOfCarriesTorusCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FormalModel

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel GlobalTheory.ConstLin

section Thru

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {D : DegPre R}
  {D' : DegPre R'} {F : D'.P.A.left ⟶ D.P.A.left} {w : LB.Iso D'.P.L (D.P.L.pull F)} {ε : D'.X → D.X}

theorem thru_pull_iff {T T₀ : Over (Sp R)} {T' : Over (Sp R')} (k : T₀ ⟶ T) {g : GtPt D T} {g₀ : GtPt D T₀}
    (hk : GtPt.IsPull k.left g g₀) (h : T'.left ⟶ T₀.left) (ξ : GtPt D' T') :
    Thru w ε h g₀ ξ ↔ Thru w ε (h ≫ k.left) g ξ := by
  have hb : k ≫ g.b = g₀.b := Over.OverMorphism.ext hk.1.symm
  refine forall_congr' fun y => and_congr (forall_congr' fun j => ?_) (forall_congr' fun Z => forall_congr' fun r =>
    forall_congr' fun z => forall_congr' fun J => forall_congr' fun J' => forall_congr' fun hJ => ?_)
  · rw [Category.assoc, ConstTanRed.comp_gtφT D k g.b g₀.b hb]
  · rw [(val_corr hJ (hk.2 (ε y)) (r ≫ h)).trans (val_pull hJ _ _ _), Category.assoc]

theorem eq_of_thru {Y : Over (Sp R)} [GrpObj Y] {Φ : ∀ T, (T ⟶ Y) ≃ GtPt D T} (hΦ : Represents Φ)
    (hε : Function.Surjective ε) {T' : Over (Sp R')} {r r' : T'.left ⟶ Y.left} {ξ : GtPt D' T'}
    (h : Thru w ε r (Φ Y (𝟙 Y)) ξ) (h' : Thru w ε r' (Φ Y (𝟙 Y)) ξ) : r = r' := by
  refine hom_ext hΦ (((h 0).1 2).symm.trans ((h' 0).1 2)) fun χ z J hJ => ?_
  obtain ⟨χ, rfl⟩ := hε χ
  obtain ⟨J', hJ'⟩ := TorusCoord.exists_good' D'.P.isLB z
  have a := ((h χ).2 _ (𝟙 _) z J J' hJ hJ').trans ((h' χ).2 _ (𝟙 _) z J J' hJ hJ').symm
  rwa [Category.id_comp, Category.id_comp] at a

end Thru

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R}
  {I : Ideal R'} {E : DegData R' I} {hE : IsPullDeg ρ D E.toPre} {A' : PolAV (Sp (FractionRing R'))}
  {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] {Y : Over (Sp R)}

theorem Carries.thru {e : ℕ} {c : GtCoord I E.toPre e G'} {g : GtPt D Y} {φ} (h : Carries hE c g φ)
    {T : Over (Sp (R' ⧸ I ^ (e + 1)))} (x : T ⟶ thickObj R' I e G') :
    Thru hE.w hE.xe (T' := (Over.map (thick R' I e)).obj T) (x.left ≫ φ) g (TorusCoord.toGtPt c x) := by
  have hx := TorusCoord.isPointOf_toGtPt c x
  intro y
  refine ⟨fun k => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [TorusCoord.gtφT_eq, TorusCoord.gtφT_eq]
    refine TorusCoordPull.Oφ_pull hE g.b (TorusCoord.toGtPt c x).b (x.left ≫ φ) ?_ y k
    rw [hx.1, Category.assoc, h.1, Category.assoc]
  · have o := (TorusCoord.comp_eq_of_left (TorusCoord.toGtPt c x).b c.pG r (r ≫ x.left)
      (by rw [hx.1, Category.assoc])).1 y
    refine (congrArg (fun q => val (g.s (hE.xe y)) q z J) (Category.assoc _ _ _).symm).trans
      ((h.2 y Z (r ≫ x.left) z J J' hJ hJ').trans (congrArg₂ (· * ·)
        (Finset.prod_congr rfl fun k _ => congrArg (fun q => TorusCoordPull.om hE.w z J J' q ^ Oinvε k) (o k).symm) ?_))
    exact ((val_corr hJ' (hx.2 y) r).trans (val_pull hJ' _ _ _)).symm

theorem Carries.isGrpPullback' [GrpObj Y] {Φ : ∀ T, (T ⟶ Y) ≃ GtPt D T} (hΦ : Represents Φ) (U : UnifPre I E A' G')
    {e : ℕ} {φ} (h : Carries hE (U.gt e) (Φ Y (𝟙 Y)) φ) :
    IsGrpPullback (thickObj R' I e G') Y (thick R' I e ≫ spMap ρ) φ := by
  refine ⟨h.isPullback hΦ U, fun T x y x₀ y₀ hx hy => ?_⟩
  let Tw := (Over.map (thick R' I e)).obj T
  let T₀ : Over (Sp R) := Over.mk (T.hom ≫ thick R' I e ≫ spMap ρ)
  let i : Tw.left ⟶ T₀.left := 𝟙 T.left
  have hi : i ≫ T₀.hom = Tw.hom ≫ spMap ρ := (Category.id_comp _).trans (Category.assoc _ _ _).symm
  have pl : ∀ k : T₀ ⟶ Y, GtPt.IsPull k.left (Φ Y (𝟙 Y)) (Φ T₀ k) := fun k => by
    have := hΦ.1 _ _ k (𝟙 Y)
    rwa [Category.comp_id] at this
  have key : ∀ (x : T ⟶ thickObj R' I e G') (x₀ : T₀ ⟶ Y), x₀.left = x.left ≫ φ →
      Thru hE.w hE.xe i (Φ T₀ x₀) (TorusCoord.toGtPt (U.gt e) x) := fun x x₀ hx => by
    refine (thru_pull_iff x₀ (pl x₀) i _).2 ?_
    have e₁ : i ≫ x₀.left = x.left ≫ φ := (Category.id_comp _).trans hx
    rw [e₁]
    exact h.thru x
  obtain ⟨ξ, hξ⟩ := ConstPoint.exists_gtPt_through globalFns_holds (pull_grp hE) hE.w_gen hE.xe.toAddMonoidHom hE.c_pr
    (T := T₀) (T' := Tw) i hi (Φ T₀ (x₀ * y₀))
  have hξ' : Thru hE.w hE.xe i (Φ T₀ (x₀ * y₀)) ξ := hξ
  have ad := Thru.isAdd (pull_grp hE) globalFns_holds hE.w_gen hi (key x x₀ hx) (key y y₀ hy) hξ' (hΦ.2 T₀ x₀ y₀)
  obtain rfl : ξ = TorusCoord.toGtPt (U.gt e) (x * y) :=
    isAdd_unique ad (TorusCoord.isAdd_pointsEquiv (U.gt e) globalFns_holds x y)
  exact (Category.id_comp _).symm.trans
    (eq_of_thru hΦ hE.xe.surjective ((thru_pull_iff _ (pl _) i _).1 hξ') (h.thru (x * y)))

theorem isGrpPullback_of_carries : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → IsGrpPullback (thickObj R' I e G') Y.H (thick R' I e ≫ spMap ρ) φ :=
  fun _ _ _ _ _ U Y _ _ h => h.isGrpPullback' Y.rep U

end GlobalTheory.FormalModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGtPointInvolutionActionSubOfIdempotent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TorusExt

noncomputable section

namespace GlobalTheory.Mum.IdemDiff

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
variable {O : Type} [Ring O] [StarRing O] [Module O D.X]

theorem val_act (oa : D.OAct O) (a : O)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (g : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        charVal g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))

theorem gtPtAct_of_isAdd : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O), a * a = a → ∀ g₀ g h t : GtPtF D F, GtPtAct oa a g₀ g → GtPtAct oa a h h → GtPtF.IsAdd t h g → GtPtAct oa a t t := by
  intro R _ _ D F _ _ O _ _ _ oa a ha g₀ g h t hg hh hadd
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hs : star a * star a = star a := by rw [← star_mul, ha]
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have aa : oa.onB.act a = oa.onB.act a ≫ oa.onB.act a := by rw [← oa.onB.map_mul, ha]
  have ss : oa.onB.act (star a) = oa.onB.act (star a) ≫ oa.onB.act (star a) := by rw [← oa.onB.map_mul, hs]
  obtain ⟨b₁, v₁⟩ := (isAdd_iff_val _ _ _).1 hadd
  have gb : g.b = g.b ≫ oa.onB.act a := by rw [hg.1, Category.assoc, ← aa]
  have tb : t.b = t.b ≫ oa.onB.act a := by
    have e := gb
    rw [b₁, MonObj.mul_comp, ← hh.1] at e
    exact mul_right_cancel e
  refine ⟨tb, fun u hu u₀ χ => corr_of_val D.P.isLB fun y J hJ => (val_act oa a u t χ hJ).trans ?_⟩
  have vg : ∀ χ, charVal g χ y J = charVal g₀ (star a • χ) y J * val₂ u y J (cP D _ χ) g₀.b := fun χ =>
    (val_corr hJ (hg.2 u hu u₀ χ) _).symm.trans (val_act oa a u g₀ χ hJ)
  have vh : charVal h χ y J = charVal h (star a • χ) y J * val₂ u y J (cP D _ χ) h.b :=
    (val_corr hJ (hh.2 u hu u₀ χ) _).symm.trans (val_act oa a u h χ hJ)
  have vc := IsRos.val_comp hG D.P.isAb D.P.isLB ss aa ⟨hu, u₀⟩ ⟨hu, u₀⟩ ⟨hu, u₀⟩ hJ (cP D _ χ) g₀.b
  have vg' : charVal g χ y J = charVal g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b := by
    rw [vg χ, vg (star a • χ), ← mul_smul, hs, vc, cf, hg.1, _root_.mul_assoc]
  have ra := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := TF (R := R) F) hJ t.b h.b (cP D _ χ)).2
  rw [← tb, ← hh.1, ← b₁] at ra
  have e₂ := v₁ (star a • χ) y J hJ
  rw [cf] at e₂
  have a₁ := congrArg Additive.ofMul ra
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul (v₁ χ y J hJ)
  have a₄ := congrArg Additive.ofMul vg'
  have a₅ := congrArg Additive.ofMul vh
  show _ = charVal t χ y J
  apply Additive.ofMul.injective
  simp only [ofMul_mul, th] at a₁ a₂ a₃ a₄ a₅ ⊢
  linear_combination (norm := abel) a₃ - a₄ + a₅ - a₁ - a₂

end GlobalTheory.Mum.IdemDiff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImmersionOfForallAffineSurjectiveAppLE
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isImmersion_of_forall_affine_surjective_appLE : ∀ (Y Z : Scheme.{0}) (φ : Y ⟶ Z), (∀ y : Y, ∃ (U : Z.Opens) (W : Y.Opens) (h : W ≤ φ ⁻¹ᵁ U), IsAffineOpen U ∧ φ y ∈ U ∧ φ ⁻¹ᵁ U ≤ W ∧ IsAffineOpen W ∧ Function.Surjective (φ.appLE U W h).hom) → IsImmersion φ := by
  intro Y Z φ H
  have H' : ∀ y : Y, ∃ U : Z.Opens, φ y ∈ U ∧ IsClosedImmersion (φ ∣_ U) := by
    intro y
    obtain ⟨U, W, h, hU, hy, hW, hWa, hs⟩ := H y
    obtain rfl : W = φ ⁻¹ᵁ U := le_antisymm h hW
    refine ⟨U, hy, ?_⟩
    have : IsAffine U := hU
    have : IsAffine (φ ⁻¹ᵁ U) := hWa
    rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (Arrow.isoMk hWa.isoSpec hU.isoSpec (Scheme.Opens.toSpecΓ_naturality φ _) :
        Arrow.mk (φ ∣_ U) ≅ Arrow.mk (Spec.map (φ.app U)))]
    rw [Scheme.Hom.app_eq_appLE]
    exact IsClosedImmersion.spec_of_surjective _ hs
  choose U hyU hU using H'
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi g hg => by
      have : IsOpenImmersion i := hi
      have : IsImmersion g := hg
      infer_instance⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) U ?_ fun y => ?_
  · rintro _ ⟨y, rfl⟩
    exact (le_iSup U y : U y ≤ ⨆ i, U i) (hyU y)
  · have := hU y
    infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemOfValNonnegOverCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntOverCdvr

open IsLocalRing

theorem isIntegralElem_of_val_nonneg : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v → ∀ z : F, 0 ≤ v z → ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).IsIntegralElem z := by
  intro V _ _ _ hV ϖ hϖ F _ _ _ v hv z hz
  obtain ⟨hdvr, hcomp, hchar⟩ := hV
  let K := FractionRing V
  letI : Algebra V F := ((algebraMap K F).comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).mpr
    ((algebraMap K F).injective.comp (IsFractionRing.injective V K))
  haveI : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := F)).mpr inferInstance
  obtain ⟨W, hW, -, -, hfin, -, hloc, hs, -⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra V F {z}
  haveI := hfin

  have hVnn : ∀ r : V, 0 ≤ v (algebraMap V F r) := fun r =>
    GlobalTheory.FiniteDVRValuation.val_nonneg hϖ hv r

  let S : ValuationSubring F := GlobalTheory.FiniteDVRValuation.nonnegSubring v (RingHom.id F)
  have hWnn : ∀ w ∈ W, 0 ≤ v w := by
    intro w hw
    have hint : IsIntegral V w := (Algebra.IsIntegral.isIntegral (R := V) (⟨w, hw⟩ : W)).map W.val
    let φ : V →+* S := (algebraMap V F).codRestrict S (fun r => hVnn r)
    have hS : (algebraMap S F).IsIntegralElem w := RingHom.IsIntegralElem.of_comp (f := φ) hint
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := F)).1 hS
    rw [← hy]
    exact y.2

  have hϖpos : 0 < v (algebraMap V F ϖ) := by
    obtain ⟨n, hn, hu⟩ := GlobalTheory.FiniteDVRValuation.exists_nat_val hϖ hv hϖ.ne_zero
    have hn0 : n ≠ 0 := fun h => hϖ.not_isUnit (hu h)
    change 0 < v (algebraMap K F (algebraMap V K ϖ))
    rw [hn]
    exact_mod_cast Nat.pos_of_ne_zero hn0

  have hunit : ∀ c : W, v (c : F) = 0 → IsUnit c := by
    intro c hc
    by_contra hnu
    have hinj : Function.Injective (algebraMap V W) := by
      intro a b hab
      apply FaithfulSMul.algebraMap_injective V F
      have := congrArg Subtype.val hab
      simpa using this
    set ϖW : W := algebraMap V W ϖ
    have hϖW0 : ϖW ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    obtain ⟨N, hN⟩ : ∃ N : ℕ, IsDiscreteValuationRing.addVal W ϖW = N := by
      rcases h : IsDiscreteValuationRing.addVal W ϖW with _ | N
      · exact absurd (IsDiscreteValuationRing.addVal_eq_top_iff.1 h) hϖW0
      · exact ⟨N, rfl⟩
    have hc1 : 1 ≤ IsDiscreteValuationRing.addVal W c := by
      rw [ENat.one_le_iff_ne_zero]
      exact fun h => hnu (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
    have hdvd : ϖW ∣ c ^ N := by
      rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, AddValuation.map_pow, hN]
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • IsDiscreteValuationRing.addVal W c := nsmul_le_nsmul_right hc1 N
    obtain ⟨d, hd⟩ := hdvd
    have h1 : v ((c : F) ^ N) = 0 := by rw [AddValuation.map_pow, hc, nsmul_zero]
    have h2 : v ((c : F) ^ N) = v (algebraMap V F ϖ) + v (d : F) := by
      rw [← AddValuation.map_mul]
      congr 1
      have h := congrArg Subtype.val hd
      simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul] at h
      exact h
    have h3 : 0 < v ((c : F) ^ N) := by
      rw [h2]
      exact lt_of_lt_of_le hϖpos (le_add_of_nonneg_right (hWnn d d.2))
    rw [h1] at h3
    exact lt_irrefl _ h3

  obtain ⟨a, ha, b, hb, hb0, hab⟩ := hs z (Finset.mem_singleton_self z)
  have hzW : z ∈ W := by
    let a' : W := ⟨a, ha⟩
    let b' : W := ⟨b, hb⟩
    rcases le_total (IsDiscreteValuationRing.addVal W b') (IsDiscreteValuationRing.addVal W a') with h | h
    · obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 h
      have hc' : a = b * c := congrArg Subtype.val hc
      have : z = c := by
        apply mul_left_cancel₀ hb0
        rw [mul_comm, hab, hc']
      rw [this]; exact c.2
    · obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 h
      have hc' : b = a * c := congrArg Subtype.val hc
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hb0 (by simpa using hc')
      have hzc : z * c = 1 := by
        apply mul_left_cancel₀ ha0
        calc a * (z * c) = z * (a * c) := by ring
          _ = a * 1 := by rw [← hc', hab, _root_.mul_one]
      have hz0 : z ≠ 0 := left_ne_zero_of_mul_eq_one hzc
      have hvc : v (c : F) = 0 := by
        have hsum : v z + v (c : F) = 0 := by rw [← AddValuation.map_mul, hzc, AddValuation.map_one]
        have hc0 := hWnn c c.2
        refine le_antisymm ?_ hc0
        calc v (c : F) = 0 + v (c : F) := (zero_add _).symm
          _ ≤ v z + v (c : F) := by gcongr
          _ = 0 := hsum
      obtain ⟨u, hu⟩ := hunit c hvc
      have : z = ((u⁻¹ : Wˣ) : W) := by
        have h1 : ((u : W) : F) * (((u⁻¹ : Wˣ) : W) : F) = 1 := by
          rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
        rw [hu] at h1
        calc z = z * ((c : F) * (((u⁻¹ : Wˣ) : W) : F)) := by rw [h1, _root_.mul_one]
          _ = (z * c) * (((u⁻¹ : Wˣ) : W) : F) := by ring
          _ = _ := by rw [hzc, _root_.one_mul]
      rw [this]; exact Subtype.property _

  exact (Algebra.IsIntegral.isIntegral (R := V) (⟨z, hzW⟩ : W)).map W.val

end GlobalTheory.IntOverCdvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfSmoothGeomIrreducibleOverModificatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumInt

theorem isIntegral_of_smooth : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S),
    Smooth G.hom → GeometricallyIrreducible G.hom → Nonempty G.left → IsIntegral G.left := by
  intro R _ _ M G hsm hgi _
  haveI := M.integral
  haveI : IsReduced G.left := GlobalTheory.isReduced_of_smooth_of_isReduced G.hom
  haveI : IrreducibleSpace G.left := GeometricallyIrreducible.irreducibleSpace G.hom G.hom.isOpenMap
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.MumInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleFibreFst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MoverFibre

theorem isIrreducible_fibre_fst : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, IsIrreducible ((fst G G).left ⁻¹' {x}) := by
  intro R _ G _ hG x
  let j := G.left.fromSpecResidueField x
  let p₁ : pullback G.hom G.hom ⟶ G.left := pullback.fst G.hom G.hom
  have hp : (fst G G).left = p₁ := rfl
  have hirr0 := GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ G hG _ (j ≫ G.hom)
  haveI hirr : IrreducibleSpace (pullback G.hom (j ≫ G.hom) : Scheme.{0}) := hirr0
  let e : pullback G.hom (j ≫ G.hom) ≅ p₁.fiber x :=
    pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso G.hom G.hom j).symm ≪≫ pullbackSymmetry _ _
  have hr := (IrreducibleSpace.isIrreducible_univ (pullback G.hom (j ≫ G.hom) : Scheme.{0})).image _
      ((e.hom ≫ Scheme.Hom.fiberι p₁ x).continuous.continuousOn)
  rw [Set.image_univ] at hr
  have hrange : Set.range (e.hom ≫ Scheme.Hom.fiberι p₁ x) = Set.range (Scheme.Hom.fiberι p₁ x) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨e.hom z, by rw [Scheme.Hom.comp_apply]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨e.inv z, by rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e.inv e.hom, e.inv_hom_id]; rfl⟩
  show IsIrreducible (p₁ ⁻¹' {x})
  rw [← Scheme.Hom.range_fiberι p₁ x, ← hrange]
  exact hr

end GlobalTheory.MoverFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

variable {S : Scheme.{0}} (G : Over S) (L : LB G.left)

abbrev LocSec (N : S.Opens) : Type := ∀ i : L.ι, Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ N)

variable {G L}

def IsLocSec {N : S.Opens} (s : LocSec G L N) : Prop :=
  ∀ i j, resG _ (fun _ hx => ⟨hx.1.1, hx.2⟩ : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
    resG _ (fun _ hx => hx.1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U i ⊓ L.U j) (L.g i j : Γ(G.left, L.U i ⊓ L.U j)) *
      resG _ (fun _ hx => ⟨hx.1.2, hx.2⟩ : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U j ⊓ G.hom ⁻¹ᵁ N) (s j)

theorem lpow_U_le [GrpObj G] {K : Type} [Field K] {ξ : Sp K ⟶ S} {N : S.Opens} (hξ : Set.range ξ ⊆ N)
    (j : Fin 1 → L.ι) :
    (LPow G L 1 (Over.mk ξ)).U j ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ (L.U (j 0) ⊓ G.hom ⁻¹ᵁ N) := by
  intro y hy
  refine ⟨Set.mem_iInter.1 hy 0, ?_⟩
  have e : (snd (Over.mk ξ) G).left ≫ G.hom = (fst (Over.mk ξ) G).left ≫ ξ :=
    (Over.w (snd (Over.mk ξ) G)).trans (Over.w (fst (Over.mk ξ) G)).symm
  show G.hom ((snd (Over.mk ξ) G).left y) ∈ N
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact hξ ⟨_, rfl⟩

def genPull [GrpObj G] {K : Type} [Field K] {ξ : Sp K ⟶ S} {N : S.Opens} (hξ : Set.range ξ ⊆ N)
    (s : LocSec G L N) (j : Fin 1 → L.ι) : Γ((Over.mk ξ ⊗ G).left, (LPow G L 1 (Over.mk ξ)).U j) :=
  ((snd (Over.mk ξ) G).left.appLE _ _ (lpow_U_le hξ j)).hom (s (j 0))

def GenIs [GrpObj G] {K : Type} [Field K] (ξ : Sp K ⟶ S) {N : S.Opens} (s : LocSec G L N)
    (v : SecM G L 1 (Over.mk ξ)) : Prop :=
  ∃ hξ : Set.range ξ ⊆ N, genPull hξ s = v.1

def FibNz {N : S.Opens} (s : LocSec G L N) (W : S.Opens) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), Set.range x ⊆ W →
    ∃ (y : Sp K ⟶ G.left) (i : L.ι), y ≫ G.hom = x ∧ Set.range y ⊆ (L.U i ⊓ G.hom ⁻¹ᵁ N : G.left.Opens) ∧
      valF y _ (s i) ≠ 0

theorem isLocSec_zero {N : S.Opens} : IsLocSec (0 : LocSec G L N) := fun i j => by
  simp [Pi.zero_apply, map_zero, mul_zero]

end GlobalTheory.UMin.ThBdl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariantStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_coinvariant : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.KCoinv := by
  first | exact @GlobalTheory.KCoinvGood.kCoinv | exact GlobalTheory.KCoinvGood.kCoinv | (intros; apply GlobalTheory.KCoinvGood.kCoinv <;> assumption)
end

