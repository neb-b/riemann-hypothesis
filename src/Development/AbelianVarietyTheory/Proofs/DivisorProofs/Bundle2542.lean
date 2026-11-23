module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeometricValuesIsoOfIdentificationDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegOfGenericFiniteNormalExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GenExt

attribute [local instance] ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK

theorem grp : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E), ∃ (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ ∧ IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ ∧ κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ ∧ κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ := by
  intro R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂
  haveI : IsNoetherianRing R' := hR.1
  haveI : IsIntegrallyClosed R' := hR.2.2.1
  have sc : spMap ((algebraMap R' (FractionRing R')).comp ρ) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ :=
    spMap_comp ρ (algebraMap R' (FractionRing R'))
  have gpp := pull_grp p
  have g1 := (pull_grp q₁).congr sc rfl
  have g2 := (pull_grp q₂).congr sc rfl

  obtain ⟨κ, k₁, k₂⟩ : ∃ κ : E.P.A.left ⟶ D₃.P.A.left, κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ ∧
      κ ≫ D₃.P.A.hom = E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R')) :=
    ⟨gpp.1.lift _ _ (g1.1.w.trans (Category.assoc _ _ _).symm), gpp.1.lift_fst _ _ _, gpp.1.lift_snd _ _ _⟩
  have gκ : IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ :=
    IsGrpPullback.cancel gpp (g1.congr rfl k₁.symm) k₂

  let G₂ := (Over.pullback (specOf ρ)).obj D₂.P.A
  have gb : IsGrpPullback G₂ D₂.P.A (spMap ρ) (pullback.fst D₂.P.A.hom (specOf ρ)) := isGrpPullback_pullback _ _
  obtain ⟨κ₂, l₁, l₂⟩ : ∃ κ₂ : E.P.A.left ⟶ G₂.left, κ₂ ≫ pullback.fst D₂.P.A.hom (specOf ρ) = GlobalTheory.PsiEvenPull.proj q₂ ∧
      κ₂ ≫ G₂.hom = E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R')) :=
    ⟨gb.1.lift _ _ (g2.1.w.trans (Category.assoc _ _ _).symm), gb.1.lift_fst _ _ _, gb.1.lift_snd _ _ _⟩
  have gκ₂ : IsGrpPullback E.P.A G₂ (spMap (algebraMap R' (FractionRing R'))) κ₂ :=
    IsGrpPullback.cancel gb (g2.congr rfl l₁.symm) l₂
  have hj : GlobalTheory.IsGenericPointHom (S := Sp R') (jK R') := .fractionField R' (FractionRing R')
  have s₃ : IsSemiAbelian D₃.P.A := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ D₃.P.isAb
  have s₂ : IsSemiAbelian G₂ :=
    GlobalTheory.isSemiAbelian_of_isAbelianScheme _ (GlobalTheory.isAbelianScheme_pullback_obj _ _ D₂.P.isAb)
  obtain ⟨F, ⟨hF, hκ⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) hj s₃ s₂ gκ gκ₂
  refine ⟨F.hom.left ≫ pullback.fst D₂.P.A.hom (specOf ρ), κ, ?_, gκ, k₁, ?_⟩
  · exact ((isGrpPullback_of_iso F).comp gb).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, hκ, l₁]

theorem bundle : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ E.P.A.left) (z : Z) (j : D₂.P.L.ι) (i : D₃.P.L.ι) (k : E.P.L.ι) (l : D₁.P.L.ι), GlobalTheory.PsiEvenPull.proj q₂ (f z) ∈ D₂.P.L.U j → κ (f z) ∈ D₃.P.L.U i → f z ∈ E.P.L.U k → GlobalTheory.PsiEvenPull.proj q₁ (f z) ∈ D₁.P.L.U l → gw w (f ≫ κ) z j i * (gw p.w (f ≫ κ) z l i)⁻¹ = gw q₂.w f z j k * (gw q₁.w f z l k)⁻¹ := by
  intro R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  obtain ⟨w₀, hw₀⟩ := _root_.GlobalTheory.Mum.genBundle_extends R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  obtain ⟨w, hw, hr⟩ := GlobalTheory.T.exists_bundleIso_rescaled_preserving_rigidification R R' ρ D₂ D₃ Φ gp w₀ hw₀
  exact ⟨w, hw, hr, GlobalTheory.T.rigidified_identifications_generic_fibre_agree R R' ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂ w hw hr⟩

theorem cpt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∀ x : D₃.X, (D₃.c x).left ≫ Φ = spMap ρ ≫ (D₂.c (q₂.xe (q₁.xe.symm (p.xe x)))).left := by
  intro R R' _ _ _ _ ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂ x
  set y := q₁.xe.symm (p.xe x) with hy
  have hy' : q₁.xe y = p.xe x := q₁.xe.apply_symm_apply _
  have sc : spMap ((algebraMap R' (FractionRing R')).comp ρ) = jK R' ≫ spMap ρ :=
    spMap_comp ρ (algebraMap R' (FractionRing R'))
  have gpp := pull_grp p
  have b1 : (E.c y).left ≫ E.P.A.hom = 𝟙 _ := by simpa using Over.w (E.c y)
  have b3 : (D₃.c x).left ≫ D₃.P.A.hom = 𝟙 _ := by simpa using Over.w (D₃.c x)
  have cq : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₁ =
      spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₁.c (p.xe x)).left := by
    rw [← hy']; exact q₁.c_pr y
  have cp : (D₃.c x).left ≫ GlobalTheory.PsiEvenPull.proj p = spMap ρ ≫ (D₁.c (p.xe x)).left := p.c_pr x
  have hx : (E.c y).left ≫ κ = jK R' ≫ (D₃.c x).left := by
    apply gpp.1.hom_ext
    · show ((E.c y).left ≫ κ) ≫ GlobalTheory.PsiEvenPull.proj p = (jK R' ≫ (D₃.c x).left) ≫ GlobalTheory.PsiEvenPull.proj p
      rw [Category.assoc, h₁, cq, Category.assoc, cp, sc, Category.assoc]
    · rw [Category.assoc, gκ.1.w, ← Category.assoc, b1, Category.id_comp, Category.assoc, b3]
      exact (Category.comp_id _).symm
  have c2 : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₂ =
      spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₂.c (q₂.xe y)).left := q₂.c_pr y
  have hsep := (GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian D₂.P.A
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme D₂.P.A D₂.P.isAb)).2
  have b2 : (D₂.c (q₂.xe y)).left ≫ D₂.P.A.hom = 𝟙 _ := by simpa using Over.w (D₂.c (q₂.xe y))
  haveI := hsep
  refine ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R')) D₂.P.A.hom ?_ (jK R') ?_
  · rw [Category.assoc, gp.1.w, ← Category.assoc, b3, Category.assoc, b2]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · rw [← Category.assoc, ← hx, Category.assoc, h₂, c2, sc, Category.assoc]

end GlobalTheory.Mum.GenExt

namespace GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem isPullDeg_of_generic : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')), IsPullDeg ρ D₁ D₃ → IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E → IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E → Nonempty (IsPullDeg ρ D₂ D₃) := by
  intro R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂
  have hα : Function.Injective (algebraMap R' (FractionRing R')) := IsFractionRing.injective R' _
  obtain ⟨Φ, κ, gp, gκ, h₁, h₂⟩ := GenExt.grp R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂
  obtain ⟨w, hw, hr, hT⟩ := GenExt.bundle R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  have hc := GenExt.cpt R R' ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  obtain ⟨s, hs⟩ := GlobalTheory.PullDegComp.exists_generic_lift (show Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) from hα.comp hρ) q₂

  let lf : FractionRing (FractionRing R') →+* FractionRing R' :=
    IsFractionRing.lift (A := FractionRing R') (K := FractionRing (FractionRing R')) (g := RingHom.id (FractionRing R')) Function.injective_id
  let r' : (TK R').left ⟶ (TK (FractionRing R')).left := spMap lf
  have hrj : r' ≫ jK (FractionRing R') = 𝟙 _ := by
    show spMap lf ≫ spMap (algebraMap (FractionRing R') (FractionRing (FractionRing R'))) = 𝟙 _
    rw [← spMap_comp]
    have : lf.comp (algebraMap (FractionRing R') (FractionRing (FractionRing R'))) = RingHom.id _ :=
      RingHom.ext fun a => IsFractionRing.lift_algebraMap (A := FractionRing R') (K := FractionRing (FractionRing R')) (g := RingHom.id (FractionRing R')) Function.injective_id a
    rw [this]; exact Spec.map_id _
  have hr2 : r' ≫ jK (FractionRing R') ≫ spMap ((algebraMap R' (FractionRing R')).comp ρ) =
      GlobalTheory.ArcPull.genMap hρ ≫ jK R := by
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [hrj, Category.id_comp]
    exact (spMap_comp ρ (algebraMap R' (FractionRing R'))).trans ((Category.id_comp _).symm.trans (GlobalTheory.ArcPull.fracMap_sq hρ))
  refine ⟨(GlobalTheory.DvrDeg.exists_isPullDeg_of_val hρ D₂ D₃ q₂.psiW s hs gp w hw hr
    (p.xe.trans (q₁.xe.symm.trans q₂.xe)) hc (fun x z J J' hJ hJ' => ?_)).choose⟩
  set y := q₁.xe.symm (p.xe x) with hy
  have hy' : q₁.xe y = p.xe x := q₁.xe.apply_symm_apply _
  set e : (TK R').left ⟶ E.P.A.left := r' ≫ E.xK y with he
  have gpp := pull_grp p
  have b1 : (E.c y).left ≫ E.P.A.hom = 𝟙 _ := by simpa using Over.w (E.c y)
  have b3 : (D₃.c x).left ≫ D₃.P.A.hom = 𝟙 _ := by simpa using Over.w (D₃.c x)
  have cq : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₁ =
      spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₁.c (p.xe x)).left := by
    rw [← hy']; exact q₁.c_pr y
  have cp : (D₃.c x).left ≫ GlobalTheory.PsiEvenPull.proj p = spMap ρ ≫ (D₁.c (p.xe x)).left := p.c_pr x
  have a1 : (e ≫ κ) ≫ GlobalTheory.PsiEvenPull.proj p = D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p := by
    rw [Category.assoc, h₁]
    show (r' ≫ jK (FractionRing R') ≫ (E.c y).left) ≫ GlobalTheory.PsiEvenPull.proj q₁ =
      (jK R' ≫ (D₃.c x).left) ≫ GlobalTheory.PsiEvenPull.proj p
    rw [Category.assoc, Category.assoc, cq, Category.assoc, cp, ← Category.assoc (jK (FractionRing R')),
      ← Category.assoc r', hr2, ← Category.assoc (jK R'), ← GlobalTheory.ArcPull.fracMap_sq hρ, Category.id_comp]
  have a2 : (e ≫ κ) ≫ D₃.P.A.hom = D₃.xK x ≫ D₃.P.A.hom := by
    rw [Category.assoc, gκ.1.w]
    show (r' ≫ jK (FractionRing R') ≫ (E.c y).left) ≫ E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R')) =
      (jK R' ≫ (D₃.c x).left) ≫ D₃.P.A.hom
    simp only [Category.assoc, reassoc_of% b1, b3, Category.id_comp, Category.comp_id]
    rw [← Category.assoc, hrj, Category.id_comp]; rfl
  have hx : e ≫ κ = D₃.xK x := gpp.1.hom_ext a1 a2
  obtain ⟨JE, hJE⟩ := GlobalTheory.DegPull.exists_good' E.P.isLB z
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.DegPull.exists_good' D₁.P.isLB z
  have v₂ := GlobalTheory.ArcPull.psi_val q₂ (GlobalTheory.ArcPull.genMap hρ) r' hr2 hJ hJE y
  have v₁ := GlobalTheory.ArcPull.psi_val q₁ (GlobalTheory.ArcPull.genMap hρ) r' hr2 hJ₁ hJE y
  have v₃ := GlobalTheory.ArcPull.psi_val p (GlobalTheory.ArcPull.genMap hρ) (𝟙 _) (GlobalTheory.ArcPull.fracMap_sq hρ) hJ₁ hJ' x
  rw [hy'] at v₁
  rw [v₁, Category.id_comp] at v₃
  have ex₂ : e ≫ GlobalTheory.PsiEvenPull.proj q₂ = D₃.xK x ≫ Φ := by rw [← h₂, ← Category.assoc, hx]
  have ex₁ : e ≫ GlobalTheory.PsiEvenPull.proj q₁ = D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p := by rw [← h₁, ← Category.assoc, hx]
  have t := hT _ e z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) (JE e) (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p))
    (by rw [← Scheme.Hom.comp_apply, ex₂]; exact hJ _) (by rw [← Scheme.Hom.comp_apply, hx]; exact hJ' _) (hJE e)
    (by rw [← Scheme.Hom.comp_apply, ex₁]; exact hJ₁ _)
  simp only [hx] at t
  have o₂ : GlobalTheory.ArcPull.om q₂.w z J JE e = gw q₂.w e z (J (D₃.xK x ≫ Φ)) (JE e) := by
    unfold GlobalTheory.ArcPull.om; rw [ex₂]
  have o₁ : GlobalTheory.ArcPull.om q₁.w z J₁ JE e = gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e) := by
    unfold GlobalTheory.ArcPull.om; rw [ex₁]
  have oo : GlobalTheory.ArcPull.om w z J J' (D₃.xK x) = gw w (D₃.xK x) z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) := rfl
  have op : GlobalTheory.ArcPull.om p.w z J₁ J' (D₃.xK x) =
      gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x)) := rfl
  change val (D₂.psi (q₂.xe y)) _ z J = _
  rw [v₂, oo, o₂]
  rw [o₁, op] at v₃
  have v₄ : val (E.psi y) r' z JE = gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e) *
      ((gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x)))⁻¹ *
        val (D₃.psi x) (𝟙 _) z J') := by
    rw [← v₃, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
  rw [v₄]
  have t' : gw w (D₃.xK x) z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) =
      gw q₂.w e z (J (D₃.xK x ≫ Φ)) (JE e) * (gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e))⁻¹ *
      gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x)) := by
    rw [← t, inv_mul_cancel_right]
  rw [t']
  simp only [mul_inv_rev, inv_inv]
  ac_rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegOfPeriodicOfIsRegSub
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isReg_of_periodic_of_isReg_sub : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ), ⨆ i, W i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) (pre u.ex (W i))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i), h i (z + l) = h i z) → (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → ∀ i, IsReg u.ex (W i) (h i) := by
  intro A _ g L u hA K W h hW hd hp hr
  obtain ⟨hopen, -, hpre, hval, hinf, -, hsup, -, -, -, -, htop⟩ := _root_.GlobalTheory.CechPer.pre_val_rules A g L u
  have glue := _root_.GlobalTheory.CechPer.isReg_of_locally A g L u hA
  have alg := _root_.GlobalTheory.RegAlg.main A g L u
  obtain ⟨n, V, r, hV⟩ := _root_.GlobalTheory.RatioCover.main A g L u hA
  have tor := fun c : Fin n => _root_.GlobalTheory.CechPer.exists_section_of_isReg_sub A g L u hA K W h hW hr ⟨V c, hV.1 c⟩
  choose k hk using tor
  have hk' : ∀ c i, IsReg u.ex (V c ⊓ W i) (k c - h i) := hk
  have covW : ∀ z, ∃ i, z ∈ pre u.ex (W i) := fun z => (hsup K W z).1 (hW ▸ htop z)
  have covV : ∀ z, ∃ c, z ∈ pre u.ex (V c) := fun z => (hsup (Fin n) V z).1 (hV.2.1 ▸ htop z)
  have hreg : ∀ c, IsReg u.ex (V c) (k c) := by
    refine _root_.GlobalTheory.CechPer.isReg_of_isReg_sub A g L u hA n V r hV k (fun c z hz => ?_) (fun c l z hz => ?_) (fun c c' => ?_)
    · obtain ⟨i, hi⟩ := covW z
      have hz' : z ∈ pre u.ex (V c ⊓ W i) := by rw [hinf]; exact ⟨hz, hi⟩
      have h1 : DifferentiableAt ℂ (k c - h i) z :=
        ((alg _).2.2.2.2.1 _ (hk' c i) z hz').differentiableAt ((hopen _).mem_nhds hz')
      have h2 : DifferentiableAt ℂ (h i) z := (hd i z hi).differentiableAt ((hopen _).mem_nhds hi)
      have h3 := h1.add h2
      rw [sub_add_cancel] at h3
      exact h3.differentiableWithinAt
    · obtain ⟨i, hi⟩ := covW z
      have hz' : z ∈ pre u.ex (V c ⊓ W i) := by rw [hinf]; exact ⟨hz, hi⟩
      obtain ⟨b, hb⟩ := hk' c i
      have e1 := hb z hz'
      have e2 := hb _ ((hpre _ l z).2 hz')
      rw [hval, ← e1, Pi.sub_apply, Pi.sub_apply, hp i l z hi] at e2
      exact sub_left_injective e2
    · refine glue _ _ fun z hz => ?_
      obtain ⟨i, hi⟩ := covW z
      refine ⟨V c ⊓ V c' ⊓ W i, inf_le_left, by rw [hinf]; exact ⟨hz, hi⟩, ?_⟩
      have r1 := (alg _).2.2.2.1 (V c ⊓ V c' ⊓ W i) (inf_le_inf_right _ inf_le_left) _ (hk' c i)
      have r2 := (alg _).2.2.2.1 (V c ⊓ V c' ⊓ W i) (inf_le_inf_right _ inf_le_right) _ (hk' c' i)
      have r3 := ((alg _).2.1 _ _ r1 r2).2.1
      rwa [sub_sub_sub_cancel_right] at r3
  intro i
  refine glue _ _ fun z hz => ?_
  obtain ⟨c, hc⟩ := covV z
  refine ⟨V c ⊓ W i, inf_le_right, by rw [hinf]; exact ⟨hc, hz⟩, ?_⟩
  have r1 := (alg _).2.2.2.1 (V c ⊓ W i) inf_le_left _ (hreg c)
  have r3 := ((alg _).2.1 _ _ r1 (hk' c i)).2.1
  rwa [sub_sub_cancel] at r3

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedSiegelModuliOverIntegers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SepSiegel

theorem isSeparated_toZ : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)), IsSeparated (toZ F.X) := by
  intro g n F
  obtain ⟨N, i, hi, -, e⟩ := F.qproj
  have hs : IsSeparated F.s := by
    rw [← e]
    have : IsSeparated (PSpace.str (cycAway n) N) := by
      unfold PSpace.str
      infer_instance
    infer_instance
  have ht : toZ F.X = F.s ≫ toZ (Sp (cycAway n)) := by
    first
    | exact specULiftZIsTerminal.hom_ext _ _
    | exact specZIsTerminal.hom_ext _ _
  rw [ht]
  infer_instance

end GlobalTheory.SepSiegel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.OneTraitTheta

open GlobalTheory GlobalTheory.Ex GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport GlobalTheory.ValuesPullIso GlobalTheory.LabTrans
open GlobalTheory.PsiEvenPull (proj)

theorem exists_values_iso (hL : Laws) {R R' : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F]
    [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (hF : Compat φ F) {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') : ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧
      ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' →
        IsPullGtF φ hD F g g' → I.Rel c' c := by
  let z : Sp F := IsLocalRing.closedPoint F
  obtain ⟨th', h₁, h₂⟩ := GeneratorPull.exists_generator_pull hL R R' φ D.P D'.P _ hD.w (pull_grp hD) hD.w_gen ν.th ν.th_gen
  obtain ⟨c, hc⟩ := ν'.th_gen th'
  obtain ⟨c', hc'⟩ := h₁ ν'.th
  have key : ∀ x : TF (R := R') F ⟶ D'.P.A, sval (Z := Sp F) ν.th (x.left ≫ proj hD) z ν.J =
      (om hD.w z ν.J ν'.J x.left).val * sval (Z := Sp F) th' x.left z ν'.J := fun x =>
    h₂ (Sp F) x.left z ν.J ν'.J (good ν z) (good ν' z)
  have k₁ := fun x : TF (R := R') F ⟶ D'.P.A =>
    IndivisibleSection.sval_of_secIsMul (p := D'.P.A.hom) hc (show Sp F ⟶ _ from x.left) z (good ν' z)
  have k₂ := fun x : TF (R := R') F ⟶ D'.P.A =>
    IndivisibleSection.sval_of_secIsMul (p := D'.P.A.hom) hc' (show Sp F ⟶ _ from x.left) z (good ν' z)
  by_cases h : c = 0
  · subst h
    refine exists_iso_of_th hD hL.globalFns hF ν ν' z 1 fun x => ?_
    have e₁ := k₁ x
    rw [GenSecField.cst_zero', zero_mul] at e₁
    have e₂ := k₂ x
    rw [e₁, mul_zero] at e₂
    exact ((key x).trans ((congrArg _ e₁).trans (mul_zero _))).trans ((congrArg _ e₂).trans (mul_zero _)).symm
  · let u : (FractionRing R')ˣ := Units.mk0 (algebraMap R' _ c) fun e =>
      h (IsFractionRing.injective R' (FractionRing R') (e.trans (map_zero _).symm))
    refine exists_iso_of_th hD hL.globalFns hF ν ν' z (TauTwist.unitAt (Z := Sp F) (jFK (R := R') F) z u) fun x => ?_
    refine ((key x).trans (congrArg _ (k₁ x))).trans ((_root_.mul_assoc _ _ _).symm.trans (congrArg₂ (· * ·) ?_ rfl))
    rw [Units.val_mul, TauTwist.unitAt_val]
    refine (_root_.mul_comm _ _).trans (congrArg₂ (· * ·) ?_ rfl)
    exact (congrArg (fun q => cst (Z := Sp F) q z c) (Over.w x)).trans
      (cst_comp (Z := Sp F) (jFK (R := R') F) (algebraMap R' (FractionRing R')) z c)

theorem exists_scalar {K C I : Type} [Field K] [Field C] (f : K →+* C) {v t : I → K} (s : Cˣ)
    (h : ∀ i, f (v i) = s * f (t i)) : ∃ c : K, c ≠ 0 ∧ ∀ i, v i = c * t i := by
  by_cases h₀ : ∀ i, t i = 0
  · exact ⟨1, one_ne_zero, fun i => f.injective (by rw [h, h₀]; simp)⟩
  · obtain ⟨i, hi⟩ := not_forall.1 h₀
    have hi' : f (t i) ≠ 0 := (map_ne_zero f).2 hi
    have e : f (v i / t i) = s := by rw [map_div₀, h, mul_div_cancel_right₀ _ hi']
    exact ⟨v i / t i, fun h₁ => s.ne_zero (by rw [← e, h₁, map_zero]), fun l => f.injective (by rw [map_mul, e, h])⟩

theorem isThetaPt_descend (hL : Laws) (hL₂ : Laws2) {S S' : Scheme.{0}} [IsLocallyNoetherian S] [IsLocallyNoetherian S']
    {P : PolAV S} {P' : PolAV S'} {f : S' ⟶ S} {a : P'.A.left ⟶ P.A.left} (hp : IsGrpPullback P'.A P.A f a)
    (hw : LBIso P'.L (P.L.pull a)) {K C : Type} [Field K] [Field C] [IsAlgClosed C] (em : K →+* C) (s : Sp K ⟶ S)
    (s' : Sp C ⟶ S') (hs : spMap em ≫ s = s' ≫ f) {m : ℕ} (hm : Odd m) (hmK : (m : K) ≠ 0) {I : Type}
    (x : I → (Over.mk s ⟶ P.A)) (x' : I → (Over.mk s' ⟶ P'.A)) (hx : ∀ i, (x' i).left ≫ a = spMap em ≫ (x i).left)
    (hk : ∀ i, x' i ^ m ^ 2 = 1) {w : I → C} (hw' : IsThetaPt P' m x' fun i => fnOf (w i)) {v : I → K} (c : Cˣ)
    (hv : ∀ i, em (v i) = c * w i) : IsThetaPt P m x fun i => fnOf (v i) := by
  have hmC : (m : C) ≠ 0 := by rw [← map_natCast em]; exact (map_ne_zero em).2 hmK
  let U : Over.mk (s' ≫ f) ⟶ Over.mk s := Over.homMk (spMap em) hs
  obtain ⟨e, he⟩ : ∃ e : (Over.mk s' ⟶ P'.A) ≃* (Over.mk (s' ≫ f) ⟶ P.A), ∀ y, (e y).left = y.left ≫ a :=
    LiePull.exists_pushEquiv hp (Over.mk s') _ rfl
  have hU : ∀ i, U ≫ x i = e (x' i) := fun i => Over.OverMorphism.ext ((hx i).symm.trans (he _).symm)
  have hkU : ∀ i, (U ≫ x i) ^ m ^ 2 = 1 := fun i => by rw [hU, ← map_pow, hk, map_one]
  have hkx : ∀ i, x i ^ m ^ 2 = 1 := fun i => by
    letI := em.toAlgebra
    haveI : Flat (spMap em) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact (inferInstance : Module.Flat K C)
    haveI : Surjective (spMap em) := ⟨fun p => ⟨(⊥ : PrimeSpectrum C), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
    haveI : Epi (spMap em) := Flat.epi_of_flat_of_surjective (spMap em)
    have E : U ≫ (x i ^ m ^ 2) = U ≫ 1 := by rw [MonObj.comp_pow, hkU, MonObj.comp_one]
    exact Over.OverMorphism.ext ((cancel_epi (spMap em)).1 (congrArg (fun q => q.left) E))
  obtain ⟨t, ht⟩ := Specialise.exists_isThetaPt_local hL hL₂ P s hm (IsUnit.mk0 _ hmK) x hkx
  have T₁ := Specialise.isThetaPt_map hL₂ P em hs ht
  have T₂ := ((CoordSep.coord_exists_unique_separate hL C _ P (s' ≫ f) m hm hmC I (fun i => U ≫ x i) hkU).2.2.1
    fun i => em (t i)).1 T₁
  let τ : (Over.mk s').left ⟶ (Over.mk (s' ≫ f)).left := 𝟙 (Sp C)
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp C)))
  have T₃ : IsCoordPt P' m x' 1 fun i => fnOf (em (t i)) :=
    FullExtend.isCoordPt_move τ hp hw τ (𝟙 _) (Category.comp_id _) (Category.id_comp _) (fun th h s => by
      obtain ⟨c, hc⟩ := h s
      have e := VVRank.pullM_id P.A P.isLB 1 (SecM.ofSec P.A th)
      exact ⟨c, fun j => (hc j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩)
      (fun i => (Category.id_comp _).trans (hx i).symm) hk (z := 1)
      ((Category.id_comp _).trans (by rw [← he, map_one])) T₂
  obtain ⟨-, h₂, h₃, -⟩ := CoordSep.coord_exists_unique_separate hL C _ P' s' m hm hmC I x' hk
  obtain ⟨d, hd⟩ := (h₂ 1 _ w T₃).1 ((h₃ w).1 hw')
  obtain ⟨c', hc', hv'⟩ := exists_scalar em (v := v) (t := t) (c * d) fun i => by
    rw [hv, hd, Units.val_mul, _root_.mul_assoc]; rfl
  rw [show v = fun i => c' * t i from funext hv']
  exact Specialise.isThetaPt_mul P ht hc'

theorem isThetaPt_of_series : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → ∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) := by
  intro R _ _ _ hR D A lab n hn ho _ hT j v hv
  obtain ⟨W, _, _, _, φ, G, _, _, D', A', U', hD, a, _, em₀, hW, iφ, lφ, hG, ⟨ga, hga, gp, lb⟩, c₀, H₀⟩ := hT
  have hV := GlobalTheory.lawsAndExpansions
  have hL : Laws := hV.1.1
  have hL₂ : Laws2 := hV.1.2.1
  have hGF := hL.globalFns
  have := hR.2
  have := hR.1.1
  have := hW.1
  have := hW.2.2
  have hB := D.tau_bimult
  have b₀ : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hm : Odd (n ^ j) := ho.pow
  have hk : 1 ≤ (n ^ j) ^ 2 := pow_pos hm.pos 2
  generalize n ^ j = m at *
  obtain ⟨C, _, _, _, _, _, gam, hgam, hC⟩ := exists_complete_isAlgClosed_cExt W (Kb W)
  have : CharZero C := (RingHom.charZero_iff (algebraMap (FractionRing W) C).injective).1 inferInstance
  letI : Algebra (FractionRing R) C := ((algebraMap (FractionRing W) C).comp ga).toAlgebra
  have cC : Compat φ C := fun r => congrArg (algebraMap (FractionRing W) C) (hga r)
  have a₀K : algebraMap (FractionRing R) (Kb W) = (algebraMap (FractionRing W) (Kb W)).comp ga :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c₀ r).trans
      (congrArg (algebraMap (FractionRing W) (Kb W)) (hga r).symm))
  let jW : Kb W →ₐ[FractionRing W] C := ⟨gam, hgam⟩
  let jR : Kb W →ₐ[FractionRing R] C := ⟨gam, fun t => by rw [a₀K]; exact hgam (ga t)⟩
  have hCR : CExt R (maximalIdeal R) C :=
    ⟨fun r => (cC r).symm ▸ hC.1 _, fun r hr => (cC r).symm ▸ hC.2 _ (map_nonunit φ r hr)⟩
  obtain ⟨N, ν, -⟩ := ValuesExist.exists_integral_values hL R D.toPre D.psi_even hB C ⊤ fun _ => trivial
  obtain ⟨N', ν', -⟩ := ValuesExist.exists_integral_values hL W D'.toPre D'.psi_even D'.tau_bimult C ⊤ fun _ => trivial
  obtain ⟨J, hJX, hJ⟩ := exists_values_iso hL hD cC ν ν'
  obtain ⟨f, hf, hf'⟩ := GlobalTheory.TorsionIso.torsion_clause W _ b₀ D' A' G hG U' C (m ^ 2) hk
  have ex : ∀ i : QkPt D.toPre (Kb R) (m ^ 2), ∃ (p₁ : QkPt D.toPre C (m ^ 2)) (p' : QkPt D'.toPre C (m ^ 2))
      (x' : TFK (R := W) C ⟶ A'.A), QkExt (jR.comp em₀).toRingHom i p₁ ∧ p'.y = hD.xe.symm p₁.y ∧
      IsPullGtF φ hD C p₁.g p'.g ∧ x'.left ≫ a = spMap (jR.comp em₀).toRingHom ≫ (lab _ i).left ∧
      QkToAkU U'.toUnifPre C (m ^ 2) p' x' := fun i => by
    obtain ⟨q₁, hq₁⟩ := exists_ext hB em₀ i
    obtain ⟨r, hr⟩ := exists_ext hB jR q₁
    let q₀ := pullQk hD hGF c₀ hB D'.tau_bimult q₁
    obtain ⟨x₀, hx₀⟩ := exists_lift_pt gp.1 em₀.toRingHom (em₀.comp_algebraMap.trans a₀K) (lab _ i)
    have t₀ := H₀ _ hk i q₁ q₀ x₀ hq₁ rfl (isPullGtF_pullGt hD hGF c₀ _) hx₀
    obtain ⟨⟨q₀', hq₀'⟩, hx, hgal⟩ := GlobalTheory.UT.Cl.galois_holds W _ b₀ D' A' G hG U' _ C jW _ hk q₀
    obtain ⟨x₀', hx₀'⟩ := hx x₀
    refine ⟨r, q₀', x₀', qkExt_trans hq₁ hr, ?_,
      isPullGtF_ext hD cC jW.toRingHom jW.comp_algebraMap (isPullGtF_pullGt hD hGF c₀ _) hr hq₀', ?_,
      (hgal q₀' x₀ x₀' hq₀' hx₀').1 t₀⟩
    · rw [hq₀'.1, hr.1]; rfl
    · rw [hx₀', Category.assoc, hx₀, ← Category.assoc, ← Geo.Tor.spMap_comp]; rfl
  choose p₁ p' x' e₁ e₂ e₃ e₄ e₅ using ex
  have hGt := _root_.GlobalTheory.Ex.GtValues.points_correspond
  choose q hq using fun i => (((hGt R D.toPre D.psi_even hB C N ν).2.2.2.2 _).1 (p₁ i)).exists
  choose q' hq' using fun i => (((hGt W D'.toPre D'.psi_even D'.tau_bimult C N' ν').2.2.2.2 _).1 (p' i)).exists
  obtain ⟨s, hs⟩ := hv C hCR (jR.comp em₀) N ν p₁ q e₁ hq
  have Q := _root_.GlobalTheory.Ex.ThetaSeries.theta_const_eq_series hV hGt (_root_.GlobalTheory.Ex.brFam hL hL₂) W _ hW rfl D' A' G hG U' C hC N' ν' m hm _ p' q' x' e₅ hq'
  have : CharZero (Kb R) := (RingHom.charZero_iff (algebraMap (FractionRing R) (Kb R)).injective).1 inferInstance
  refine isThetaPt_descend hL hL₂ gp lb (jR.comp em₀).toRingHom (jFK (R := R) (Kb R)) (jFK (R := W) C) ?_ hm
    (Nat.cast_ne_zero.2 hm.pos.ne') (lab _) x' e₄ (fun i => ?_) Q (s * J.lam) fun i => ?_
  · exact (Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap (jR.comp em₀).comp_algebraMap).trans (Geo.Tor.spMap_comp _ _))
  · rw [(hf.1 _ _).1 (e₅ i)]; exact hf' _
  · have e := (RelabelCoords.series_iso J hm (p := q' i) (p' := q i) (ν.eX.injective (by
      rw [hJX, (hq i).1, (hq' i).1, e₂, AddEquiv.apply_symm_apply])) (hJ _ _ _ _ (hq i).2 (hq' i).2 (e₃ i))).1
    rw [e, Units.val_mul, _root_.mul_assoc, Units.mul_inv_cancel_left]
    exact hs i

end GlobalTheory.Mum.OneTraitTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiBalanceFormalSumMemSpanCubicalThetaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiBalanceFormalSum_mem_span_cubicalTheta : ∀ {r : ℕ} (W A A' : Matrix (Fin r) (Fin r) ℤ), A.transpose * (W + W.transpose) = (W + W.transpose) * A' → GlobalTheory.TensBal.sig W A A' ∈ Submodule.span ℤ (Set.range fun p : GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r => GlobalTheory.TensBal.theta p.1 p.2.1 p.2.2) := by
  first | exact @GlobalTheory.TensBal.SpanPf.main | exact GlobalTheory.TensBal.SpanPf.main | (intros; apply GlobalTheory.TensBal.SpanPf.main <;> assumption)
end

