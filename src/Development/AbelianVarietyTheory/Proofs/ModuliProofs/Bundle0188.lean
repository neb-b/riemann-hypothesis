module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsWeilIsRoot
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfGenericFibre
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0127

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaExtend

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.ThetaObjPull

theorem pic_local {R : Type} [CommRing R] [IsLocalRing R] (c : Pic (Sp R)) : c = 0 := by
  obtain ⟨U, hU, h⟩ := locZero_base (𝟙 (Sp R)) c (IsLocalRing.closedPoint R)
  have := pull_eq_zero_of_range h (𝟙 _) fun y =>
    (IsLocalRing.specializes_closedPoint y).mem_open U.isOpen hU
  rwa [pull_id, pull_id] at this

theorem locZero_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A)
    (h₁ : LocZero (fst T A).left (cls (Out.translDiff A L x) (LB.isLB_linComb hL _ _))) :
    LocZero (fst T A).left (lam (cls L hL) (fst T A ≫ x) (snd T A)) := by
  have h₂ := (h₁.sub (locZero_base (fst T A).left (pull x.left (cls L hL)))).sub
    (locZero_base (fst T A).left (-pull (1 : T ⟶ A).left (cls L hL)))
  convert h₂ using 1
  rw [cls_translDiff hL, lam]
  simp only [map_neg, ← pull_comp, ← Over.comp_left, MonObj.comp_one]
  abel

theorem kTriv_of_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {P : LB (A ⊗ A).left}
    (hP : P.IsLB) (e : cls P hP = lam (cls L hL) (fst A A) (snd A A))
    (h : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1) :
    Out.KTriv A L := by
  intro R _ t x hx
  have h₁ := (locZero_iff _ (LB.isLB_linComb hL _ _)).1 hx
  have h₂ := locZero_lam hL x h₁
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ A).left fun p => ?_)
  obtain ⟨V, hV, H⟩ := h₂ p
  refine ⟨V, hV, ?_⟩
  let T' : Over S := Out.overRes (T := Over.mk t) V
  let i : T' ⟶ Over.mk t := Out.overResι V
  have H' := pull_eq_zero_of_range H (lift (snd A T' ≫ i) (fst A T')).left fun y => by
    have e := congrArg (fun q => q.left y) (lift_fst (snd A T' ≫ i) (fst A T'))
    show (fst (Over.mk t) A).left ((lift (snd A T' ≫ i) (fst A T')).left y) ∈ V
    refine e ▸ ?_
    exact ((snd A T').left y).2
  have := h T' (i ≫ x) ((cls_eq_zero_iff (pull_isLB hP _)).1 (by
    rw [cls_pull hP, e, pull_lam, lift_fst, lift_snd]
    rwa [pull_lam, lift_fst_assoc, lift_snd, Category.assoc] at H'))
  exact congrArg (fun q => q.left) (this.trans (MonObj.comp_one i).symm)

section Dvr

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

variable {A : Over (Sp V)} [GrpObj A] {B : Over (Sp K)} [GrpObj B] {ψ : B.left ⟶ A.left}



end Dvr

section Pol

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
  {A : Over (Sp V)} [GrpObj A]

end Pol

end GlobalTheory.ThetaExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKTrivialOfPrincipalGenericFibreDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.KTrivSpread

theorem kTriv_of_finite_flat {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {A : Over (Sp V)} [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {Z : Over (Sp V)} (i : Z ⟶ A)
    [IsFinite Z.hom] [Flat Z.hom]
    (hZ : ∀ (T : Over (Sp V)) (x : T ⟶ A), MemKL A L x ↔ ∃ z : T ⟶ Z, z ≫ i = x)
    {A' : Over (Sp K)} [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap (algebraMap V K)) φ)
    {L' : LB A'.left} (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hk : KTriv A' L') : KTriv A L := by
  have := hA.proper
  have := schemeTheoreticallyDominant_fractionField V K
  let Y := pullback Z.hom (spMap (algebraMap V K))
  have : IsAffine Y := isAffine_of_isAffineHom (pullback.snd Z.hom (spMap (algebraMap V K)))
  have : IsSchemeTheoreticallyDominant (pullback.fst Z.hom (spMap (algebraMap V K))) :=
    .of_isPullback (IsPullback.of_hasPullback Z.hom (spMap (algebraMap V K))).flip
  let d : Sp Γ(Y, ⊤) ⟶ Z.left := Y.isoSpec.inv ≫ pullback.fst Z.hom (spMap (algebraMap V K))
  let t : Sp Γ(Y, ⊤) ⟶ Sp K := Y.isoSpec.inv ≫ pullback.snd Z.hom (spMap (algebraMap V K))
  have hd : d ≫ Z.hom = t ≫ spMap (algebraMap V K) := by
    simp only [d, t, Category.assoc, pullback.condition]
  have hdi : (d ≫ i.left) ≫ A.hom = t ≫ spMap (algebraMap V K) := by
    rw [Category.assoc, Over.w i, hd]
  let x : Over.mk t ⟶ A' := Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
  let z : Over.mk (t ≫ spMap (algebraMap V K)) ⟶ Z := Over.homMk d hd
  have hz : z ≫ i = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
  have hx : x = 1 := hk _ t x (memKL_of_push h hL hL' hw x ((hZ _ _).2 ⟨z, hz⟩))
  have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
  have hi : i = toUnit Z ≫ η[A] := by
    have : IsSchemeTheoreticallyDominant d := by
      dsimp only [d]; infer_instance
    refine over_ext_of_schemeTheoreticallyDominant d (congrArg (fun q => q.left)
      (show z ≫ i = z ≫ toUnit Z ≫ η[A] from ?_))
    rw [hz, hx', ← Category.assoc, comp_toUnit]
    rfl
  intro R _ s y hy
  obtain ⟨u, rfl⟩ := (hZ _ y).1 hy
  rw [hi, ← Category.assoc, comp_toUnit]

theorem kTriv_of_generic_fibre : Laws → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L → KTriv B M.L.L := by
  intro hL V K _ _ _ _ _ _ P B _ _ M φ hB h hw ha
  have hM := M.L.isLB
  have hP : AbLaw.IsProjBy B.hom :=
    (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B M.L.L hB hM ha V (𝟙 _) B.left (𝟙 _) B.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  obtain ⟨hO, hu, hK⟩ := UU.TrivTwist.inK_iff_trivial_twist _ B M.L.L hM
  obtain ⟨H, j, hj, hH⟩ := _root_.GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hL.globalFns V B hB hP M.L.L _ hM hO
  have hfin : IsFinite H.hom :=
    AmpleStabFinite.isFinite_of_relAmple hL.globalFns V B hB M.L.L _ hM hO ha H j hj hH
  have hflat : Flat H.hom := _root_.GlobalTheory.StabFlat.flat_of_isFinite hL.globalFns V B hB hP M.L M.c _ hO hu H j hj hH hfin
  exact kTriv_of_finite_flat hB hM j (fun T x => (hK _ rfl T x).trans (hH T x)) h P.isLB hw P.ktriv

end GlobalTheory.KTrivSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwistAmpleBundleTranslationBundleIsoTranslate
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.TwistIsTranslate

open CechPic

variable {K : Type} [Field K]

theorem pull_const {A T : Over (Sp K)} (x : 𝟙_ (Over (Sp K)) ⟶ A) (c : CechPic.Pic A.left) :
    CechPic.pull (toUnit T ≫ x).left c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hx : CechPic.pull x.left (cls L hL) = 0 := by
    have hc := hL.cover
    let z₀ : (𝟙_ (Over (Sp K))).left := (default : PrimeSpectrum K)
    have hz : x.left z₀ ∈ (⨆ i, L.U i) := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    refine GlobalTheory.RigidifyTwist.pull_cls_eq_zero hL x.left i fun z => ?_
    rwa [show z = z₀ from Subsingleton.elim (α := PrimeSpectrum K) _ _]
  rw [Over.comp_left, pull_comp, hx, map_zero]

theorem exists_comp_eq [IsAlgClosed K] {A B : Over (Sp K)} (s : A ⟶ B) [IsFinite s.left] [Surjective s.left]
    (y : 𝟙_ (Over (Sp K)) ⟶ B) : ∃ x : 𝟙_ (Over (Sp K)) ⟶ A, x ≫ s = y := by
  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section (k := K) (pullback.snd s.left y.left)
  have h1 := Over.w s
  have h2 := Over.w y
  refine ⟨Over.homMk (t ≫ pullback.fst s.left y.left) ?_, ?_⟩
  · simp only [Category.assoc, ← h1, pullback.condition_assoc, h2]
    simpa using ht
  · ext
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, pullback.condition]
    rw [← Category.assoc, ht]
    exact Category.id_comp _

theorem lam_id_const {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (x : 𝟙_ (Over (Sp K)) ⟶ A)
    (c : CechPic.Pic A.left) :
    lam c (𝟙 A) (toUnit A ≫ x) = CechPic.pull ((toUnit A ≫ x) * 𝟙 A).left c - c := by
  have h1 : (1 : A ⟶ A) = toUnit A ≫ (1 : 𝟙_ (Over (Sp K)) ⟶ A) := by simp
  have hc : (𝟙 A) * (toUnit A ≫ x) = (toUnit A ≫ x) * 𝟙 A := mul_comm _ _
  simp only [lam, hc, Over.id_left, pull_id, pull_const, h1]
  abel

theorem iso_of_formIs (P : Out.PolAV (Sp K)) (M : LB P.A.left) (hM : M.IsLB) (s : P.A ⟶ P.A) (hs : FormIs P M s)
    (x : 𝟙_ (Over (Sp K)) ⟶ P.A) :
    LBIso (LB.div M (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, ((toUnit P.A ≫ x ≫ s) * 𝟙 P.A).left] ![1, -1]))
      (M.pull ((toUnit P.A ≫ x) * 𝟙 P.A).left) := by
  obtain ⟨-, hiso⟩ := hs
  have hL : P.L.IsLB := P.isLB
  have hc1 : (cubeLB P.A ![fst P.A P.A, snd P.A P.A] M).IsLB := LB.isLB_linComb hM _ _
  have hc2 : (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ s] P.L).IsLB := LB.isLB_linComb hL _ _
  have hLam : abelian₂ P.A M = cubeLB P.A ![fst P.A P.A, snd P.A P.A] M := rfl
  rw [hLam] at hiso
  have e := (cls_eq_iff hc1 hc2).2 hiso
  rw [cls_cube_two hM _ _ hc1, cls_cube_two hL _ _ hc2] at e
  have e2 := congrArg (CechPic.pull (lift (𝟙 P.A) (toUnit P.A ≫ x)).left) e
  rw [pull_lam, pull_lam] at e2
  simp only [lift_fst, lift_snd_assoc, lift_snd] at e2
  rw [lam_id_const, Category.assoc, lam_id_const] at e2
  have hd := LB.isLB_div hM (LB.isLB_linComb hL (K := Fin 2)
    ![𝟙 P.A.left, ((toUnit P.A ≫ x ≫ s) * 𝟙 P.A).left] ![1, -1])
  refine (cls_eq_iff hd (pull_isLB hM _)).1 ?_
  rw [cls_div hM (LB.isLB_linComb hL _ _), cls_linComb hL, cls_pull hM]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, one_smul,
    neg_smul]
  rw [sub_eq_iff_eq_add] at e2
  rw [e2]
  abel

theorem twist_iso_translate : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (y : 𝟙_ (Over (Sp K)) ⟶ P.A), M.IsLB → Out.RelAmple P.A M → ∃ x : 𝟙_ (Over (Sp K)) ⟶ P.A, LBIso (LB.div M (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, ((toUnit P.A ≫ y) * 𝟙 P.A).left] ![1, -1])) (M.pull ((toUnit P.A ≫ x) * 𝟙 P.A).left) := by
  intro hA hB K _ _ P M y hM hAmp
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.BundleForm.exists_formIs hA hB K P M hM
  obtain ⟨hfin, hsurj⟩ := _root_.GlobalTheory.FormFinite.isFinite_and_surjective_of_formIs hA hB K P M s hM hAmp hs
  obtain ⟨x, hx⟩ := exists_comp_eq s y
  refine ⟨x, ?_⟩
  have h := iso_of_formIs P M hM s hs x
  rwa [hx] at h

end GlobalTheory.TwistIsTranslate
end
end

