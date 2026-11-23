module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0159
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalForm
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsUnitThetaKeyRuleSmoothBase
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsLeNatCastNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory.PolVanishing

variable {X : Scheme.{0}} {L : LB X}

theorem lbIso_pw_tw (hL : L.IsLB) (b N t : ℤ) :
    LBIso (AbLaw.pw L (b + N * t)) (tw (AbLaw.pw L b) (AbLaw.pw L N) t) := by
  refine lbIso_of_chartPull ⟨fun i => (i, i), fun i y hy => ⟨hy, hy⟩, fun y i j hi hj => ?_⟩
    (isLB_tw (isLB_pw hL b) (isLB_pw hL N) t)
  refine Eq.trans ?_ (gm_div (AbLaw.pw (AbLaw.pw L N) (-t)) (AbLaw.pw L b) (𝟙 X) y (i, i) (j, j)
    ⟨⟨hi, hi⟩, hj, hj⟩).symm
  change gm (𝟙 X) y (L.U i ⊓ L.U j) (L.g i j ^ (b + N * t)) =
    gm (𝟙 X) y (L.U i ⊓ L.U j) (L.g i j ^ b) * (gm (𝟙 X) y (L.U i ⊓ L.U j) ((L.g i j ^ N) ^ (-t)))⁻¹
  rw [← map_inv, ← map_mul, zpow_neg, inv_inv, ← zpow_mul, ← zpow_add]

theorem lbIso_pull_pw (μ' : X ⟶ X) (d l : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, μ'] ![d, -1])) (hα : α.IsGen) :
    LBIso ((AbLaw.pw L l).pull μ') (AbLaw.pw L (d * l)) := by
  let A := LB.LinComb L (K := Fin 2) ![𝟙 X, μ'] ![d, -1]
  have le : ∀ p : L.ι × (PUnit → L.ι), L.U p.1 ⊓ ((AbLaw.pw L l).pull μ').U p.2 ≤
      LB.wchart L (K := Fin 2) ![𝟙 X, μ'] ![p.1, p.2 PUnit.unit] := fun p y hy =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hy.1, mem_pull.1 hy.2]
  refine gen_chartPull (A' := LB.div (AbLaw.pw L (d * l)) ((AbLaw.pw L l).pull μ')) (h := 𝟙 X)
    (A := AbLaw.pw A l) ⟨fun p => ![p.1, p.2 PUnit.unit], le, fun y p q hp hq => ?_⟩
    ⟨fun j => α.s j ^ l⟩ fun i j => ?_
  · refine (gm_div ((AbLaw.pw L l).pull μ') (AbLaw.pw L (d * l)) (𝟙 X) y p q ⟨hp, hq⟩).trans ?_
    rw [gm_pull_g (AbLaw.pw L l) μ' (𝟙 X) y p.2 q.2 hp.2 hq.2]
    refine Eq.trans ?_ ((map_zpow _ _ l).trans (congrArg (· ^ l)
      (gm_linComb L (K := Fin 2) ![𝟙 X, μ'] ![d, -1] (𝟙 X) y _ _ (le p hp) (le q hq)))).symm
    rw [Fin.prod_univ_two]
    change gm (𝟙 X) y (L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1 ^ (d * l)) *
        (gm (𝟙 X ≫ μ') y (L.U (p.2 PUnit.unit) ⊓ L.U (q.2 PUnit.unit))
          (L.g (p.2 PUnit.unit) (q.2 PUnit.unit) ^ l))⁻¹ =
      (gm (𝟙 X) y (L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) ^ d *
        gm (𝟙 X ≫ μ') y (L.U (p.2 PUnit.unit) ⊓ L.U (q.2 PUnit.unit))
          (L.g (p.2 PUnit.unit) (q.2 PUnit.unit)) ^ (-1 : ℤ)) ^ l
    rw [map_zpow, map_zpow, mul_zpow, zpow_neg_one, inv_zpow, zpow_mul]
  · have h := congrArg (· ^ l) (hα i j)
    simp only [mul_zpow, ← map_zpow] at h
    exact h

variable {R : Type} [CommRing R] {f : X ⟶ Spec (CommRingCat.of R)}

theorem exactAt_of_lbIso {M M' : LB X} (hM : M.IsLB) (hM' : M'.IsLB) (h : LBIso M M')
    {κ : Type} [LinearOrder κ] {D : κ → X.Opens} {p : ℕ}
    (hp : (cubeComplex (secCube f M D)).ExactAt p) : (cubeComplex (secCube f M' D)).ExactAt p := by
  obtain ⟨w, hw⟩ := h
  exact hp.of_iso ((cubeFunctor κ R).mapIso (secCubeCongr f D hM hM' w hw))

theorem exactAt_of_affine_covers [IsSeparated f] {M : LB X} (hM : M.IsLB)
    {κ : Type} [LinearOrder κ] [Fintype κ] {D : κ → X.Opens}
    {κ' : Type} [LinearOrder κ'] [Fintype κ'] {D' : κ' → X.Opens}
    (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (hD' : ∀ i, IsAffineOpen (D' i)) (hc' : ⨆ i, D' i = ⊤) {p : ℕ}
    (hp : (cubeComplex (secCube f M D)).ExactAt p) : (cubeComplex (secCube f M D')).ExactAt p := by
  match p with
  | 0 => exact (secCube_exactAt_zero_and_one R X f M κ' D' hc').1
  | 1 => exact (secCube_exactAt_zero_and_one R X f M κ' D' hc').2
  | p + 2 =>
    rw [← cechComplex_exactAt_succ_iff_cube, HomologicalComplex.exactAt_iff_isZero_homology,
      ModuleCat.isZero_iff_subsingleton] at hp ⊢
    obtain ⟨e⟩ := cechLB_homology_equiv_of_affine_covers R X f M κ D κ' D' hM inferInstance
      hD hc hD' hc' (p + 1)
    exact @Equiv.subsingleton _ _ e.symm.toEquiv hp

theorem exists_forall_le_exactAt [IsNoetherianRing R] (hL : L.IsLB) {N : ℤ} (hN : 0 < N) {m : ℕ}
    {s : Fin (m + 1) → LB.Sec (AbLaw.pw L N)} (hs : VeryAmpleBy f (AbLaw.pw L N) s) :
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p,
      (cubeComplex (secCube f (AbLaw.pw L n) (fun i => Out.nonzeroLocus (s i)))).ExactAt p := by
  choose t₀ ht₀ using fun b : ℤ =>
    _root_.GlobalTheory.KeyKa.secCube_tw_exactAt_of_veryAmpleBy R X f (AbLaw.pw L N) m s (AbLaw.pw L b) (isLB_pw hL N) (isLB_pw hL b) hs
  obtain ⟨T, hT⟩ := ((Set.finite_Ico (0 : ℤ) N).image t₀).bddAbove
  refine ⟨T * N, fun n hn p => ?_⟩
  have h₁ : t₀ (n % N) ≤ n / N :=
    (hT ⟨n % N, ⟨Int.emod_nonneg n hN.ne', Int.emod_lt_of_pos n hN⟩, rfl⟩).trans
      (Int.le_ediv_of_mul_le hN hn)
  have h₂ := exactAt_of_lbIso (isLB_tw (isLB_pw hL _) (isLB_pw hL N) _) (isLB_pw hL _)
    (lbIso_pw_tw hL (n % N) N (n / N)).symm (ht₀ (n % N) (n / N) h₁ p)
  rwa [Int.emod_add_mul_ediv] at h₂

theorem exists_le_natCast_ne_zero (K : Type) [Field K] (B : ℕ) : ∃ m : ℕ, B ≤ m ∧ (m : K) ≠ 0 := by
  by_cases h : (B : K) = 0
  · exact ⟨B + 1, Nat.le_succ B, by simp [h]⟩
  · exact ⟨B, le_rfl, h⟩

theorem exactAt_secCube_pw : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (l : ℤ) (I : Type) [LinearOrder I] [Fintype I] (D : I → P.A.left.Opens), 1 ≤ l → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ p, (cubeComplex (secCube P.A.hom (pw P.L l) D)).ExactAt p := by
  intro hLaw K _ _ P l I _ _ D hl hD hc p
  have := P.isAb.proper
  obtain ⟨N, hN, r, s, -, hs⟩ := veryAmpleBy_of_relAmple P.isLB P.ample (𝟙 P.A.left)
    (Category.id_comp _) P.isLB (lbIso_pull_id P.isLB).symm
  obtain ⟨n₀, hn₀⟩ := exists_forall_le_exactAt P.isLB (by exact_mod_cast hN) hs
  obtain ⟨m, hm, hmK⟩ := exists_le_natCast_ne_zero K n₀.toNat
  have hm₁ : 1 ≤ m := Nat.pos_of_ne_zero fun h => hmK (by simp [h])
  have hle : n₀ ≤ (m : ℤ) ^ 2 * l := by
    have h₁ : n₀ ≤ m := by omega
    have h₂ : (1 : ℤ) ≤ m := by exact_mod_cast hm₁
    nlinarith [mul_nonneg (sq_nonneg (m : ℤ)) (sub_nonneg.2 hl)]
  obtain ⟨α, hα⟩ := hLaw.mulPull _ P m
  have := (hLaw.mulN _ P m hm₁).1
  refine _root_.GlobalTheory.exactAt_secCube_of_mul_pull hLaw K P m _ I D p hmK (isLB_pw P.isLB l) ?_
  refine exactAt_of_lbIso (isLB_pw P.isLB _) (LB.isLB_pull (isLB_pw P.isLB l) _)
    (lbIso_pull_pw _ _ l α hα).symm ?_
  refine exactAt_of_affine_covers (isLB_pw P.isLB _) (fun i => (hs.2 i).1) hs.1
    (fun i => (hD i).preimage _) ?_ (hn₀ _ hle p)
  rw [← Scheme.Hom.preimage_iSup, hc]
  rfl

end GlobalTheory.PolVanishing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsProjectiveAbelianModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open scoped CategoryTheory.Obj

namespace GlobalTheory.KeyTf

theorem exists_isGrpPullback_of_le {S : Type} [CommRing S] {R₀ R₁ : Subring S} (h : R₀ ≤ R₁) (A : Over (Sp S))
    [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A.left ⟶ A₀.left)
    (H : IsGrpPullback A A₀ (spMap R₀.subtype) φ) :
    ∃ φ₁ : A.left ⟶ ((Over.pullback (spMap (Subring.inclusion h))).obj A₀).left,
      IsGrpPullback A ((Over.pullback (spMap (Subring.inclusion h))).obj A₀) (spMap R₁.subtype) φ₁ := by
  have e : spMap R₀.subtype = spMap R₁.subtype ≫ spMap (Subring.inclusion h) :=
    spMap_comp (Subring.inclusion h) R₁.subtype
  have hp := isGrpPullback_pullback A₀ (spMap (Subring.inclusion h))
  refine ⟨hp.1.lift φ (A.hom ≫ spMap R₁.subtype) (by rw [H.1.w, e, Category.assoc]), ?_⟩
  exact IsGrpPullback.cancel hp (H.congr e (hp.1.lift_fst _ _ _).symm) (hp.1.lift_snd _ _ _)

theorem exists_projective_abelian_model : ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] (P : Out.PolAV (Sp S)), ∃ (R : Subring S) (A₀ : Over (Sp R)) (_ : GrpObj A₀) (φ : P.A.left ⟶ A₀.left), Algebra.FiniteType ℤ R ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension P.g A₀.hom ∧ IsProjOver A₀.hom ∧ IsGrpPullback P.A A₀ (spMap R.subtype) φ := by
  intro S _ _ _ P
  have hc := P.isAb.comm
  have hs := P.isAb.smooth
  have hpr := P.isAb.proper
  have hg := P.isAb.geomConnected
  obtain ⟨R₀, A₀, _, _, φ₀, -, hft₀, hs₀, hsep₀, hqc₀, H₀⟩ :=
    GlobalTheory.smooth_grpScheme_descends_to_fg_subring S P.A ∅ hs inferInstance inferInstance
  obtain ⟨F, hF⟩ := _root_.GlobalTheory.isProjOver_descends_to_subring S R₀ _ _ P.A.hom A₀.hom φ₀ H₀.1 (GlobalTheory.ProjSpace.isProjOver_polAV P)
  obtain ⟨R₁, h₀₁, hF₁, hft₁⟩ := exists_finiteType_subring_adjoin S R₀ F hft₀
  obtain ⟨A₁, _, _, φ₁, hp₁, hs₁, H₁⟩ : ∃ (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (_ : IsCommMonObj A₁)
      (φ₁ : P.A.left ⟶ A₁.left), IsProjOver A₁.hom ∧ Smooth A₁.hom ∧ IsGrpPullback P.A A₁ (spMap R₁.subtype) φ₁ := by
    obtain ⟨φ₁, H₁⟩ := exists_isGrpPullback_of_le h₀₁ P.A A₀ φ₀ H₀
    exact ⟨_, _, inferInstance, φ₁, hF R₁ h₀₁ hF₁ _ _ _ (IsPullback.of_hasPullback _ _),
      inferInstanceAs (Smooth (pullback.snd _ _)), H₁⟩
  let κ := IsLocalRing.residue S
  have e₁ : spMap (κ.comp R₁.subtype) = spMap κ ≫ spMap R₁.subtype := spMap_comp _ _
  have hfib : GeometricallyConnected (pullback.snd A₁.hom (spMap (κ.comp R₁.subtype))) := by
    have Q := IsPullback.of_hasPullback A₁.hom (spMap (κ.comp R₁.subtype))
    let l := H₁.1.lift (pullback.fst A₁.hom (spMap (κ.comp R₁.subtype))) (pullback.snd _ _ ≫ spMap κ)
      (by rw [Q.w, e₁, Category.assoc])
    have Q' : IsPullback l (pullback.snd A₁.hom (spMap (κ.comp R₁.subtype))) P.A.hom (spMap κ) :=
      IsPullback.of_right (by rw [H₁.1.lift_fst, ← e₁]; exact Q) (H₁.1.lift_snd _ _ _) H₁.1
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) Q' hg
  obtain ⟨f, hf, hconn⟩ := _root_.GlobalTheory.ConnOpen.geometricallyConnected_near R₁ _ A₁.hom _ (κ.comp R₁.subtype) hp₁ hs₁ hfib
  obtain ⟨u, hu⟩ : IsUnit (f : S) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hf
  obtain ⟨R₂, h₁₂, hF₂, hft₂⟩ := exists_finiteType_subring_adjoin S R₁ {((u⁻¹ : Sˣ) : S)} hft₁
  obtain ⟨φ₂, H₂⟩ := exists_isGrpPullback_of_le h₁₂ P.A A₁ φ₁ H₁
  have hunit : IsUnit (Subring.inclusion h₁₂ f) :=
    IsUnit.of_mul_eq_one (⟨((u⁻¹ : Sˣ) : S), hF₂ (by simp)⟩ : R₂) (Subtype.ext (by
      show (f : S) * _ = 1
      rw [← hu]; exact u.mul_inv))
  have hp₂ : IsProjOver ((Over.pullback (spMap (Subring.inclusion h₁₂))).obj A₁).hom :=
    GlobalTheory.ProjSpace.isProjOver_pullback_snd _ hp₁
  have hab : IsAbelianScheme ((Over.pullback (spMap (Subring.inclusion h₁₂))).obj A₁) :=
    ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd _ _)), projProper _ _ _ hp₂, hconn R₂ _ hunit⟩
  refine ⟨R₂, _, inferInstance, φ₂, hft₂, hab, ?_, hp₂, H₂⟩
  have e₂ : spMap (κ.comp R₂.subtype) = spMap κ ≫ spMap R₂.subtype := spMap_comp _ _
  refine GlobalTheory.CM.smoothOfRelativeDimension_of_fibre R₂ _ (κ.comp R₂.subtype) _ _
    (pullback.fst P.A.hom (spMap κ) ≫ φ₂) (pullback.snd P.A.hom (spMap κ)) P.g hab ?_ ?_
  · rw [e₂]; exact (IsPullback.of_hasPullback _ _).paste_horiz H₂.1
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback (IsPullback.of_hasPullback _ _)
      P.smoothDim

end GlobalTheory.KeyTf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDomainTensorOfIsAlgClosed
section
namespace GlobalTheory.ThetaEquiv

section Algebra
open Polynomial TensorProduct AlgebraicGeometry CategoryTheory Limits

theorem isDomain_tensor_of_isAlgClosed (K A : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (F : Type) [Field F] [Algebra K F] : IsDomain (F ⊗[K] A) := by
  let f : Spec (.of A) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K A))
  have hf : LocallyOfFiniteType f := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hi : IsIntegral (Over.mk f).left := inferInstanceAs (IsIntegral (Spec (.of A)))
  have hg : GeometricallyIntegral f :=
    GlobalTheory.geometricallyIntegral_of_isIntegral_of_isAlgClosed K (Over.mk f) hf
  let y := Spec.map (CommRingCat.ofHom (algebraMap K F))
  have : IsIntegral (pullback y f) :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral F y
  have : IsIntegral (Spec (.of (F ⊗[K] A))) := IsIntegral.of_isIso (pullbackSpecIso K F A).hom
  exact (affine_isIntegral_iff (.of (F ⊗[K] A))).mp this

theorem exists_baseChange {K F : Type} [Field K] [Field F] (e : K →+* F) (A : Type) [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] (h : ∀ (L : Type) [Field L] [Algebra K L], IsDomain (L ⊗[K] A)) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra F B) (_ : Algebra.Smooth F B) (ψ : A →+* B),
      ∀ p : A →+* F, p.comp (algebraMap K A) = e → ∃ q : B →ₐ[F] F, q.toRingHom.comp ψ = p := by
  letI := e.toAlgebra
  refine ⟨F ⊗[K] A, inferInstance, h F, inferInstance, inferInstance,
    (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := A)).toRingHom, fun p hp => ?_⟩
  let p' : A →ₐ[K] F := { p with commutes' := fun a => congr($hp a) }
  refine ⟨Algebra.TensorProduct.lift (AlgHom.id F F) p' fun _ _ => .all _ _, ?_⟩
  ext a
  simp [p']

theorem exists_root_prime (K : Type) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : n.Prime)
    (R : Type) [CommRing R] [IsDomain R] [Algebra K R] [Algebra.Smooth K R] (κ : R) (hκ : IsUnit κ)
    (p₀ p : R →ₐ[K] K) (u₀ : K) (hu : u₀ ^ n = p₀ κ) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra K B) (_ : Algebra.Smooth K B) (φ : R →ₐ[K] B)
      (r : B) (q₀ q : B →ₐ[K] K), r ^ n = φ κ ∧ q₀.comp φ = p₀ ∧ q.comp φ = p ∧ q₀ r = u₀ := by
  by_cases h : ∃ ρ : R, ρ ^ n = κ
  · obtain ⟨ρ, hρ⟩ := h
    have h₁ : p₀ κ ≠ 0 := (hκ.map p₀).ne_zero
    have h₂ : p₀ ρ ≠ 0 := by
      intro h0
      apply h₁
      rw [← hρ, map_pow, h0, zero_pow hn.ne_zero]
    refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, AlgHom.id K R,
      algebraMap K R (u₀ / p₀ ρ) * ρ, p₀, p, ?_, rfl, rfl, ?_⟩
    · rw [mul_pow, ← map_pow, div_pow, hu, ← map_pow, hρ, div_self h₁]
      simp
    · simp [h₂]
  · have hic : IsIntegrallyClosed R := GlobalTheory.isIntegrallyClosed_of_smooth K R
    let L := FractionRing R
    let f : R[X] := X ^ n - C κ
    have hf : f.Monic := monic_X_pow_sub_C κ hn.ne_zero
    have hmap : f.map (algebraMap R L) = X ^ n - C (algebraMap R L κ) := by simp [f]
    have hirr : Irreducible (f.map (algebraMap R L)) := by
      rw [hmap]
      refine X_pow_sub_C_irreducible_of_prime hn fun b hb => h ?_
      have hb' : IsIntegral R b := by
        refine ⟨f, hf, ?_⟩
        simp [f, hb]
      obtain ⟨ρ, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
      exact ⟨ρ, IsFractionRing.injective R L (by rw [map_pow, hb])⟩
    have hpr : Prime f := by
      refine ⟨hf.ne_zero, fun hu => hirr.not_isUnit (hu.map (mapRingHom (algebraMap R L))), fun a b hab => ?_⟩
      rw [← map_dvd_map (algebraMap R L) (IsFractionRing.injective R L) hf, Polynomial.map_mul] at hab
      rw [← map_dvd_map (algebraMap R L) (IsFractionRing.injective R L) hf,
        ← map_dvd_map (algebraMap R L) (IsFractionRing.injective R L) hf]
      exact hirr.prime.dvd_or_dvd hab
    have hdom : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime hpr
    have hroot : AdjoinRoot.root f ^ n = algebraMap R (AdjoinRoot f) κ := by
      have := AdjoinRoot.aeval_eq f (f := f)
      rw [AdjoinRoot.mk_self] at this
      simpa [f, sub_eq_zero] using this
    have hru : IsUnit (AdjoinRoot.root f) := by
      rw [← isUnit_pow_iff hn.ne_zero, hroot]
      exact hκ.map _
    have het : Algebra.Etale R (AdjoinRoot f) := by
      refine GlobalTheory.etale_adjoinRoot_of_isUnit_derivative hf ?_
      have : AdjoinRoot.mk f f.derivative =
          algebraMap K (AdjoinRoot f) (n : K) * AdjoinRoot.root f ^ (n - 1) := by
        simp [f, derivative_X_pow]
      rw [this]
      exact ((Ne.isUnit (Nat.cast_ne_zero.2 hn.ne_zero)).map _).mul (hru.pow _)
    have hsm : Algebra.Smooth K (AdjoinRoot f) := Algebra.Smooth.comp K R (AdjoinRoot f)
    have lift : ∀ (s : R →ₐ[K] K) (u : K), u ^ n = s κ → ∃ q : AdjoinRoot f →ₐ[K] K,
        q.comp (IsScalarTower.toAlgHom K R (AdjoinRoot f)) = s ∧ q (AdjoinRoot.root f) = u := by
      intro s u hs
      refine ⟨AdjoinRoot.liftAlgHom f s u (by simp [f, hs]), ?_, ?_⟩
      · ext a
        simp
      · simp
    obtain ⟨u, hu'⟩ := IsAlgClosed.exists_pow_nat_eq (p κ) hn.pos
    obtain ⟨q₀, h₀, h₀'⟩ := lift p₀ u₀ hu
    obtain ⟨q, h₁, -⟩ := lift p u hu'
    exact ⟨AdjoinRoot f, inferInstance, hdom, inferInstance, hsm, IsScalarTower.toAlgHom K R _,
      AdjoinRoot.root f, q₀, q, hroot, h₀, h₁, h₀'⟩

theorem exists_root (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ) : n ≠ 0 →
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra K R] [Algebra.Smooth K R] (κ : R) (_ : IsUnit κ)
    (p₀ p : R →ₐ[K] K) (u₀ : K) (_ : u₀ ^ n = p₀ κ),
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra K B) (_ : Algebra.Smooth K B) (φ : R →ₐ[K] B)
      (r : B) (q₀ q : B →ₐ[K] K), r ^ n = φ κ ∧ q₀.comp φ = p₀ ∧ q.comp φ = p ∧ q₀ r = u₀ := by
  induction n using induction_on_primes with
  | zero => exact fun h => (h rfl).elim
  | one =>
    intro _ R _ _ _ _ κ _ p₀ p u₀ hu
    exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, AlgHom.id K R, κ, p₀, p,
      by simp, rfl, rfl, by simpa using hu.symm⟩
  | prime_mul l a hl ih =>
    intro hn R _ _ _ _ κ hκ p₀ p u₀ hu
    obtain ⟨B, _, _, _, _, φ, r, q₀, q, h₁, h₂, h₃, h₄⟩ :=
      exists_root_prime K hl R κ hκ p₀ p (u₀ ^ a) (by rw [← pow_mul, mul_comm, hu])
    have hr : IsUnit r := by
      rw [← isUnit_pow_iff hl.ne_zero, h₁]
      exact hκ.map _
    obtain ⟨B', _, _, _, _, φ', r', q₀', q', g₁, g₂, g₃, g₄⟩ :=
      ih (right_ne_zero_of_mul hn) B r hr q₀ q u₀ h₄.symm
    refine ⟨B', inferInstance, inferInstance, inferInstance, inferInstance, φ'.comp φ, r', q₀', q', ?_, ?_, ?_, g₄⟩
    · rw [mul_comm, pow_mul, g₁, ← map_pow, h₁, AlgHom.comp_apply]
    · rw [← AlgHom.comp_assoc, g₂, h₂]
    · rw [← AlgHom.comp_assoc, g₃, h₃]

end Algebra

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

def IsVal (x : KeyIn ℂ) (t : ℂ) : Prop :=
  ∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
    charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8

theorem exists_isVal (hU : ThetaUnifAV) (x : KeyIn ℂ) : ∃ t, IsVal x t := by
  obtain ⟨τ, M, a, b, c, h₁, h₂, -, h₃⟩ := (GlobalTheory.KeyNormalExists.exists_normalAt hU x).1
  exact ⟨_, τ, M, a, b, c, h₁, h₂, h₃, rfl⟩

theorem val_eq_root (hL : Out.Laws) (hU : ThetaUnifAV) (hI : Key.Chi.InversionStatement) {S : Type} [CommRing S]
    (y : KeyIn S) {n : ℕ} (hn : 1 ≤ n) (κ : Sˣ)
    (hκ : ∀ (s : S →+* ℂ) (x : KeyIn ℂ) (t : ℂ), KeyPB x y s → IsVal x t → t ^ n = s κ)
    (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.Smooth ℂ B] (ψ : S →+* B) (r : B)
    (hr : r ^ n = ψ κ) (q₀ q : B →ₐ[ℂ] ℂ)
    (h₀ : ∀ x₀ : KeyIn ℂ, KeyPB x₀ y (q₀.toRingHom.comp ψ) → IsVal x₀ (q₀ r))
    (x : KeyIn ℂ) (t : ℂ) (hx : KeyPB x y (q.toRingHom.comp ψ)) (ht : IsVal x t) : t = q r := by
  obtain ⟨yB, hyB⟩ := GlobalTheory.KeyPow.keyIn_baseChange hL.polBaseChange S B y ψ
  have hex : ∀ p : B →ₐ[ℂ] ℂ, ∃ u : ℂ, (∃ z : KeyIn ℂ, KeyPB z yB p.toRingHom ∧ IsVal z u) ∧ (p = q → u = t) := by
    intro p
    by_cases hp : p = q
    · subst hp
      exact ⟨t, ⟨x, GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y yB x ψ _ hyB hx, ht⟩, fun _ => rfl⟩
    · obtain ⟨z, hz⟩ := GlobalTheory.KeyPow.keyIn_baseChange hL.polBaseChange B ℂ yB p.toRingHom
      obtain ⟨u, hu⟩ := exists_isVal hU z
      exact ⟨u, ⟨z, hz, hu⟩, fun h => (hp h).elim⟩
  choose T hT hTq using hex
  have hru : IsUnit r := by
    rw [← isUnit_pow_iff (Nat.one_le_iff_ne_zero.1 hn), hr]
    exact κ.isUnit.map ψ
  obtain ⟨r, rfl⟩ := hru
  rw [← hTq q rfl]
  refine _root_.GlobalTheory.RootConst.value_eq_unit_of_pow_eq hL hU hI B yB n r T q₀ hn hT (fun p => ?_) ?_ q
  · obtain ⟨z, hz, hu⟩ := hT p
    rw [hκ _ z _ (GlobalTheory.keyPB_trans _ _ _ y yB z ψ _ hyB hz) hu, ← map_pow, hr]
    rfl
  · obtain ⟨z, hz, hu⟩ := hT q₀
    exact _root_.GlobalTheory.NormalUnique.thetaFrame_value_unique hU hI z _ _ hu (h₀ z (GlobalTheory.keyPB_trans _ _ _ y yB z ψ _ hyB hz))

theorem val_equivariant : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → (∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf) → (∀ x : KeyIn ℂ, ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S) (y : KeyIn S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (t₀ : k), Algebra.Smooth k S ∧ (∀ (K : Type) [Field K] [Algebra k K], IsDomain (TensorProduct k K S)) ∧ KeyPB x y s ∧ ∀ (e : k →+* ℂ) (x₀ : KeyIn ℂ), KeyPB x₀ y (e.comp s₀.toRingHom) → (∃ (τ M : Matrix (Fin x₀.P.g) (Fin x₀.P.g) ℂ) (a b : Fin x₀.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x₀ τ M a b c ∧ e t₀ = M.det ^ 4 / c ^ 8)) → ∀ (f : ℂ →+* ℂ) (x x' : KeyIn ℂ) (t t' : ℂ), KeyPB x' x f → (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8) → (∃ (τ M : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (a b : Fin x'.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x' τ M a b c ∧ t' = M.det ^ 4 / c ^ 8) → t' = f t := by
  rintro hL hU hI ⟨N, hN, hR⟩ hfam f x x' t t' hx' ht ht'
  obtain ⟨k, _, _, S, _, _, y, s, s₀, t₀, hsm, hdom, hx, h₀⟩ := hfam x
  have : IsDomain S := by
    have := hdom k
    exact (Algebra.TensorProduct.lid k S).symm.toMulEquiv.isDomain _
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.KeySmoothBase.exists_unit_of_smooth hU hL.polBaseChange N hR k S y
  have hn := hN y.P.g
  let e : k →+* ℂ := s.comp (algebraMap k S)
  obtain ⟨R, _, _, _, _, ψ₁, hψ₁⟩ := exists_baseChange e S hdom
  obtain ⟨p, hp⟩ := hψ₁ s rfl
  obtain ⟨p₀, hp₀⟩ := hψ₁ (e.comp s₀.toRingHom) (by ext a; simp)
  have hu : e t₀ ^ N y.P.g = p₀ (ψ₁ κ) := by
    obtain ⟨x₀, hx₀⟩ := GlobalTheory.KeyPow.keyIn_baseChange hL.polBaseChange S ℂ y (e.comp s₀.toRingHom)
    rw [hκ _ x₀ _ hx₀ (h₀ e x₀ hx₀), ← hp₀]
    rfl
  obtain ⟨B, _, _, _, _, φ, r, q₀, q, hr, hq₀, hq, hq₀r⟩ :=
    exists_root ℂ (N y.P.g) (Nat.one_le_iff_ne_zero.1 hn) R (ψ₁ κ) (κ.isUnit.map ψ₁) p₀ p (e t₀) hu
  have key : ∀ (g : ℂ →+* ℂ) (z : KeyIn ℂ) (u : ℂ), KeyPB z y (g.comp s) → IsVal z u → u = g (q r) := by
    intro g z u hz hu
    obtain ⟨B', _, _, _, _, ψ₂, hψ₂⟩ := exists_baseChange g B fun L _ _ => isDomain_tensor_of_isAlgClosed ℂ B L
    obtain ⟨Q, hQ⟩ := hψ₂ (g.comp q.toRingHom) (by ext a; simp)
    obtain ⟨Q₀, hQ₀⟩ := hψ₂ (g.comp q₀.toRingHom) (by ext a; simp)
    have a₁ : Q.toRingHom.comp (ψ₂.comp (φ.toRingHom.comp ψ₁)) = g.comp s := by
      rw [← RingHom.comp_assoc, hQ, ← hp, ← hq]
      rfl
    have a₀ : Q₀.toRingHom.comp (ψ₂.comp (φ.toRingHom.comp ψ₁)) = (g.comp e).comp s₀.toRingHom := by
      rw [← RingHom.comp_assoc, hQ₀, RingHom.comp_assoc s₀.toRingHom, ← hp₀, ← hq₀]
      rfl
    have b₁ : Q (ψ₂ r) = g (q r) := congr($hQ r)
    have b₀ : Q₀ (ψ₂ r) = (g.comp e) t₀ := by
      rw [RingHom.comp_apply, ← hq₀r]
      exact congr($hQ₀ r)
    rw [← b₁]
    refine val_eq_root hL hU hI y hn κ hκ B' (ψ₂.comp (φ.toRingHom.comp ψ₁)) (ψ₂ r) ?_ Q₀ Q
      (fun x₀ hx₀ => ?_) z u (a₁ ▸ hz) hu
    · rw [← map_pow, hr]
      rfl
    · rw [b₀]
      exact h₀ _ x₀ (a₀ ▸ hx₀)
  have c₁ : t = q r := key (RingHom.id ℂ) x t hx ht
  rw [c₁]
  exact key f x' t' (GlobalTheory.keyPB_trans _ _ _ y x x' s f hx hx') ht'

end GlobalTheory.ThetaEquiv
end

