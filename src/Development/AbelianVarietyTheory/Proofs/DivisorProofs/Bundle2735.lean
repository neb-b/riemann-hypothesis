module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecScalOneVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointEndomorphismImageEqMovedGtPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionSectionOfSpreadThroughLatticeMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricTorsionSection_of_spread_through_latticeMap : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (o : Type) [CommRing o] (s : B ⟶ Sp o) (o₁ : o →+* V₁) (o₂ : o →+* V₂), ξ₁ ≫ s = spMap o₁ → ξ₂ ≫ s = spMap o₂ → ∀ (k : ℕ) (ζ : o), 1 ≤ k → IsUnit (k : o) → ζ ^ k = 1 → ∀ (Wo : B.Opens) (h : Wo.toScheme ⟶ H.left) (ξ₁' : Sp V₁ ⟶ Wo.toScheme) (ξ₂' : Sp V₂ ⟶ Wo.toScheme), h ≫ H.hom = Wo.ι → ξ₁' ≫ Wo.ι = ξ₁ → ξ₂' ≫ Wo.ι = ξ₂ → ∀ (F₁ : Type) [Field F₁] [IsAlgClosed F₁] [Algebra (FractionRing V₁) F₁] (F₂ : Type) [Field F₂] [IsAlgClosed F₂] [Algebra (FractionRing V₂) F₂] (c : D₁.toPre.X →+ ℤ) (x₁ : TFK (R := V₁) F₁ ⟶ A₁.A) (x₂ : TFK (R := V₂) F₂ ⟶ A₂.A), TorAt U₁ F₁ k (algebraMap (FractionRing V₁) F₁ (algebraMap V₁ (FractionRing V₁) (o₁ ζ))) c x₁ → x₁.left ≫ genMap U₁ ≫ β₁ = spMap (algebraMap (FractionRing V₁) F₁) ≫ jK V₁ ≫ ξ₁' ≫ h → x₂ ^ k = 1 → x₂.left ≫ genMap U₂ ≫ β₂ = spMap (algebraMap (FractionRing V₂) F₂) ≫ jK V₂ ≫ ξ₂' ≫ h → TorAt U₂ F₂ k (algebraMap (FractionRing V₂) F₂ (algebraMap V₂ (FractionRing V₂) (o₂ ζ))) (c.comp ρ) x₂ := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.torAt_of_spread₂ | exact GlobalTheory.Poinc.Sep.Spz.torAt_of_spread₂ | (intros; apply GlobalTheory.Poinc.Sep.Spz.torAt_of_spread₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointFrameMulEqIntegralGenerators
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.IntEval

theorem frames_mul_eq_integral : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → w.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → ∀ (h : (𝟙_ (Over (Sp V))) ⟶ G) (g' : GtPt D.toPre (𝟙_ (Over (Sp V)))) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => (h).left) (fun _ => 1))) (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, (g'.b).left] (DegPre.lineε 1))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g' → IntTerm.Ext U.toUnifPre x h → GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g' g → f.IsGen → t.IsGen → (∀ e : ℕ, GlobalTheory.Poinc.IntEval.TRel U.toUnifPre h g'.b f t e) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι) (JB : ((TF (R := V) (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good A.L z JA → Good U.LG.L z JG → Good D.toPre.P.L z JB → Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h).left) (fun _ => JA (x).left) * val (Z := (TF (R := V) (FractionRing V)).left) fr (𝟙 _) z JA * val w (𝟙 _) z JB = val f (toUnit (TF (R := V) (FractionRing V))).left z JG * val t (toUnit (TF (R := V) (FractionRing V))).left z JB := by
  intro V _ _ _ hV D A G _ _ hG U w₀ hw₀ N hN g w x fr hg hw hfr hL h g' f t hF hExt hP hf ht htl z JA JG JB hJA hJG hJB
  obtain ⟨z₀⟩ := CoefBasic.exists_pt (R := V) (F := FractionRing V)
  obtain ⟨JA₀, hA₀⟩ := CoefBasic.exists_good' A.isLB z₀
  obtain ⟨JG₀, hG₀⟩ := CoefBasic.exists_good' U.LG.isLB z₀
  obtain ⟨l, hl⟩ := CoefBasic.cstH_surj z₀ (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀
    (x.left ≫ U.gen.inv.left) z₀ (JG₀ (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA₀ x.left) *
      val (Z := (TF (R := V) (FractionRing V)).left) fr (𝟙 _) z₀ JA₀ *
      (val f (toUnit (TF (R := V) (FractionRing V))).left z₀ JG₀)⁻¹).val
  have hl0 : l ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hl
    exact Units.ne_zero _ hl.symm
  have hfv : ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG),
      Good A.L z JA → Good U.LG.L z JG →
      (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z
          (JG (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA x.left)).val *
        (val (Z := (TF (R := V) (FractionRing V)).left) fr (𝟙 _) z JA).val =
      UT.cst (FractionRing V) z l * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG).val := by
    intro z' JA' JG' hA hG'
    obtain rfl := CoefBasic.pt_eq z₀ z'
    have ind := GlobalTheory.Poinc.FrameIndep.frame_ratio_indep V _ D A G U.toUnifPre w₀ hw₀ x fr hfr h f hf hExt z₀ JA' JA₀ JG' JG₀
      hA hG' hA₀ hG₀
    rw [mul_inv_eq_iff_eq_mul] at ind
    rw [← Units.val_mul, ind, Units.val_mul, CoefBasic.cst_eq, hl]
  have hφ : DegPre.lineφ D.toPre (FractionRing V) g.b = fun i =>
      (toUnit (TF (R := V) (FractionRing V))).left ≫ (![(η[D.toPre.P.A]).left, g'.b.left] : Fin 2 → _) i := by
    funext i
    fin_cases i
    · exact Over.comp_left (f := toUnit (TF (R := V) (FractionRing V))) (g := η[D.toPre.P.A])
    · exact hP.1
  obtain ⟨w₁, hw₁, hv₁⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre (FractionRing V) g.b)
    (ε' := DegPre.lineε 1) (by rw [hφ]; exact fun _ _ _ => rfl)
    (LB.pullGen D.toPre.P.L _ _ t (toUnit (TF (R := V) (FractionRing V))).left) (pullGen_isGen _ _ _ _ ht _)
  obtain ⟨w', hw', hwv⟩ := TorsionValue.exists_frm_scale w₁ hw₁ (inv_ne_zero hl0)
  have hwt : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z l * (val w' (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
    intro z J hJ
    rw [hwv z J hJ, hv₁ _ _ z J hJ, val_pull hJ, Category.id_comp, ← _root_.mul_assoc, GlobalTheory.UT.CoefBasic.cst_eq,
      GlobalTheory.UT.CoefBasic.cst_eq, ← map_mul, mul_inv_cancel₀ hl0, map_one, _root_.one_mul]
  have hLies : LiesOver U.toUnifPre w₀ g w' x fr := by
    intro k hk wk hwk hwkg s s' v hExp hVal
    obtain ⟨σ', hIso, n, c, σ, fs, hE, hσ, hs⟩ := hExp
    choose xs hxs using fun i => GlobalTheory.ExpansionValueZero.exists_coeff (A := V) U.LG.isLB (σ i) h.left
      (GeneratorPullback.powGen U.LG.L _ _ f k) (powGen_isGen _ _ _ _ hf k) (fun W _ q => by simp)
    have hxs' : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp V) z J, Good U.LG.L z J →
        sval (σ i) (r ≫ h.left) z J = Geo.Tor.cst r z (xs i) * (val f r z J ^ k).val :=
      fun i Z r z J hJ => (hxs i Z r z J hJ).trans (by rw [val_pow])
    choose a ha using fun i α => GlobalTheory.T.exists_integral_coefficient_section_coordinate_rig V D.toPre g' t ht k α (fs i α)
    have hv := GlobalTheory.T.section_value_generic_point_integral_section V (maximalIdeal V) D A G U.toUnifPre w₀ x fr h l f hExt hfv k s σ' hIso n c σ hσ xs hxs' v hVal
    have hwk' : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z (l ^ k) * (val wk (𝟙 _) z J).val =
        (val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ k).val := by
      intro z J hJ
      rw [hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hwt z J hJ, mul_pow,
        GlobalTheory.UT.CoefBasic.cst_eq, GlobalTheory.UT.CoefBasic.cst_eq, map_pow]
    have hc := GlobalTheory.T.integral_combination_terms_rational_point_frame V D.toPre g' g hP t l hl0 k wk hwkg hwk' s' n c fs hs a ha
    have hI := admissibleBase_of_completeNormalLocalCharZero hV
    have key := EvalZero.sumF_comb hI (FractionRing V) Finset.univ (fun i => c i * (l ^ k)⁻¹) _ _ fun i =>
      EvalZero.sumF_map (maximalIdeal V) (FractionRing V) (a i) (xs i) fun e' =>
        GlobalTheory.T.section_value_integral_point_congruent_term_sum V (maximalIdeal V) D A G U.toUnifPre h g' hF f t e' k (htl e') (σ i) (fs i) (hE i e') (xs i) (hxs' i)
          (a i) (ha i)
    have hlk : l ^ k ≠ 0 := pow_ne_zero _ hl0
    convert (preTransparency := .reducible) key using 1
    · funext α
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (a i α)) =
          (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (a i α) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
        ← hc α, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]
    · simp only [Algebra.algebraMap_self, RingHom.id_apply]
      rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (xs i)) =
          (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (xs i) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
        ← hv, mul_comm v, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]
  haveI : CharZero V := hV.2.2.2
  have heq := LiesUniq.frame_unique (admissibleBase_of_completeNormalLocalCharZero hV) hG U hw₀ hw hw' hfr hL hLies z JB hJB
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hfv z JA JG hJA hJG, ← hwt z JB hJB, heq]
  ring

end GlobalTheory.Poinc.IntEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorPointOverStrictHenselisationNoetherianNormStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsor_point_over_strictHenselisation_noetherianNormal : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O, σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA := by
  first | (exact @GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType) | (exact GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType) | (intros; apply GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateUniformisationTranslateEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.TranslCoord

theorem coord_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)), wL.IsGen → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e) z J := by
  intro R _ _ _ hR D A G _ _ hG U g hg a ha hlev A₂ D₂ U₂ wL hwL β hβ hp w hw xe hker hc e h hh hfst χ Z r z J J' hJ hJ'
  have hpg := _root_.GlobalTheory.MumCmp.Transl.pG_comp_lift_translate R (maximalIdeal R) D D₂ A A₂ G U.toUnifPre U₂.toUnifPre g a β hβ e (hp e)
    (fun ae h1 h2 => (hlev e ae h1 h2).1) h hh hfst
  obtain ⟨u, hu, hu'⟩ := _root_.GlobalTheory.MumCmp.TranslRatio.exists_ratio_gen (U.gt e) (U₂.gt e) β.hom g w hw χ (xe χ) (hc χ) h hh hpg
  have hp' : (U₂.gt e).pG ≫ β.hom = (U.gt e).pG := Over.OverMorphism.ext (hp e)
  have := (U.gt e).q_flat
  have := (U.gt e).q_surj
  have := (U.gt e).q_affine
  obtain ⟨v, hv, hv'⟩ := GlobalTheory.CoordCompare.exists_gen_of_val_eq D.toPre.P.isLB _ _ (U.gt e).q.left u hu
    (fun Z r r' z J hJ hrr => by
      obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D₂.toPre.P.L D₂.toPre.P.isLB z
      rw [hu' Z r z J J' hJ hJ', hu' Z r' z J J' hJ hJ']
      exact _root_.GlobalTheory.TwCoordInv.ratio_translate_invariant (U.gt e) (U₂.gt e) β.hom hp' g w χ (xe χ)
        (fun Z r z J J' hJ hJ' h1 h2 => hker e Z r z J J' hJ hJ' h1 h2 χ) a h hh hfst r r' z J J' hJ hJ' hrr)
  have h1 := GlobalTheory.CoordCompare.val_eq_one GlobalTheory.globalFns_holds (D.toPre.c (xe χ)) _ rfl v hv (fun y J hJ => by
      obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D₂.toPre.P.L D₂.toPre.P.isLB y
      have := (U.gt e).q_hom
      have k := hv' _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶ thickObj R (maximalIdeal R) e G).left y J hJ
      rw [← Over.comp_left, MonObj.one_comp] at k
      rw [k, hu' _ _ y J J' hJ hJ']
      exact _root_.GlobalTheory.Mum.twistRatio_eq_one_at_unit (U.gt e) (U₂.gt e) β.hom g w χ (xe χ) a h hh hfst (fun ae h1 h2 => (hlev e ae h1 h2).2 (xe χ)) y J J' hJ hJ')
    Z (r ≫ (U.gt e).q.left) z J hJ
  rw [hv' Z r z J hJ, hu' Z r z J J' hJ hJ', mul_inv_eq_one] at h1
  exact h1

end GlobalTheory.MumCmp.TranslCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitEquivariantBijectionTransportCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem trait_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), Eqv T.D'.toPre T.A F (C.n ^ j) lab' E' → ∃ (lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A)) (E : Fam D.toPre F (C.n ^ j) → SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)) (Φ : Fam D.toPre F (C.n ^ j) → Fam T.D'.toPre F (C.n ^ j)), LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ (∀ (s : Fam D.toPre F (C.n ^ j)) (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)), F₀.Over s → (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((Φ s).s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1)) ∧ ∀ (s : Fam D.toPre F (C.n ^ j)) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' (Φ s)) q z Jt := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ em hc f hf hfst hα w₀ hw₀ lab' hlab' E' hE'
  obtain ⟨Φ, hΦb, hΦa, hΦs, hΦP, hΦp, hΦf⟩ := GlobalTheory.FamPull.fam_transport R D W T.φ T.D' T.hD F hc (C.n ^ j)
  obtain ⟨lab, hLE, hon, hlr⟩ := GlobalTheory.Mum.Trait.exists_lab_push R hR D C j W T F em hc f hf hfst hα lab' hlab' hE'.onto
  obtain ⟨Tr, hTb, hTa, hTs, hTv⟩ := GlobalTheory.Mum.SecMove.exists_trait_transport R hR D C j wA hwA W T F hc f hf hfst hα w₀ hw₀
  have hC2 := GlobalTheory.T.transport_symmetric_lifts_theta_group_trait R hR D C j wA hwA W T F hc f hf hfst hα w₀ hw₀
  refine ⟨lab, fun s => Tr (E' (Φ s)), Φ, hLE, ⟨?_, ?_, ?_, hon, ?_, ?_, ?_⟩, hΦP, fun s => hTv (E' (Φ s))⟩
  · exact hTb.comp (hE'.bij.comp hΦb)
  · intro s s' s'' h i
    exact hTa _ _ _ (hE'.add _ _ _ (hΦa s s' s'' h)) i
  · intro c s s' h i
    exact hTs c _ _ (hE'.smul c _ _ (hΦs c s s' h)) i
  · intro p
    obtain ⟨p', hy, hg⟩ := hΦp p
    exact (hΦf p p' hy hg).1 (hE'.frame p')
  · intro p
    obtain ⟨p', hy, hg⟩ := hΦp p
    exact (hC2 _ _ (hlr p p' hy hg) ((hE'.onto _).2 ⟨p', rfl⟩)).1 (hE'.lift p')
  · intro p w θ s s' hw hθ hr
    obtain ⟨p', hy, hg⟩ := hΦp p
    obtain ⟨w', hw', hr'⟩ := (hΦf p p' hy hg).2 w hw
    obtain ⟨θ', hθ', hact⟩ := (hC2 _ _ (hlr p p' hy hg) ((hE'.onto _).2 ⟨p', rfl⟩)).2 θ hθ
    exact hact _ _ _ _ (hTv _) (hTv _) (hE'.act p' w' θ' _ _ hw' hθ' (hr' s s' hr))

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitTorsionPointMapCommutesCharInjectiveHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two.KeyDvr
open GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic GlobalTheory.UT.EndTors
attribute [local instance] gtGroup

theorem act_zero₂ {R : Type} [CommRing R] [IsDomain R] {D₁ D₂ : DegPre R} (b : D₁.P.A ⟶ D₂.P.A) [IsMonHom b]
    (h : D₂.X →+ D₁.X) {F : Type} [Field F] [Algebra (FractionRing R) F] {o₁ : GtPtF D₁ F} {o₂ : GtPtF D₂ F}
    (h₁ : o₁.IsZero) (h₂ : o₂.IsZero) : Act D₁ D₂ b h o₁ o₂ := by
  obtain ⟨hb₁, hv₁⟩ := (isZero_iff o₁).1 h₁
  obtain ⟨hb₂, hv₂⟩ := (isZero_iff o₂).1 h₂
  refine ⟨by rw [hb₂, hb₁, MonObj.one_comp], fun χ u hu z J hJ => ?_⟩
  rw [hv₂ _ z _ ((isPart_inr (M₁ := D₁.P.L) (M₂ := D₂.P.L)).good hJ),
    hv₁ _ z _ ((isPart_inl (M₁ := D₁.P.L) (M₂ := D₂.P.L)).good hJ), hb₁, _root_.one_mul]
  exact (hu.2 _ (TF (R := R) F).hom z J hJ).symm

theorem sumV_shift₂ {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {X X' : Type} [AddCommGroup X]
    [AddCommGroup X'] (h : X' →+ X) (y : X') (y' : X) {B₁ B₂ b₁ b₂ : X' → F} {C₁ C₂ c₁ c₂ : X → F}
    (hB₁ : ∀ α, B₁ (α + y) = b₁ α) (hB₂ : ∀ α, B₂ (α + y) = b₂ α)
    (hC₁ : ∀ α, C₁ (α + y') = c₁ α) (hC₂ : ∀ α, C₂ (α + y') = c₂ α)
    (H : ∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => b₁ p.1.1 * c₂ p.1.2 - b₂ p.1.1 * c₁ p.1.2) 0)
    (α : X) :
    SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0 := by
  refine sumV_equiv v (Equiv.subtypeEquiv ((Equiv.addRight y).prodCongr (Equiv.addRight y')) fun p => ?_) (fun p => ?_)
    (H (α - h y - y'))
  · simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight, map_add (f := _)]
    constructor
    · intro e; rw [show α = α - h y - y' + h y + y' by abel, ← e]; abel
    · intro e; rw [← e]; abel
  · simp only [Equiv.subtypeEquiv_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight,
      hB₁, hB₂, hC₁, hC₂]

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (A₁ A₂ : PolAV (Sp (FractionRing V))) (G₁ G₂ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif (maximalIdeal V) D₁ A₁ G₁) (U₂ : Unif (maximalIdeal V) D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → Function.Injective h → Key U₁.toUnifPre U₂.toUnifPre c b h F := by
  intro V _ _ _ _ hV ϖ hϖ F _ _ _ v hv D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ a c b h hc hgen hlin hcoord hE
    k hk p x hx g' hg'
  have hL : LL := GlobalTheory.firstFiveLaws
  obtain ⟨-, h₁, h₂, h₃, h₄⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  choose Q hQ' using QForm.exists_QVal hϖ D₂
  have hQ : QForm.IsQ D₂.toPre ϖ Q := hQ'
  have hB := D₂.tau_bimult
  have := hc
  have := hlin.2.1
  have CV := GlobalTheory.UT.CoefVal.main hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D₂ Q hQ F v hv
  have EV₁ := GlobalTheory.UT.EvalZero.value_at_origin hL V _ hA D₁ A₁ G₁ hG₁ U₁ F
  have EV₂ := GlobalTheory.UT.EvalZero.value_at_origin hL V _ hA D₂ A₂ G₂ hG₂ U₂ F
  have LU₁ := _root_.GlobalTheory.LevelCompat.qkToAkU_level hL V _ hA D₁ A₁ G₁ hG₁ U₁ F
  have LU₂ := _root_.GlobalTheory.LevelCompat.qkToAkU_level hL V _ hA D₂ A₂ G₂ hG₂ U₂ F
  have BJ₁ := (expBijF_and_expandsF_lin hL V _ hA D₁ A₁ G₁ hG₁ U₁).1 F
  have BJ₂ := (expBijF_and_expandsF_lin hL V _ hA D₂ A₂ G₂ hG₂ U₂).1 F
  have SV := fun Ix => AdicValSum.main V ϖ hϖ F v hv Ix
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D₂ A₂ G₂ hG₂ U₂ F k hk
  obtain ⟨ρ₁, hρ₁⟩ := EV₁.1
  obtain ⟨w₀₁, hN₁⟩ := EV₁.2.1 ρ₁ hρ₁
  obtain ⟨ρ₂, hρ₂⟩ := EV₂.1
  obtain ⟨w₀₂, hN₂⟩ := EV₂.2.1 ρ₂ hρ₂
  have hw₀₁ := hN₁.1
  have hw₀₂ := hN₂.1
  have hxk : x ^ k = 1 := (hx w₀₁ hw₀₁).1
  obtain ⟨p₀, hp₀⟩ := f₂ (x ≫ c) (by rw [← MonObj.pow_comp, hxk, MonObj.one_comp])
  obtain ⟨l', hl', -⟩ := (CV g').1
  obtain ⟨z, hz⟩ := GlobalTheory.exists_rep_mod_shifted_form_small D₂.toPre.X Q (QForm.bHom hϖ D₂ hQ)
    (fun a₀ b₀ => by rw [QForm.bHom_apply, QForm.bOf]; ring) (QForm.two_Q_eq hϖ D₂ hQ)
    (fun a ha => QForm.Q_pos hϖ D₂ hQ ha) (k • l') k hk p₀.y
  let p₁ : QkPt D₂.toPre F k := qkMk hB (p₀.y + k • z) (p₀.g + iota hB F z)
    (by rw [nsmul_add, qk_nsmul hB, map_add (f := _), map_nsmul])
  have hp₁ : QkToAkU U₂.toUnifPre F k p₁ (x ≫ c) :=
    (f₁ _ _).2 (hp₀.symm.trans ((f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨z, rfl, rfl⟩)))
  let d : GtPtF D₂.toPre F := g' - p₁.g
  have hd : d.IsAdd p₁.g g' := (isAdd_iff_eq _ _ _).2 (sub_add_cancel _ _).symm
  obtain ⟨l, hl, -⟩ := (CV d).1
  obtain ⟨l₁, hl₁, -⟩ := (CV p₁.g).1
  have ho : (0 : GtPtF D₂.toPre F).IsZero := (isZero_iff_eq _).2 rfl
  have ho₁ : (0 : GtPtF D₁.toPre F).IsZero := (isZero_iff_eq _).2 rfl
  suffices H : d.IsZero from ⟨p₁, (sub_eq_zero.1 ((isZero_iff_eq _).1 H)).symm, hp₁⟩
  have gu : ∀ (g : GtPtF D₂.toPre F) (a b : D₂.toPre.X →+ ℚ), GtV hϖ hv g a → GtV hϖ hv g b → a = b :=
    fun g a b ha hb => (CV g).1.unique ha hb
  have k0 : (0 : ℚ) < k := by exact_mod_cast hk
  refine _root_.GlobalTheory.UT.SmallZero.main hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D₂ Q hQ F v hv k hk d 0 l ho hl (fun m => ?_) fun n j hn hj w₁ hw₁ => ?_
  · have e₁ := gu g' l' (l + l₁) hl' ((CV d).2.2.2.1 p₁.g g' l l₁ hd hl hl₁)
    have e₂ := gu p₁.g l₁ ((k : ℚ)⁻¹ • (Int.castAddHom ℚ).comp (QForm.bHom hϖ D₂ hQ p₁.y)) hl₁ (by
      have := (CV p₁.g).2.2.2.2.1 k hk p₁
      convert this using 2 with χ
      simp [QForm.bHom_apply, div_eq_inv_mul])
    have e₃ := hz m
    have e₄ : ((QForm.bHom hϖ D₂ hQ (p₀.y + k • z) m : ℤ) : ℚ) - (k • l') m = -(k * l m) := by
      rw [e₁, e₂]
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, Int.coe_castAddHom,
        smul_eq_mul, nsmul_eq_mul]
      dsimp [p₁, qkMk]
      show _ - (k : ℚ) * (l m + (k : ℚ)⁻¹ * ((QForm.bHom hϖ D₂ hQ (p₀.y + k • z) m : ℤ) : ℚ)) = _
      field_simp
      ring
    rw [e₄, abs_neg, abs_mul, abs_of_pos k0] at e₃
    exact le_of_mul_le_mul_left e₃ k0
  have up₂ : ∀ (r : QkPt D₂.toPre F k) (n N : ℕ), N = k * n → ∃ q : QkPt D₂.toPre F N, q.y = n • r.y ∧ q.g = r.g :=
    fun r n N h => ⟨qkMk hB (n • r.y) r.g (by rw [h, mul_nsmul, qk_nsmul hB, map_nsmul]), rfl, rfl⟩
  have hB₁ := D₁.tau_bimult
  have up₁ : ∀ (r : QkPt D₁.toPre F k) (n N : ℕ), N = k * n → ∃ q : QkPt D₁.toPre F N, q.y = n • r.y ∧ q.g = r.g :=
    fun r n N h => ⟨qkMk hB₁ (n • r.y) r.g (by rw [h, mul_nsmul, qk_nsmul hB₁, map_nsmul]), rfl, rfl⟩
  have hj1 : 1 ≤ j := hj ▸ Nat.mul_pos hk hn
  obtain ⟨q₁, qy₁, qg₁⟩ := up₂ p₁ n j hj
  obtain ⟨w, hw⟩ := (coef_basic V D₂.toPre F j d).1
  obtain ⟨θ, hθ, ω, hω, K⟩ := exists_pre_coef hL hA hG₂ U₂ hj1 q₁
    (((LU₂ k n j hk hn hj p₁ q₁ _).1 qy₁ qg₁).1 hp₁) hw₀₂ (qg₁ ▸ hd) hw
  refine ⟨w, hw, fun S₁ S₂ hS => ?_⟩
  obtain ⟨T₁, hT₁, -⟩ := (BJ₂ j hj1 w₀₂ hw₀₂).2 S₁
  obtain ⟨T₂, hT₂, -⟩ := (BJ₂ j hj1 w₀₂ hw₀₂).2 S₂
  obtain ⟨n', hn', CR⟩ := _root_.GlobalTheory.Mum.Two.exists_crossH V A₁ A₂ F c hc j k hk
  obtain ⟨T₁', T₂', hC, hne⟩ := CR T₁ T₂
  have hj' : 1 ≤ k * n' := Nat.mul_pos hk hn'
  obtain ⟨S₁', hT₁', -⟩ := (BJ₁ _ hj' w₀₁ hw₀₁).1 T₁'
  obtain ⟨S₂', hT₂', -⟩ := (BJ₁ _ hj' w₀₁ hw₀₁).1 T₂'
  obtain ⟨w₁', hw₁'⟩ := (coef_basic V D₁.toPre F (k * n') 0).2.1 zero_b
  obtain ⟨q, qy, qg⟩ := up₁ p n' _ rfl
  obtain ⟨θ', hθ', ω', hω', K'⟩ := exists_pre_coef hL hA hG₁ U₁ hj' q
    (((LU₁ k n' _ hk hn' rfl p q _).1 qy qg).1 hx) hw₀₁
    (g₀ := 0) (g₁ := p.g) ((isAdd_iff_eq _ _ _).2 (by rw [qg, zero_add])) hw₁'.1
  obtain ⟨t₁, s₁, a₁, e₁, c₁⟩ := K T₁ S₁ hT₁
  obtain ⟨t₂, s₂, a₂, e₂, c₂⟩ := K T₂ S₂ hT₂
  obtain ⟨t₁', s₁', a₁', e₁', c₁'⟩ := K' T₁' S₁' hT₁'
  obtain ⟨t₂', s₂', a₂', e₂', c₂'⟩ := K' T₂' S₂' hT₂'
  have hC' := (GlobalTheory.T.thetaSectionCrossRelation_iff_of_thetaAction V A₁ A₂ F c hc j _ θ θ' (by rw [hθ, hθ']) _ _ _ _ _ _ _ _
    a₁ a₂ a₁' a₂').2 hC
  have nl₂ : ∀ (g : GtPtF D₂.toPre F) (i : ℕ), 1 ≤ i → ∀ (u : Frm D₂.toPre F i g.b) (s : Fam D₂.toPre F i), u.IsGen →
      NullV v (coef s g u) := fun g i hi u s hu => ((CV g).2.2.2.2.2.2 i hi u s hu).1
  choose Q₁ hQ₁' using QForm.exists_QVal hϖ D₁
  have hQ₁ : QForm.IsQ D₁.toPre ϖ Q₁ := hQ₁'
  have CV₁ := GlobalTheory.UT.CoefVal.main hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D₁ Q₁ hQ₁ F v hv
  have nl₁ : ∀ (g : GtPtF D₁.toPre F) (i : ℕ), 1 ≤ i → ∀ (u : Frm D₁.toPre F i g.b) (s : Fam D₁.toPre F i), u.IsGen →
      NullV v (coef s g u) := fun g i hi u s hu => ((CV₁ g).2.2.2.2.2.2 i hi u s hu).1
  have MX := _root_.GlobalTheory.Mum.MixTwo.main V _ hA D₁ D₂ A₁ A₂ G₁ G₂ hG₁ hG₂ U₁ U₂ a c b h hc hgen hlin hcoord F w₀₁ w₀₂ hw₀₁ hw₀₂
  refine _root_.GlobalTheory.UT.sumV_cancel_hom F v D₁.toPre.X D₂.toPre.X h hE (coef S₁ 0 w₁) (coef S₂ 0 w₁) (coef S₁ d w) (coef S₂ d w)
    (coef S₁' 0 w₁') (coef S₂' 0 w₁') (nl₂ _ _ hj1 _ _ hw₁.1) (nl₂ _ _ hj1 _ _ hw₁.1) (nl₂ _ _ hj1 _ _ hw)
    (nl₂ _ _ hj1 _ _ hw) (nl₁ _ _ hj' _ _ hw₁'.1) (nl₁ _ _ hj' _ _ hw₁'.1)
    (fun α => (SV _ _ _ (MX j _ hj1 hj' _ _ _ _ _ _ _ _ hT₁ hT₂ hT₁' hT₂' hC 0 0 (act_zero₂ b h ho₁ ho) w₁ w₁'
      hw₁.1 hw₁'.1 α)).1)
    (sumV_shift₂ v h q₁.y q.y c₁ c₂ c₁' c₂' fun α => (SV _ _ _ (MX j _ hj1 hj' _ _ _ _ _ _ _ _ e₁ e₂ e₁' e₂'
      hC' p.g g' hg' ω ω' hω hω' α)).1) fun h0 => ?_
  obtain ⟨cc, hcc⟩ := exists_value hρ₂ T₂
  obtain ⟨cc', hcc'⟩ := exists_value hρ₁ T₂'
  have σ := (SV _ _ _ (EV₂.2.2 w₀₂ ρ₂ hN₂ j T₂ S₂ hT₂ 0 w₁ ho hw₁ cc hcc)).1
  have σ' := (SV _ _ _ (EV₁.2.2 w₀₁ ρ₁ hN₁ _ T₂' S₂' hT₂' 0 w₁' ho₁ hw₁' cc' hcc')).1
  rw [h0] at σ'
  obtain rfl := eq_zero_of_sumV_zero v σ'
  obtain ⟨y⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := V) F).left) A₁.isLB y
  refine hne (fun y J hJ h => hS ?_) y J hJ ((hcc' y J hJ).trans ?_)
  · have e : cstH (R := V) y cc = 0 :=
      (cst_eq y cc).symm.trans ((Units.mul_left_eq_zero _).1 ((hcc y J hJ).symm.trans h))
    obtain rfl : cc = 0 := cstH_inj y (e.trans (map_zero _).symm)
    exact σ
  · exact mul_eq_zero_of_left ((cst_eq y 0).trans (map_zero _)) _

end GlobalTheory.Mum.Two.KeyDvr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateDualNumberPointInverseConstantTangentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_dual_number_point_inverse_constant_tangent : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (S : Type) [CommRing S] (A : Over (Sp S)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (c : epsR S ⟶ A) (p : Sp S ⟶ A.left), c.left = spMap (algebraMap S (DualNumber S)) ≫ p → ∀ y : epsR S ⟶ A, (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ y.left = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ c.left ↔ IsTangent (y * c⁻¹)) ∧ ∀ f, tanVal y f = tanVal (y * c⁻¹) f := by
  first | exact @GlobalTheory.TanAdd.translate_const | exact GlobalTheory.TanAdd.translate_const | (intros; apply GlobalTheory.TanAdd.translate_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationMovesAlongDvrInjectionGivenFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_moves_along_dvr_injection_given_fibre : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'], IsAdicComplete (maximalIdeal V) V → IsAdicComplete (maximalIdeal V') V' → ∀ (φ : V →+* V') (φK : FractionRing V →+* FractionRing V'), φK.comp (algebraMap V _) = (algebraMap V' _).comp φ → (maximalIdeal V).map φ ≤ maximalIdeal V' → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (A' : PolAV (Sp (FractionRing V'))) (ψ : A'.A.left ⟶ A.A.left), IsGrpPullback A'.A A.A (spMap φK) ψ → LBIso A'.L (A.L.pull ψ) → A'.g = A.g → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing V') F], (algebraMap (FractionRing V') F).comp φK = algebraMap (FractionRing V) F → ∃ (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg φ D.toPre D'.toPre) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal V') D' A' G'), IsSemiAbelian G' ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (q : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), QkToAkU U.toUnifPre F k q x → ∃ (q' : QkPt D'.toPre F k) (x' : TFK (R := V') F ⟶ A'.A), hD.xe q'.y = q.y ∧ x'.left ≫ ψ = x.left ∧ QkToAkU U'.toUnifPre F k q' x' := by
  first | exact @GlobalTheory.UnifMoveGiven.move_given | exact GlobalTheory.UnifMoveGiven.move_given | (intros; apply GlobalTheory.UnifMoveGiven.move_given <;> assumption)
end

