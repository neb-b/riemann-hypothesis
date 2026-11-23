module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2251
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0193
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2529
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusPairOfTorsionPointOver
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

namespace GlobalTheory.Poinc.Sep.LiesPair

theorem exists_pair_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → w.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → ∃ p : QkPt D.toPre (FractionRing V) N, p.y = 0 ∧ p.g = g ∧ QkToAkU U.toUnifPre (FractionRing V) N p x := by
  intro V _ _ _ hCN D A G _ _ hG U w₀ hw₀ N hN g w x fr hg hw hfr hov
  haveI : CharZero V := hCN.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  have hB := D.tau_bimult
  obtain ⟨o, ho₁, ho₂⟩ := hg
  let p : QkPt D.toPre (FractionRing V) N :=
    ⟨0, g, o, ho₁, GlobalTheory.TorsionQk.isIota_zero hB ho₂⟩
  obtain ⟨pb, hp⟩ := qkExtExists V D.toPre (FractionRing V)
    (AlgebraicClosure (FractionRing V)) (algebraMap _ _) (fun r => by simp) N p
  let xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    GlobalTheory.TorsionExt.fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x
  obtain ⟨wb, frb, hwb, hfrb, hlb⟩ := GlobalTheory.T.torusExtension_point_liesOver_after_field_extension V _ hA D A G hG U (AlgebraicClosure (FractionRing V)) w₀
    hw₀ g w x fr hw hfr hov xb rfl
  obtain ⟨f', f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U (AlgebraicClosure (FractionRing V)) N hN
  have hq := (f₁ pb (f' pb)).2 rfl
  obtain ⟨w', fr', hw', hfr', hl'⟩ := GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU V _ hA D A G hG U
    (AlgebraicClosure (FractionRing V)) w₀ hw₀ _ hN pb (f' pb) hp.1 hq
  have hpb := (GlobalTheory.TorusExt.eq_gtExt_iff _ (RingHom.comp_id _) _ _).2 hp.2
  obtain ⟨wb₂, hwb₂, hlb₂⟩ : ∃ wb₂ : Frm D.toPre (AlgebraicClosure (FractionRing V)) 1 pb.g.b,
      wb₂.IsGen ∧ LiesOver U.toUnifPre w₀ pb.g wb₂ xb frb := by
    rw [hpb]
    exact ⟨wb, hwb, hlb⟩
  have e := GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver hL V _ hA D A G hG U (AlgebraicClosure (FractionRing V)) w₀ hw₀
    pb.g wb₂ w' xb (f' pb) frb fr' hwb₂ hw' hfrb hfr' hlb₂ hl'
  refine ⟨p, rfl, rfl, ?_⟩
  refine (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hN hp x).2 ?_
  rw [← e] at hq
  exact hq

end GlobalTheory.Poinc.Sep.LiesPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusSpreadOverTraitSpecialisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem isLocalHom_of_map_maximalIdeal {W κ : Type} [CommRing W] [IsLocalRing W] [Field κ] (c : W →+* κ)
    (hc : ∀ x ∈ maximalIdeal W, c x = 0) : IsLocalHom c :=
  ⟨fun a ha => by
    by_contra h
    have hm : a ∈ maximalIdeal W := (IsLocalRing.mem_maximalIdeal a).2 h
    rw [hc a hm] at ha
    exact not_isUnit_zero ha⟩

theorem exists_common_residue {R W V : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] [CommRing V]
    [IsLocalRing V] (ψ : R →+* W) [IsLocalHom ψ] (g : R →+* V) [IsLocalHom g] :
    ∃ (κ : Type) (_ : Field κ) (c : W →+* κ) (b : V →+* κ), (∀ x ∈ maximalIdeal W, c x = 0) ∧
      (∀ x ∈ maximalIdeal V, b x = 0) ∧ c.comp ψ = b.comp g := by
  letI : Algebra (ResidueField R) (ResidueField W) := (ResidueField.map ψ).toAlgebra
  letI : Algebra (ResidueField R) (ResidueField V) := (ResidueField.map g).toAlgebra
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (ResidueField W ⊗[ResidueField R] ResidueField V)
  letI := Ideal.Quotient.field M
  let q := Ideal.Quotient.mk M
  refine ⟨_ ⧸ M, inferInstance, q.comp ((Algebra.TensorProduct.includeLeftRingHom).comp (residue W)),
    q.comp ((Algebra.TensorProduct.includeRight.toRingHom).comp (residue V)), fun x hx => ?_, fun x hx => ?_,
    RingHom.ext fun r => ?_⟩
  · simp [(IsLocalRing.residue_eq_zero_iff x).2 hx]
  · simp [(IsLocalRing.residue_eq_zero_iff x).2 hx]
  · simp only [RingHom.comp_apply]
    congr 1
    rw [← ResidueField.map_residue ψ r, ← ResidueField.map_residue g r]
    change Algebra.TensorProduct.includeLeftRingHom (algebraMap (ResidueField R) (ResidueField W) (residue R r)) =
      Algebra.TensorProduct.includeRight (algebraMap (ResidueField R) (ResidueField V) (residue R r))
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem spread₂_of_trait {B : Scheme.{0}} (H : Over B) [GrpObj H]
    {V₁ : Type} [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] {D₁ : DegData V₁ (maximalIdeal V₁)}
    {A₁ : PolAV (Sp (FractionRing V₁))} {G₁ : Over (Sp V₁)} [GrpObj G₁] [IsCommMonObj G₁]
    {V₂ : Type} [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] {D₂ : DegData V₂ (maximalIdeal V₂)}
    {A₂ : PolAV (Sp (FractionRing V₂))} {G₂ : Over (Sp V₂)} [GrpObj G₂] [IsCommMonObj G₂]
    (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left)
    (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left)
    {R : Type} [CommRing R] [IsLocalRing R] (ιB : Sp R ⟶ B) (HR : Over (Sp R)) [GrpObj HR] [IsCommMonObj HR]
    (φR : HR.left ⟶ H.left) (hR : IsGrpPullback HR H ιB φR)
    (g₁ : R →+* V₁) (β₁' : G₁.left ⟶ HR.left) (eβ₁ : β₁' ≫ φR = β₁) (hξ₁ : spMap g₁ ≫ ιB = ξ₁)
    (g₂ : R →+* V₂) (hg₂ : IsLocalHom g₂) (β₂' : G₂.left ⟶ HR.left) (hβ₂ : IsGrpPullback G₂ HR (spMap g₂) β₂')
    (eβ₂ : β₂' ≫ φR = β₂) (hξ₂ : spMap g₂ ≫ ιB = ξ₂)
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (ψ₀ : R →+* W) (hψ : IsLocalHom ψ₀)
    (Ω : Type) [Field Ω] (α : W →+* Ω) (hα : Function.Injective α) (b₁ : V₁ →+* Ω)
    (hb₁ : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0) (eα : α.comp ψ₀ = b₁.comp g₁)
    (GΩ : Over (Sp Ω)) [GrpObj GΩ] (n : GΩ.left ⟶ ((Over.pullback (spMap ψ₀)).obj HR).left)
    (hn : IsGrpPullback GΩ ((Over.pullback (spMap ψ₀)).obj HR) (spMap α) n)
    (n₁ : GΩ.left ⟶ G₁.left) (hn₁ : IsGrpPullback GΩ G₁ (spMap b₁) n₁)
    (hnn : n ≫ pullback.fst HR.hom (spMap ψ₀) = n₁ ≫ β₁')
    (j : splitTorus (Sp W) D₁.toPre.X ⟶ (Over.pullback (spMap ψ₀)).obj HR) (hj : IsMonHom j)
    (ej : GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb₁ hn₁) :
    ∃ ρ, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ := by
  haveI := hψ
  haveI := hg₂
  haveI := hj
  obtain ⟨κ, _, c, b₂, hc0, hb0, ec⟩ := exists_common_residue ψ₀ g₂
  have hcl : IsLocalHom c := isLocalHom_of_map_maximalIdeal c hc0
  have hb₂ := GlobalTheory.TorusPart.map_pow_one_eq_zero hb0
  have hW := isGrpPullback_pullback HR (spMap ψ₀)
  have hm := isGrpPullback_pullback ((Over.pullback (spMap ψ₀)).obj HR) (spMap c)
  obtain ⟨m₂, hm₂, em₂⟩ := GlobalTheory.SpreadTrait.pull_cancel hβ₂ (spMap b₂)
    ((hm.comp hW).congr ((GlobalTheory.SpreadTrait.spMap_comp' ψ₀ c).trans
      ((congrArg spMap ec).trans (GlobalTheory.SpreadTrait.spMap_comp' g₂ b₂).symm)) rfl)
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U₂.gt 0) hb₂ hm₂).2 _
    (GlobalTheory.TorusPart.pullTorus hm j) inferInstance
  refine ⟨ρ, W, inferInstance, inferInstance, inferInstance, spMap ψ₀ ≫ ιB, (Over.pullback (spMap ψ₀)).obj HR,
    inferInstance, inferInstance, pullback.fst HR.hom (spMap ψ₀) ≫ φR, j, Ω, inferInstance, α, b₁, hb₁, GΩ,
    inferInstance, n, hn, n₁, hn₁, κ, inferInstance, c, b₂, hb₂, _, inferInstance, _, hm, m₂, hm₂, hW.comp hR, hj, hα,
    hcl, ?_, ?_, ?_, ?_, ej, hρ⟩
  · rw [← hξ₁, ← Category.assoc, ← Category.assoc, GlobalTheory.SpreadTrait.spMap_comp', GlobalTheory.SpreadTrait.spMap_comp', eα]
  · rw [← hξ₂, ← Category.assoc, ← Category.assoc, GlobalTheory.SpreadTrait.spMap_comp', GlobalTheory.SpreadTrait.spMap_comp', ec]
  · rw [← Category.assoc, hnn, Category.assoc, eβ₁]
  · rw [← eβ₂, ← Category.assoc m₂, em₂, Category.assoc]

theorem exists_spread₂ : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → IsIntegral B → IsLocallyNoetherian B → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → ∃ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ := by
  intro B H _ _ hH V₁ _ _ _ hV₁ G₁ _ _ hG₁ D₁ A₁ U₁ ξ₁ β₁ hβ₁ V₂ _ _ _ hV₂ G₂ _ _ hG₂ D₂ A₂ U₂ ξ₂ β₂ hβ₂ hBi hBn hsp
  haveI := hBi
  haveI := hBn
  let R : Type := B.presheaf.stalk (ξ₂ (closedPoint V₂))
  let ιB : Sp R ⟶ B := B.fromSpecStalk (ξ₂ (closedPoint V₂))
  let HR := (Over.pullback ιB).obj H
  have hHR : IsSemiAbelian HR := IsSemiAbelian.pullback ιB H hH
  haveI : IsCommMonObj HR := hHR.comm
  have hR := isGrpPullback_pullback H ιB
  let g₁ : R →+* V₁ := (B.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ₁).hom
  let g₂ : R →+* V₂ := (Scheme.stalkClosedPointTo ξ₂).hom
  have hg₂ : IsLocalHom g₂ := Scheme.isLocalHom_stalkClosedPointTo' ξ₂
  have hξ₁ : spMap g₁ ≫ ιB = ξ₁ := by
    have e : spMap g₁ = Spec.map (Scheme.stalkClosedPointTo ξ₁) ≫ Spec.map (B.presheaf.stalkSpecializes hsp) := by
      rw [← Spec.map_comp]; rfl
    rw [e, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hξ₂ : spMap g₂ ≫ ιB = ξ₂ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₂
  obtain ⟨β₁', hβ₁', eβ₁⟩ := GlobalTheory.SpreadTrait.pull_cancel hR (spMap g₁) (hβ₁.congr hξ₁.symm rfl)
  obtain ⟨β₂', hβ₂', eβ₂⟩ := GlobalTheory.SpreadTrait.pull_cancel hR (spMap g₂) (hβ₂.congr hξ₂.symm rfl)
  by_cases hl : IsLocalHom g₁
  · haveI := hl
    let κ₁ := ResidueField V₁
    have hC : IsLocalHom (PowerSeries.C (R := κ₁)) :=
      ⟨fun a ha => by simpa using ha.map (PowerSeries.constantCoeff (R := κ₁))⟩
    let c₁ : V₁ →+* PowerSeries κ₁ := (PowerSeries.C (R := κ₁)).comp (residue V₁)
    have hcl : IsLocalHom c₁ := RingHom.isLocalHom_comp _ _
    let ψ₀ : R →+* PowerSeries κ₁ := c₁.comp g₁
    have hψ : IsLocalHom ψ₀ := RingHom.isLocalHom_comp _ _
    let α := algebraMap (PowerSeries κ₁) (FractionRing (PowerSeries κ₁))
    have hα : Function.Injective α := IsFractionRing.injective _ _
    let b₁ : V₁ →+* FractionRing (PowerSeries κ₁) := α.comp c₁
    have hc0 : ∀ x ∈ maximalIdeal V₁, c₁ x = 0 := fun x hx => by
      simp [c₁, (IsLocalRing.residue_eq_zero_iff x).2 hx]
    have hc : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), c₁ x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hc0
    have hb : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0 := fun x hx => by
      simp [b₁, hc x hx]
    have hm₁ := isGrpPullback_pullback HR (spMap ψ₀)
    obtain ⟨mc, hmc, hmcβ⟩ := GlobalTheory.SpreadTrait.pull_cancel hβ₁' (spMap c₁)
      (hm₁.congr (GlobalTheory.SpreadTrait.spMap_comp' g₁ c₁).symm rfl)
    have hn := isGrpPullback_pullback ((Over.pullback (spMap ψ₀)).obj HR) (spMap α)
    have hn' : IsGrpPullback _ G₁ (spMap b₁) _ := (hn.comp hmc).congr (GlobalTheory.SpreadTrait.spMap_comp' c₁ α) rfl
    have hnn : pullback.fst ((Over.pullback (spMap ψ₀)).obj HR).hom (spMap α) ≫ pullback.fst HR.hom (spMap ψ₀) =
        (pullback.fst ((Over.pullback (spMap ψ₀)).obj HR).hom (spMap α) ≫ mc) ≫ β₁' := by
      rw [Category.assoc, hmcβ]
    exact spread₂_of_trait H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ιB HR _ hR g₁ β₁' eβ₁ hξ₁ g₂ hg₂ β₂' hβ₂' eβ₂ hξ₂
      (PowerSeries κ₁) ψ₀ hψ _ α hα b₁ hb rfl _ _ hn _ hn' hnn
      (GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hc hmc) inferInstance
      (GlobalTheory.TorusPart.pullTorus_gtTorus (U₁.gt 0) hc hb hmc hn' hn rfl rfl)
  · obtain ⟨W, _, _, _, ψ₀, Ω, _, αK, b₁, hψ, hb, eα, hT⟩ := _root_.GlobalTheory.exists_trait_nonlocal_torusExtension R HR hHR V₁ g₁ hl
    haveI := hψ
    let alg := algebraMap W (FractionRing W)
    have hα : Function.Injective (αK.comp alg) :=
      αK.injective.comp (IsFractionRing.injective W (FractionRing W))
    have hm₁ := isGrpPullback_pullback HR (spMap ψ₀)
    have hG₁' : IsSemiAbelian ((Over.pullback (spMap ψ₀)).obj HR) := IsSemiAbelian.pullback _ HR hHR
    obtain ⟨φ₁, hφ₁, -⟩ := GlobalTheory.SpreadTrait.pull_cancel hm₁ (spMap alg)
      ((isGrpPullback_pullback HR (spMap (alg.comp ψ₀))).congr (GlobalTheory.SpreadTrait.spMap_comp' ψ₀ alg).symm rfl)
    have hn' := isGrpPullback_pullback G₁ (spMap b₁)
    obtain ⟨n, hn, hnm⟩ := GlobalTheory.SpreadTrait.pull_cancel hm₁ (spMap (αK.comp alg))
      ((hn'.comp hβ₁').congr ((GlobalTheory.SpreadTrait.spMap_comp' g₁ b₁).trans ((congrArg spMap eα.symm).trans
        (GlobalTheory.SpreadTrait.spMap_comp' ψ₀ (αK.comp alg)).symm)) rfl)
    have hb' : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hb
    obtain ⟨j, hj, ej⟩ := _root_.GlobalTheory.TorusPart.extend_torus_hom_dvr W ((Over.pullback (spMap ψ₀)).obj HR) hG₁' _ φ₁ hφ₁ hT Ω αK _ n hn _
      (GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb' hn') inferInstance
    exact spread₂_of_trait H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ιB HR _ hR g₁ β₁' eβ₁ hξ₁ g₂ hg₂ β₂' hβ₂' eβ₂ hξ₂
      W ψ₀ hψ Ω (αK.comp alg) hα b₁ hb' eα _ n hn _ hn' hnm j hj ej

end GlobalTheory.Poinc.Sep.Spz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalBundlePrincipalPolarisatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenTranslPkg

open GlobalTheory.RigidTranslate GlobalTheory.PolTranslate GlobalTheory.GenTransl

variable {R : Type} [CommRing R] [IsDomain R]

def genPoint (G : Over (Sp R)) (a : Over.mk (jK R) ⟶ G) :
    𝟙_ (Over (Sp (FractionRing R))) ⟶ (Over.pullback (jK R)).obj G :=
  Over.homMk (pullback.lift a.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w a)) (pullback.lift_snd _ _ _)

theorem genPoint_fst (G : Over (Sp R)) (a : Over.mk (jK R) ⟶ G) :
    (genPoint G a).left ≫ pullback.fst G.hom (jK R) = a.left :=
  pullback.lift_fst _ _ _

theorem one_left_fst (G : Over (Sp R)) [GrpObj G] (T : Over (Sp (FractionRing R))) :
    (1 : T ⟶ (Over.pullback (jK R)).obj G).left ≫ pullback.fst G.hom (jK R) =
      (1 : Over.mk (T.hom ≫ jK R) ⟶ G).left := by
  have H := isGrpPullback_pullback G (jK R)
  let c : Over.mk (T.hom ≫ jK R) ⟶ G :=
    Over.homMk ((1 : T ⟶ (Over.pullback (jK R)).obj G).left ≫ pullback.fst G.hom (jK R)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      erw [Over.w (1 : T ⟶ (Over.pullback (jK R)).obj G)]
      rfl)
  have hc : c * c = c := by
    apply Over.OverMorphism.ext
    rw [H.2 T 1 1 c c rfl rfl, _root_.mul_one]
    rfl
  have : c = 1 := mul_eq_left.mp hc
  exact congrArg (fun q => q.left) this

theorem genPoint_mul_self (G : Over (Sp R)) [GrpObj G] (a : Over.mk (jK R) ⟶ G) (ha : a * a = 1) :
    genPoint G a * genPoint G a = 1 := by
  have H := isGrpPullback_pullback G (jK R)
  let T := 𝟙_ (Over (Sp (FractionRing R)))
  let U : Over.mk (T.hom ≫ jK R) ⟶ Over.mk (jK R) := Over.homMk (𝟙 _) (by simp [T])
  have hx : (U ≫ a).left = (genPoint G a).left ≫ pullback.fst G.hom (jK R) := by
    rw [genPoint_fst, Over.comp_left]
    exact Category.id_comp _
  have e := H.2 T (genPoint G a) (genPoint G a) (U ≫ a) (U ≫ a) hx hx
  rw [← MonObj.comp_mul, ha, MonObj.comp_one] at e
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [← e, one_left_fst]
  · erw [Over.w (genPoint G a * genPoint G a), Over.w (1 : T ⟶ (Over.pullback (jK R)).obj G)]

theorem transl_genPoint_fst (G : Over (Sp R)) [GrpObj G] (a : Over.mk (jK R) ⟶ G) :
    (transl (genPoint G a)).left ≫ pullback.fst G.hom (jK R) = (genPr G * genPt G a).left := by
  have H := isGrpPullback_pullback G (jK R)
  refine (H.2 _ (𝟙 _) (toUnit _ ≫ genPoint G a) (genPr G) (genPt G a) ?_ ?_).symm
  · exact (Category.id_comp _).symm
  · show pullback.snd G.hom (jK R) ≫ a.left = _
    rw [Over.comp_left, Category.assoc, genPoint_fst]
    rfl

end GlobalTheory.GenTranslPkg


open GlobalTheory.RigidTranslate GlobalTheory.PolTranslate GlobalTheory.GenTransl GlobalTheory.GenTranslPkg in
theorem GlobalTheory.Mum.exists_transl_pkg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ a : Over.mk (jK R) ⟶ G, a * a = 1 → ∃ (P₁ : GlobalTheory.UU.CP G) (A₁ : PolAV (Sp (FractionRing R))) (gen₁ : (Over.pullback (jK R)).obj G ≅ A₁.A), IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G.hom (jK R))) ∧ LBIso (abelian₂ G P₁.L.L) (abelian₂ G P.L.L) ∧ GlobalTheory.GenTransl.IsGenTransl G P.L.L P₁.L.L a := by
  intro R _ _ _ hR G _ _ hG P A gen hgen hL a ha
  obtain ⟨hdvr, -, -⟩ := hR
  haveI := hdvr
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : GeometricallyIntegral G.hom := @GlobalTheory.geometricallyIntegral_of_isSemiAbelian _ G _ hG
  haveI := A.isAb.comm
  haveI := A.isAb.proper
  let b := genPoint G a
  have hb : b * b = 1 := genPoint_mul_self G a ha
  let b' : 𝟙_ _ ⟶ A.A := b ≫ gen.hom
  have hb' : b' * b' = 1 := by
    show (b ≫ gen.hom) * (b ≫ gen.hom) = 1
    rw [← MonObj.mul_comp, hb, MonObj.one_comp]
  let L₁ : LB A.A.left := rigTransl A.L b'
  have hL₁ : L₁.IsLB := DVR.linComb_isLB _ A.isLB _ _
  let A₁ : PolAV (Sp (FractionRing R)) :=
    { A := A.A, isAb := A.isAb, g := A.g, smoothDim := A.smoothDim, L := L₁, isLB := hL₁,
      rigid := rigidified_rigTransl A.isLB, sym := sym_rigTransl hb' A.isLB A.sym,
      ample := relAmple_rigTransl hb' A.isLB A.ample, ktriv := kTriv_rigTransl hb' A.isLB A.ktriv }
  let LG := L₁.pull gen.hom.left
  have hLG : LG.IsLB := pull_isLB hL₁ _
  obtain ⟨L', hL', hLL'⟩ := _root_.GlobalTheory.Mum.lb_extends_over_dvr R G LG hLG
  have hpr : IsProper (pullback.snd G.hom (jK R)) := by
    have e : pullback.snd G.hom (jK R) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    have : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
    rw [e]; infer_instance
  have hsym : Out.Sym ((Over.pullback (jK R)).obj G) (L'.pull (pullback.fst G.hom (jK R))) :=
    _root_.GlobalTheory.sym_of_lbIso_pull_hom _ _ _ gen.hom hgen L₁ _ hL₁ (pull_isLB hL' _) A₁.sym hLL'
  obtain ⟨P₁, hP₁⟩ := _root_.GlobalTheory.CubSymPkg.exists_cp_of_generic_sym R G hG hpr L' hL' hsym
  have hPL := P.L.isLB

  have htr : LBIso LG (P.L.L.pull (genPr G * genPt G a).left) := by
    haveI hU : Unique (Sp (FractionRing R)) := inferInstanceAs (Unique (PrimeSpectrum (FractionRing R)))
    let p0 : (𝟙_ (Over (Sp (FractionRing R)))).left := hU.default
    obtain ⟨i, hi⟩ := exists_chart A.isLB (b'.left p0)
    have h1 : LBIso LG (A.L.pull (gen.hom.left ≫ (transl b').left)) :=
      lbIso_diff_pull A.isLB _ _ _ i fun z => by
        show b'.left ((gen.hom.left ≫ A.A.hom) z) ∈ A.L.U i
        have : (gen.hom.left ≫ A.A.hom) z = p0 := hU.uniq _
        rw [this]
        exact hi
    have e : gen.hom.left ≫ (transl b').left = (transl b).left ≫ gen.hom.left := by
      rw [← Over.comp_left, ← Over.comp_left, comp_transl, transl, MonObj.mul_comp, Category.id_comp,
        Category.assoc]
    rw [e] at h1
    have h2 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull (LBIso.symm hL) (transl b).left
    have h3 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hPL (pullback.fst G.hom (jK R))))
      (transl b).left
    rw [transl_genPoint_fst] at h3
    exact LBIso.trans hLG (pull_isLB A.isLB _) (pull_isLB hPL _) h1
      (LBIso.trans (pull_isLB A.isLB _) (pull_isLB (pull_isLB hPL _) _) (pull_isLB hPL _) (LBIso.symm h2) h3)

  have hext : ExtLam G LG (abelian₂ G P.L.L) := by
    refine ⟨DVR.linComb_isLB _ hPL _ _, fun κ₂ hκ => ?_⟩
    obtain ⟨c, hc⟩ := GlobalTheory.Moduli.cube_of_isLB _ A A.L A.isLB
    have e1 : LBIso (abelian₂ _ LG) ((abelian₂ A.A L₁).pull (gen.hom ⊗ₘ gen.hom).left) :=
      GlobalTheory.ZM.SiegClause.lbIso_lam_pull gen.hom hLG hL₁ (GlobalTheory.PolBaseChange.lbIso_refl hLG)
    have e2 : LBIso (abelian₂ _ (P.L.L.pull (pullback.fst G.hom (jK R))))
        ((abelian₂ A.A A.L).pull (gen.hom ⊗ₘ gen.hom).left) :=
      GlobalTheory.ZM.SiegClause.lbIso_lam_pull gen.hom (pull_isLB hPL _) A.isLB (LBIso.symm hL)
    have e3 := GlobalTheory.ZM.SiegClause.lbIso_pull_pull (lam_rigTransl (t := b') A.isLB c hc) (gen.hom ⊗ₘ gen.hom).left
    rw [Category.comp_id] at e3
    have e4 : LBIso (abelian₂ _ (P.L.L.pull (pullback.fst G.hom (jK R)))) ((abelian₂ G P.L.L).pull κ₂) :=
      GlobalTheory.LamPull.lbIso_lam_pull (isGrpPullback_pullback G (jK R)) hPL (pull_isLB hPL _)
        (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hPL _)) hκ
    have lb : ∀ {S : Scheme.{0}} (H : Over S) [GrpObj H] {M : LB H.left}, M.IsLB → (abelian₂ H M).IsLB :=
      fun _ _ _ h => DVR.linComb_isLB _ h _ _
    exact LBIso.trans (lb _ hLG) (pull_isLB (lb _ hL₁) _) (pull_isLB (lb _ hPL) _) e1
      (LBIso.trans (pull_isLB (lb _ hL₁) _) (pull_isLB (lb _ A.isLB) _) (pull_isLB (lb _ hPL) _) e3
        (LBIso.trans (pull_isLB (lb _ A.isLB) _) (lb _ (pull_isLB hPL _)) (pull_isLB (lb _ hPL) _)
          (LBIso.symm e2) e4))
  refine ⟨P₁, A₁, gen, hgen, ?_, ?_, ?_⟩
  · rw [hP₁]; exact hLL'
  · rw [hP₁]; exact _root_.GlobalTheory.Mum.lbIso_lam_of_extLam R G hG L' LG (abelian₂ G P.L.L) hL' hLG hLL' hext
  · show LBIso _ _
    rw [hP₁]
    exact LBIso.trans (pull_isLB hL' _) hLG (pull_isLB hPL _) (LBIso.symm hLL') htr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverFiniteExtOfSymmetricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformised_cover_finite_ext_of_symmetric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))), (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (C : UCover R₁) (a : C.A.A.left ⟶ A.A.left), FinExt ρ ∧ IsFib ρ A C.A a := by
  first | exact @GlobalTheory.Mum.exists_uCover | exact GlobalTheory.Mum.exists_uCover | (intros; apply GlobalTheory.Mum.exists_uCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesOfCompatibleSystemStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_powerSeries_of_compatible_system : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, Algebra k (B n)] (y : ∀ n, σ → B n) (hy : ∀ n i, IsNilpotent (y n i)) (r : ∀ n, B (n + 1) →ₐ[k] B n), (∀ n i, r n (y (n + 1) i) = y n i) → Presents k y hy → ∀ b : ∀ n, B n, (∀ n, r n (b (n + 1)) = b n) → ∃! f : MvPowerSeries σ k, ∀ n, evA k (y n) (hy n) f = b n := by
  first | exact @GlobalTheory.Katz.existsUnique_evA_eq_of_presents | exact GlobalTheory.Katz.existsUnique_evA_eq_of_presents | (intros; apply GlobalTheory.Katz.existsUnique_evA_eq_of_presents <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesSemilinearPDivGroupHomCha
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

theorem existsUnique_semiHom_ev (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e)
    (s : SemiHom σ G' G) :
    ∃! φ : Fin d → MvPowerSeries (Fin e) k', ∀ n j, c'.ev n (φ j) = s.app n (c.x n j) := by
  have h := fun j : Fin d => existsUnique_evA_eq_of_presents k' (Fin e) G'.A c'.x c'.nil
    (fun n => (G'.res n : G'.A (n + 1) →ₐ[k'] G'.A n)) c'.res c'.presents
    (fun n => s.app n (c.x n j)) (fun n => by
      change G'.res n (s.app (n + 1) (c.x (n + 1) j)) = _
      rw [s.res_app, c.res])
  choose φ hφ hu using h
  refine ⟨φ, fun n j => hφ j n, fun ψ hψ => funext fun j => hu j (ψ j) fun n => hψ n j⟩

end Katz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerUniformisedGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_veryAmpleAlong_unif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), ∃ (m : ℕ) (σ : Fin (m + 1) → H0 U.LG.L 4), VeryAmpleAlong ((Over.pullback (jK R)).obj G).hom (pullback.fst G.hom (jK R)) U.LG.L σ := by
  intro R _ _ I D A G _ _ U
  obtain ⟨m, b, hb⟩ := GlobalTheory.T.exists_veryAmple_fourthPower_polarisedAbelian_field GlobalTheory.lawsAndExpansions.1.1.ample _ A
  obtain ⟨σ, c, H⟩ := _root_.GlobalTheory.Mum.sections_move_integral R I D A G U (k := 4) (by norm_num) b
  have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
  exact ⟨m, σ, GlobalTheory.T.veryAmpleAlongPullback_transport_iso _ A.A.hom U.gen.hom.left (Over.w U.gen.hom) _ U.LG.isLB A.isLB b hb σ c H⟩
end

