module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0723
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNhdOfStalkBaseChange
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.StalkLBIso

set_option backward.isDefEq.respectTransparency false

theorem lbIso_pull_iff {X Y : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (f : Y ⟶ X) :
    LBIso (A.pull f) (B.pull f) ↔
      CechPic.pull f (CechPic.cls A hA) = CechPic.pull f (CechPic.cls B hB) := by
  rw [← CechPic.cls_pull hA f (pull_isLB hA f), ← CechPic.cls_pull hB f (pull_isLB hB f)]
  exact (CechPic.cls_eq_iff _ _).symm

theorem exists_lbIso_nhd : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h]
    [QuasiSeparated h] (x : S) (A B : LB X), A.IsLB → B.IsLB →
    LBIso (A.pull (pullback.fst h (S.fromSpecStalk x))) (B.pull (pullback.fst h (S.fromSpecStalk x))) →
    ∃ W : S.Opens, x ∈ W ∧ LBIso (A.pull (h ⁻¹ᵁ W).ι) (B.pull (h ⁻¹ᵁ W).ι) := by
  intro S X _ h _ _ x A B hA hB hAB

  have hpb : IsPullback (pullback.fst h (S.fromSpecStalk x)) (pullback.snd h (S.fromSpecStalk x)) h
      (S.fromSpecStalk x) := IsPullback.of_hasPullback _ _
  have hc := (GlobalTheory.StalkLimit.nonempty_isLimit hpb).some
  obtain ⟨V₀⟩ : Nonempty (GlobalTheory.StalkLimit.AffNhd x) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((GlobalTheory.StalkLimit.diagram x h).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd h V₀.1.ι)
  have : QuasiSeparatedSpace ((GlobalTheory.StalkLimit.diagram x h).obj V₀) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd h V₀.1.ι)

  have h0 : LBIso ((A.pull (pullback.fst h V₀.1.ι)).pull ((GlobalTheory.StalkLimit.cone hpb).π.app V₀))
      ((B.pull (pullback.fst h V₀.1.ι)).pull ((GlobalTheory.StalkLimit.cone hpb).π.app V₀)) := by
    rw [lbIso_pull_iff (pull_isLB hA _) (pull_isLB hB _), CechPic.cls_pull hA, CechPic.cls_pull hB,
      ← CechPic.pull_comp, ← CechPic.pull_comp, GlobalTheory.StalkLimit.cone_π_fst, ← lbIso_pull_iff hA hB]
    exact hAB

  obtain ⟨j, f, hj⟩ := GlobalTheory.exists_lbIso_of_isLimit (GlobalTheory.StalkLimit.diagram x h)
    (fun V => (GlobalTheory.StalkLimit.cone hpb).π.app V) (fun f => (GlobalTheory.StalkLimit.cone hpb).w f) hc
    (A.pull (pullback.fst h V₀.1.ι)) (B.pull (pullback.fst h V₀.1.ι)) (pull_isLB hA _) (pull_isLB hB _) h0
  have hj' : CechPic.pull (pullback.fst h j.1.ι) (CechPic.cls A hA) =
      CechPic.pull (pullback.fst h j.1.ι) (CechPic.cls B hB) := by
    rw [lbIso_pull_iff (pull_isLB hA _) (pull_isLB hB _), CechPic.cls_pull hA, CechPic.cls_pull hB,
      ← CechPic.pull_comp, ← CechPic.pull_comp, GlobalTheory.StalkLimit.diagram_map_fst] at hj
    exact hj

  refine ⟨j.1, j.2.1, ?_⟩
  rw [lbIso_pull_iff hA hB, ← pullbackRestrictIsoRestrict_inv_fst, CechPic.pull_comp, CechPic.pull_comp, hj']

end GlobalTheory.StalkLBIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleNhdOfStalkBaseChange
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.StalkLB

set_option backward.isDefEq.respectTransparency false

theorem exists_lb_nhd : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h]
    [QuasiSeparated h] (x : S) (N : LB (pullback h (S.fromSpecStalk x))), N.IsLB →
    ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(h ⁻¹ᵁ W), N'.IsLB ∧
      ∀ a : pullback h (S.fromSpecStalk x) ⟶ ↑(h ⁻¹ᵁ W),
        a ≫ (h ⁻¹ᵁ W).ι = pullback.fst h (S.fromSpecStalk x) → LBIso (N'.pull a) N := by
  intro S X _ h _ _ x N hN
  have hpb := IsPullback.of_hasPullback h (S.fromSpecStalk x)
  have hlim : IsLimit (GlobalTheory.schemeConeOfFamily (GlobalTheory.StalkLimit.diagram x h)
      (fun V => (GlobalTheory.StalkLimit.cone hpb).π.app V) (fun f => (GlobalTheory.StalkLimit.cone hpb).w f)) :=
    (GlobalTheory.StalkLimit.nonempty_isLimit hpb).some
  have hcpt : ∀ V : GlobalTheory.StalkLimit.AffNhd x, CompactSpace ((GlobalTheory.StalkLimit.diagram x h).obj V) := by
    intro V
    haveI : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd h V.1.ι)
  have hqs : ∀ V : GlobalTheory.StalkLimit.AffNhd x,
      QuasiSeparatedSpace ((GlobalTheory.StalkLimit.diagram x h).obj V) := by
    intro V
    haveI : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd h V.1.ι)
  obtain ⟨j, M, hM, -, hall⟩ := GlobalTheory.LBLimit.exists_lb_of_isLimit (GlobalTheory.StalkLimit.diagram x h)
    (fun V => (GlobalTheory.StalkLimit.cone hpb).π.app V) (fun f => (GlobalTheory.StalkLimit.cone hpb).w f) hlim N hN
  refine ⟨j.1, j.2.1, M.pull (pullbackRestrictIsoRestrict h j.1).inv, LB.isLB_pull hM _, fun a ha => ?_⟩
  refine LBIso.symm (hall _ a (pullbackRestrictIsoRestrict h j.1).inv ?_)
  have hfst : (GlobalTheory.StalkLimit.cone hpb).π.app j ≫ pullback.fst h j.1.ι =
      pullback.fst h (S.fromSpecStalk x) := GlobalTheory.StalkLimit.cone_π_fst hpb j
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackRestrictIsoRestrict_inv_fst, ha, hfst]
  · rw [← cancel_mono j.1.ι]
    simp only [Category.assoc]
    rw [← pullback.condition, pullbackRestrictIsoRestrict_inv_fst_assoc, reassoc_of% ha,
      reassoc_of% hfst]

end GlobalTheory.StalkLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulOfValLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.UT
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaDvr

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
  {V : Type} [CommRing V] [IsDomain V]

theorem torsion_points (yK : S.R →+* FractionRing V) {A : PolAV (Sp (FractionRing V))} {φ : A.A.left ⟶ ρ.P.A.left}
    (cart : IsGrpPullback A.A ρ.P.A (spMap yK) φ) :
    ∃ x : S.Gam → (TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A),
      (∀ a, (x a).left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫
        (ρ.pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧ Function.Injective x ∧
      ∀ z : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a := by
  have e : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) :=
    (Spec.map_comp (CommRingCat.ofHom yK) (CommRingCat.ofHom (algebraMap _ _))).symm
  obtain ⟨x, h₁, h₂⟩ := labelled_torsion_pull cart (TFK (R := V) (AlgebraicClosure (FractionRing V)))
    (E := baseOver (Sp S.R))
    (Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK :) (by simp)) ρ.pt (S.r * S.N)
    ρ.pt_add (fun a => (ρ.fr_tors a).1) (fun z hz => ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ z hz)
  exact ⟨x, fun a => (h₁ a).trans (by rw [← e]; rfl), h₂⟩

theorem frames (yK : S.R →+* FractionRing V) {A : PolAV (Sp (FractionRing V))} {φ : A.A.left ⟶ ρ.P.A.left}
    (cart : IsGrpPullback A.A ρ.P.A (spMap yK) φ) (lb : LBIso A.L (ρ.P.L.pull φ))
    (x : S.Gam → (TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A))
    (hx : ∀ a, (x a).left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫
      (ρ.pt a).left) :
    ∃ (rig : LB.Gen (A.L.pull (eSec A.A)))
      (e : ∀ a, LB.Gen (LB.LinComb A.L (Y := (TFK (R := V) (AlgebraicClosure (FractionRing V))).left) (K := Fin 1)
        (fun _ => (x a).left) (fun _ => 1))),
      rig.IsGen ∧ (∀ a, IsTorsFrame A rig (S.r * S.N) (x a) (e a)) ∧
      ∀ (k : ℕ) (σ : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))),
        ∃ t : SecA A (AlgebraicClosure (FractionRing V)) k, ∀ (a : S.Gam) (c : S.R),
          IsValueAt ρ.P.A ρ.P.L (k : ℤ) σ (ρ.pt a) (powFrame ρ.P.A ρ.P.L (ρ.pt a) (ρ.fr a) (k : ℤ)) (fn c) →
          ∀ z J, Good A.L z J → sA t (ptSecT A.A (x a)).left z J =
            @id ((TFK (R := V) (AlgebraicClosure (FractionRing V))).left.presheaf.stalk z)
              (cst (R := V) (AlgebraicClosure (FractionRing V)) z
                ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK c)) *
            (val (powFrame A.A A.L (x a) (e a) (k : ℤ)) (𝟙 _) z J).val := by
  have hh : (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) :
      (TFK (R := V) (AlgebraicClosure (FractionRing V))).left ⟶ (baseOver (Sp S.R)).left) ≫ (baseOver (Sp S.R)).hom =
      (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK :=
    (Category.comp_id _).trans (Spec.map_comp (CommRingCat.ofHom yK) (CommRingCat.ofHom (algebraMap _ _)))
  obtain ⟨rig, e, h₁, h₂, h₃⟩ := GlobalTheory.FrameMove.exists_move (T := baseOver (Sp S.R))
    (T' := TFK (R := V) (AlgebraicClosure (FractionRing V))) cart lb hh ρ.rig_gen hx ρ.fr_tors
  refine ⟨rig, e, h₁, h₂, fun k σ => ?_⟩
  obtain ⟨t, ht⟩ := h₃ k σ
  exact ⟨t, fun a c hc z J hJ => (ht a _ hc z J hJ).trans (congrArg (· * _) (GlobalTheory.FrameMove.gs_spMap _ z c))⟩

end GlobalTheory.ThetaDvr
end

namespace GlobalTheory.ThetaDvr

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_mul_of_val_le {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {x y : FractionRing V} (hy : y ≠ 0)
    (h : v (algebraMap (FractionRing V) F y) ≤ v (algebraMap (FractionRing V) F x)) :
    ∃ w : V, x = algebraMap V (FractionRing V) w * y ∧
      (v (algebraMap (FractionRing V) F y) < v (algebraMap (FractionRing V) F x) → w ∈ IsLocalRing.maximalIdeal V) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero, zero_mul], fun _ => zero_mem _⟩
  obtain ⟨n, u, hu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC.exists_hasVal hϖ x hx
  obtain ⟨m, u', hu'⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC.exists_hasVal hϖ y hy
  have hn := hv x n ⟨u, hu⟩
  have hm := hv y m ⟨u', hu'⟩
  rw [hn, hm, WithTop.coe_le_coe, Int.cast_le] at h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = m + k := ⟨(n - m).toNat, by omega⟩
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  have hu'1 : algebraMap V (FractionRing V) (↑u'⁻¹ : V) * algebraMap V (FractionRing V) (u' : V) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨ϖ ^ k * u * ↑u'⁻¹, ?_, fun hlt => ?_⟩
  · rw [hu, hu', hk, zpow_add₀ hϖ0, zpow_natCast, map_mul, map_mul, map_pow]
    linear_combination (-(algebraMap V (FractionRing V) ϖ ^ m * algebraMap V (FractionRing V) ϖ ^ k *
      algebraMap V (FractionRing V) (u : V))) * hu'1
  · rw [hn, hm, WithTop.coe_lt_coe, Int.cast_lt] at hlt
    have hk0 : k ≠ 0 := by omega
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ?_ k (Nat.pos_of_ne_zero hk0)))
    exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit

end GlobalTheory.ThetaDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldContainingCoefficientData
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder IntermediateField

namespace GlobalTheory.ColNorms.ExField

theorem exists_field_holdsData : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (cD : D.what₂.Tau → ℂ) (K : Type) [Field K] [NumberField K] (σ₀ : K →+* ℂ) (R : Ranks), StandardLatticesGL3.Crv D cc dl → IsDgen D cD → (∀ i < R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ TaylorLogMetric.CoefIn D (B.thZero (R.N i) (R.N (i + 1))) M) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ThetaFieldData B cD σ₀ R M := by
  intro D cc dl B cD K _ _ σ₀ R hC hD hM
  obtain ⟨M₁, hM₁, hE, hc⟩ := hD
  obtain ⟨⟨-, h2, h3⟩, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D
    (GlobalTheory.InducedType.induced_type D).1).2 cc dl hC
  choose Mi hMi hcoef using fun i : Fin R.m => hM i.1 i.2
  let M₀ : IntermediateField ℚ ℂ := σ₀.toRatAlgHom.fieldRange
  haveI f0 : FiniteDimensional ℚ M₀ :=
    (AlgEquiv.ofInjectiveField σ₀.toRatAlgHom).toLinearEquiv.finiteDimensional
  let M₂ : IntermediateField ℚ ℂ := ℚ⟮TaylorLogMetric.g2 (TaylorLogMetric.tor0 D cc dl).abelian₂⟯
  let M₃ : IntermediateField ℚ ℂ := ℚ⟮TaylorLogMetric.g3 (TaylorLogMetric.tor0 D cc dl).abelian₂⟯
  haveI f2 : FiniteDimensional ℚ M₂ :=
    IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.mp h2).isIntegral
  haveI f3 : FiniteDimensional ℚ M₃ :=
    IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.mp h3).isIntegral
  haveI f1 : FiniteDimensional ℚ M₁ := inferInstance
  haveI f4 : FiniteDimensional ℚ (⨆ i, Mi i : IntermediateField ℚ ℂ) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  let M : IntermediateField ℚ ℂ := (M₀ ⊔ M₁) ⊔ (M₂ ⊔ M₃) ⊔ ⨆ i, Mi i
  have l0 : M₀ ≤ M := le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  have l1 : M₁ ≤ M := le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have l2 : M₂ ≤ M := le_sup_of_le_left (le_sup_of_le_right le_sup_left)
  have l3 : M₃ ≤ M := le_sup_of_le_left (le_sup_of_le_right le_sup_right)
  have l4 : ∀ i, Mi i ≤ M := fun i => le_sup_of_le_right (le_iSup Mi i)
  refine ⟨M, inferInstance, fun k => l0 ⟨k, rfl⟩, ⟨fun τ x => l1 (hE τ x),
    l2 (IntermediateField.mem_adjoin_simple_self _ _), l3 (IntermediateField.mem_adjoin_simple_self _ _)⟩,
    fun τ => ?_, fun i hi α => l4 ⟨i, hi⟩ (hcoef ⟨i, hi⟩ α)⟩
  obtain ⟨s, hs, -⟩ := hc τ
  exact hs ▸ l1 s.2

end GlobalTheory.ColNorms.ExField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsTranslationFamilyChartsThickeningsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_points_translationFamilyCharts_thickenings : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (ρ : ∀ k, Hol (K.W (ka k)) →+* R ⊗[ℂ] Hol (K₀.W k)), (∀ k f, ρ k (K.cst (ka k) f) = θ f ⊗ₜ[ℂ] 1) → (∀ k a h, ρ k (dw (W := K.W (ka k)) a h) = LinearMap.lTensor R (dw (W := K₀.W k) a).toLinearMap (ρ k h)) → (∀ l k' k (h : K₀.le l k' k), Close (M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k'))) ((ρ k').comp (Charts.sh (hka h))) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h)).toRingHom.comp (ρ k))) → ∀ (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)), (∀ k h, ρ k h - 1 ⊗ₜ[ℂ] res k h ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k))) → ∃ ρ' : ∀ S : K₀.DObj (et : Hol F₀.V →+* R) M, Hol (K.W (ka S.T.k)) →+* S.T.C, (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) ∧ (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) ∧ ∀ (S S' : K₀.DObj (et : Hol F₀.V →+* R) M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S)) := by
  intro I _ g Λ _ F F₀ K K₀ R _ _ et M θ ka hka ρ hc hd hs res hr
  choose ψ hψ using _root_.GlobalTheory.AnPer.exists_tensorLift_of_DObj K₀ et M
  have h1 : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M) (d : R), ψ S (d ⊗ₜ[ℂ] 1) = algebraMap R S.T.C d :=
    fun S d ↦ (hψ S d 1).trans (by rw [S.T.ρ.map_one, _root_.mul_one])
  have h2 : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M) (h : Hol (K₀.W S.T.k)), ψ S (1 ⊗ₜ[ℂ] h) = S.T.ρ h :=
    fun S h ↦ (hψ S 1 h).trans (by rw [(algebraMap R S.T.C).map_one, _root_.one_mul])
  have hJ : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M),
      ∀ c ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)), ψ S c ∈ S.T.J := by
    intro S c hc
    have : M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)) ≤ S.T.J.comap (ψ S) := by
      refine Ideal.map_le_iff_le_comap.2 fun d hd ↦ ?_
      change ψ S (d ⊗ₜ[ℂ] 1) ∈ S.T.J
      rw [h1]
      exact S.mem d hd
    exact this hc
  refine ⟨fun S ↦ (ψ S).comp (ρ S.T.k), fun S f ↦ ?_, fun S h ↦ ?_, fun S S' f ↦ ?_⟩
  · exact (congrArg (ψ S) (hc _ f)).trans (h1 S _)
  · have := hJ S _ (hr S.T.k h)
    rw [(ψ S).map_sub, h2] at this
    exact this
  · have c1 := (hs _ _ _ (Charts.Hom.le f.1)).map (ψ S') (hJ S')
    have c2 := GlobalTheory.CloseTen.close_tensor S'.T.J (ρ S.T.k) (hd S.T.k)
      ((ψ S').comp (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA (Charts.Hom.le f.1))).toRingHom)
      ((f.1.φ : S.T.C →+* S'.T.C).comp (ψ S))
      (fun d ↦ by
        have e : Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA (Charts.Hom.le f.1)) (d ⊗ₜ[ℂ] 1) = d ⊗ₜ[ℂ] 1 :=
          (Algebra.TensorProduct.map_tmul _ _ _ _).trans
            (congrArg (fun x ↦ d ⊗ₜ[ℂ] x) (Charts.shA (Charts.Hom.le f.1)).map_one)
        exact (congrArg (ψ S') e).trans ((h1 S' d).trans ((f.2 d).symm.trans (congrArg f.1.φ (h1 S d).symm))))
      (by
        have e1 : ((ψ S').comp (Algebra.TensorProduct.map (AlgHom.id ℂ R)
            (Charts.shA (Charts.Hom.le f.1))).toRingHom).comp
            (Algebra.TensorProduct.includeRight : Hol (K₀.W S.T.k) →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)).toRingHom =
            S'.T.ρ.comp (Charts.sh (Charts.Hom.le f.1)) :=
          RingHom.ext fun h ↦ (congrArg (ψ S') (Algebra.TensorProduct.map_tmul (AlgHom.id ℂ R)
            (Charts.shA (Charts.Hom.le f.1)) 1 h)).trans (h2 S' _)
        have e2 : ((f.1.φ : S.T.C →+* S'.T.C).comp (ψ S)).comp
            (Algebra.TensorProduct.includeRight : Hol (K₀.W S.T.k) →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)).toRingHom =
            (f.1.φ : S.T.C →+* S'.T.C).comp S.T.ρ :=
          RingHom.ext fun h ↦ congrArg f.1.φ (h2 S h)
        rw [e1, e2]
        exact f.1.close)
    exact Relation.ReflTransGen.trans c1 c2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetReductionAdelicDetNormBandStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelSet_reduction_adelicDetNormBand : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∃ Ω : Set (GA E a), IsCompact Ω ∧ Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)) ∧ ∃ t c₁ c₂ : ℝ, 0 < t ∧ 0 < c₁ ∧ ∀ g ∈ band E a, ∃ γ : GL (Fin a) E, ∃ b ∈ Ω, ∃ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧ c₁ ≤ ∏ i, r i ∧ ∏ i, r i ≤ c₂ ∧ ∃ k ∈ (maxCompact : Subgroup (GA E a)), ratGL E a γ * g = b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k := by
  first | exact @GlobalTheory.HCF.exists_siegel_band | exact GlobalTheory.HCF.exists_siegel_band | (intros; apply GlobalTheory.HCF.exists_siegel_band <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanMaximalIdealMapOfFlatRegular
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
open IsLocalRing

theorem maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre :
    ∀ (O' O : Type) [CommRing O'] [IsRegularLocalRing O'] [CommRing O] [IsLocalRing O]
      [IsNoetherianRing O] (σ : O' →+* O), IsLocalHom σ → σ.Flat →
      IsArtinianRing (O ⧸ (IsLocalRing.maximalIdeal O').map σ) → ∀ g : ℕ, ringKrullDim O = g →
      ∃ f : Fin g → O, Ideal.span (Set.range f) = (IsLocalRing.maximalIdeal O').map σ := by
  intro O' O _ _ _ _ _ σ hloc hflat hart g hg
  letI := σ.toAlgebra
  haveI : Module.Flat O' O := hflat
  haveI : Algebra.HasGoingDown O' O := Algebra.HasGoingDown.of_flat
  haveI : IsLocalHom (algebraMap O' O) := hloc
  haveI : IsLocalHom σ := hloc
  set I : Ideal O := (maximalIdeal O').map σ with hI
  have hIle : I ≤ maximalIdeal O := IsLocalRing.map_maximalIdeal_le _
  haveI : Nontrivial (O ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal O).ne_top hIle)
  haveI : IsLocalRing (O ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal O).map (Ideal.Quotient.mk I) = maximalIdeal (O ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hF : (maximalIdeal (O ⧸ I)).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    refine ⟨⟨inferInstance, bot_le⟩, fun q ⟨hq, _⟩ hle => ?_⟩
    exact ((IsArtinianRing.isMaximal_of_isPrime q).eq_of_le (maximalIdeal.isMaximal _).ne_top
      hle).ge
  have H := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal O') (maximalIdeal O)
  have hIalg : (maximalIdeal O').map (algebraMap O' O) = I := rfl
  rw [hIalg, hmap, hF, add_zero] at H
  have hdim : ((maximalIdeal O').spanFinrank : WithBot ℕ∞) = g := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal, ← maximalIdeal_height_eq_ringKrullDim, ← H,
      maximalIdeal_height_eq_ringKrullDim, hg]
  have hg' : (maximalIdeal O').spanFinrank = g := by exact_mod_cast hdim
  have hfg : (maximalIdeal O').FG := IsNoetherian.noetherian _
  obtain ⟨t, htcard, htspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  rw [hg'] at htcard
  let u : Fin g → O' := fun i => (t.equivFin.symm (Fin.cast htcard.symm i) : O')
  have hu : Set.range u = (t : Set O') := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact (t.equivFin.symm _).2
    · intro hx; exact ⟨Fin.cast htcard (t.equivFin ⟨x, hx⟩), by simp [u]⟩
  refine ⟨fun i => σ (u i), ?_⟩
  rw [hI, ← htspan, Ideal.map_span, ← hu, ← Set.range_comp]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqAddPrimeOddModThreeValuationOne
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_sq_add_prime_odd_mod_three_unit :
    ∀ (p : ℕ) (V : ValuationSubring ℂ), p.Prime → 3 < p →
      ∃ a N : ℕ, N = a ^ 2 + p ∧ Odd N ∧ N % 3 = 2 ∧ V.valuation (N : ℂ) = 1 := by
  intro p V hp h3
  have h2 : p % 2 = 1 := by
    by_contra h
    rcases hp.eq_one_or_self_of_dvd 2 (by omega) with h' | h' <;> omega
  have h3' : p % 3 ≠ 0 := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 3 (by omega) with h' | h' <;> omega
  rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h1 | h1
  · have hcop : Nat.Coprime (2 ^ 2 + p) (4 ^ 2 + p) := by
      have hg1 := Nat.gcd_dvd_left (2 ^ 2 + p) (4 ^ 2 + p)
      have hg2 := Nat.gcd_dvd_right (2 ^ 2 + p) (4 ^ 2 + p)
      have h12 : Nat.gcd (2 ^ 2 + p) (4 ^ 2 + p) ∣ 12 := by
        have := Nat.dvd_sub hg2 hg1
        have e : 4 ^ 2 + p - (2 ^ 2 + p) = 12 := by omega
        rwa [e] at this
      have hle := Nat.le_of_dvd (by norm_num) h12
      unfold Nat.Coprime
      generalize Nat.gcd (2 ^ 2 + p) (4 ^ 2 + p) = g at hg1 hg2 h12 hle
      norm_num at hg1 hg2
      interval_cases g <;> omega
    rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with hv | hv
    · exact ⟨2, 2 ^ 2 + p, rfl, by rw [Nat.odd_iff]; omega, by omega, by exact_mod_cast hv⟩
    · exact ⟨4, 4 ^ 2 + p, rfl, by rw [Nat.odd_iff]; omega, by omega, by exact_mod_cast hv⟩
  · have hcop : Nat.Coprime (0 ^ 2 + p) (6 ^ 2 + p) := by
      have hg1 := Nat.gcd_dvd_left (0 ^ 2 + p) (6 ^ 2 + p)
      have hg2 := Nat.gcd_dvd_right (0 ^ 2 + p) (6 ^ 2 + p)
      have h36 : Nat.gcd (0 ^ 2 + p) (6 ^ 2 + p) ∣ 36 := by
        have := Nat.dvd_sub hg2 hg1
        have e : 6 ^ 2 + p - (0 ^ 2 + p) = 36 := by omega
        rwa [e] at this
      have hle := Nat.le_of_dvd (by norm_num) h36
      unfold Nat.Coprime
      generalize Nat.gcd (0 ^ 2 + p) (6 ^ 2 + p) = g at hg1 hg2 h36 hle
      norm_num at hg1 hg2
      interval_cases g <;> omega
    rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with hv | hv
    · exact ⟨0, 0 ^ 2 + p, rfl, by rw [Nat.odd_iff]; omega, by omega, by exact_mod_cast hv⟩
    · exact ⟨6, 6 ^ 2 + p, rfl, by rw [Nat.odd_iff]; omega, by omega, by exact_mod_cast hv⟩

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIdeleModuleExistsRat
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.CMVal.ModFRat

theorem modF_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := by
  intro E _ _ y
  refine ⟨∏ᶠ v : HeightOneSpectrum (𝓞 E), ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))), ?_⟩
  have h := MonoidHom.map_finprod_of_injective ((Rat.castHom ℝ : ℚ →+* ℝ) : ℚ →* ℝ) Rat.cast_injective
    (fun v : HeightOneSpectrum (𝓞 E) => ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))))
  simp only [MonoidHom.coe_coe, Rat.coe_castHom, Rat.cast_zpow, Rat.cast_natCast] at h
  rw [h]
  rfl

end GlobalTheory.CMVal.ModFRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyBoundedSupOfEquicontinuousInvariantTailsStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totallyBounded_sup_of_equicontinuous_invariant_tails : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S B : Set G) (Φ : Set (G → ℂ)), (∀ φ ∈ Φ, ∀ s ∈ S, ∀ g, φ (s * g) = φ g) → (∀ φ ∈ Φ, ∀ g ∈ B, ‖φ g‖ ≤ 1) → (∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (1 : G), ∀ φ ∈ Φ, ∀ g ∈ B, ∀ u ∈ U, g * u ∈ B → ‖φ (g * u) - φ g‖ ≤ ε) → (∀ ε : ℝ, 0 < ε → ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g ∈ B, (∃ s ∈ S, s * g ∈ C) ∨ ∀ φ ∈ Φ, ‖φ g‖ ≤ ε) → ∀ ε : ℝ, 0 < ε → ∃ F : Finset (G → ℂ), ∀ φ ∈ Φ, ∃ ψ ∈ F, ∀ g ∈ B, ‖φ g - ψ g‖ ≤ ε := by
  first | exact @GlobalTheory.totallyBounded_sup_of_equicontinuous_tails | exact GlobalTheory.totallyBounded_sup_of_equicontinuous_tails | (intros; apply GlobalTheory.totallyBounded_sup_of_equicontinuous_tails <;> assumption)
end

