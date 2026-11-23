module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.PpicTransl
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ppic
open GlobalTheory.CechPic GlobalTheory.PrimitiveOverValuationRing

theorem isIso_transl {S : Scheme.{0}} {A : Over S} [GrpObj A] (x : 𝟙_ (Over S) ⟶ A) :
    IsIso ((toUnit A ≫ x) * 𝟙 A) := by
  refine ⟨(toUnit A ≫ x)⁻¹ * 𝟙 A, ?_, ?_⟩
  · rw [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc, comp_toUnit,
      inv_mul_cancel_left]
  · rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, mul_inv_cancel_left]

theorem cls_translDiff {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S} (y : T ⟶ A)
    (h : (Out.translDiff A L y).IsLB) :
    cls _ h = GlobalTheory.CechPic.pull ((fst T A ≫ y) * snd T A).left (cls L hL) - GlobalTheory.CechPic.pull (snd T A).left (cls L hL) :=
  cls_pair hL _ _ h

theorem kTriv_transl {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) (x : 𝟙_ (Over S) ⟶ A) (h : LBIso M (L.pull ((toUnit A ≫ x) * 𝟙 A).left)) (hK : Out.KTriv A L) :
    Out.KTriv A M := by
  have hτ : ((toUnit A ≫ x)⁻¹ * 𝟙 A) ≫ ((toUnit A ≫ x) * 𝟙 A) = 𝟙 A := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, mul_inv_cancel_left]
  have hcM : cls M hM = GlobalTheory.CechPic.pull ((toUnit A ≫ x) * 𝟙 A).left (cls L hL) := by
    rw [(cls_eq_iff hM (LB.isLB_pull hL _)).mpr h, cls_pull hL]
  intro R _ t y hy
  apply hK R t y
  intro p
  obtain ⟨V, hpV, c, hc⟩ := hy p
  refine ⟨V, hpV, ?_⟩
  have hLy : (Out.translDiff A L y).IsLB := LB.isLB_linComb hL _ _
  have hMy : (Out.translDiff A M y).IsLB := LB.isLB_linComb hM _ _
  have hc0 := (cls_eq_zero_iff (LB.isLB_pull hMy _)).mpr ⟨c, hc⟩
  rw [cls_pull hMy, cls_translDiff hM, hcM, ← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp,
    ← Over.comp_left, ← Over.comp_left] at hc0
  have hm : (fst (Over.mk t) A ≫ y * snd (Over.mk t) A) ≫ ((toUnit A ≫ x) * 𝟙 A) =
      lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x) * 𝟙 A)) ≫
        (fst (Over.mk t) A ≫ y * snd (Over.mk t) A) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, MonObj.comp_mul,
      ← Category.assoc, lift_fst, lift_snd, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      comp_toUnit, mul_left_comm]
  have hs : snd (Over.mk t) A ≫ ((toUnit A ≫ x) * 𝟙 A) =
      lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x) * 𝟙 A)) ≫ snd (Over.mk t) A :=
    (lift_snd _ _).symm
  rw [hs, hm, Over.comp_left, Over.comp_left, GlobalTheory.CechPic.pull_comp, GlobalTheory.CechPic.pull_comp,
    ← map_sub] at hc0
  have hψφ : lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x)⁻¹ * 𝟙 A)) ≫
      lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x) * 𝟙 A)) = 𝟙 _ := by
    ext
    · rw [Category.assoc, lift_fst, lift_fst, Category.id_comp]
    · rw [Category.assoc, lift_snd, ← Category.assoc, lift_snd, Category.assoc, hτ, Category.comp_id,
        Category.id_comp]
  have hψf : (lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x)⁻¹ * 𝟙 A))).left ≫
      (fst (Over.mk t) A).left = (fst (Over.mk t) A).left := by
    rw [← Over.comp_left, lift_fst]
  have key := pull_eq_zero_of_mem _
    ((Over.Hom.left (fst (Over.mk t) A) ⁻¹ᵁ V).ι ≫
      (lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x)⁻¹ * 𝟙 A))).left)
    (fun z => by
      rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, Category.assoc, hψf, Scheme.Hom.comp_apply,
        ← Scheme.Hom.mem_preimage]
      exact (Scheme.Opens.range_ι _).le (Set.mem_range_self z)) hc0
  have e : ∀ D, GlobalTheory.CechPic.pull
      (lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x)⁻¹ * 𝟙 A))).left
      (GlobalTheory.CechPic.pull (lift (fst (Over.mk t) A) (snd (Over.mk t) A ≫ ((toUnit A ≫ x) * 𝟙 A))).left D) = D := by
    intro D
    rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, hψφ, Over.id_left, GlobalTheory.CechPic.pull_id]
  rw [GlobalTheory.CechPic.pull_comp, e] at key
  exact (cls_eq_zero_iff (LB.isLB_pull hLy _)).mp (by rw [cls_pull hLy, cls_translDiff hL]; exact key)

theorem transl : ∀ (Q : Out.PolAV (Sp ℂ)) (M : LB Q.A.left), M.IsLB → ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A, LBIso M (Q.L.pull ((toUnit Q.A ≫ x) * 𝟙 Q.A).left) → Out.RelAmple Q.A M ∧ Out.KTriv Q.A M := by
  intro Q M hM x h
  have := Q.isAb.comm
  refine ⟨?_, kTriv_transl Q.isLB hM x h Q.ktriv⟩
  obtain ⟨w, hw⟩ := h
  have := isIso_transl x
  have : IsIso ((toUnit Q.A ≫ x) * 𝟙 Q.A).left :=
    inferInstanceAs (IsIso ((Over.forget (Sp ℂ)).map ((toUnit Q.A ≫ x) * 𝟙 Q.A)))
  have sq : IsPullback ((toUnit Q.A ≫ x) * 𝟙 Q.A).left Q.A.hom Q.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
  exact relAmple_pull sq Q.isLB hM ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) Q.ample

end PositivityTheory.HtPt.Ppic
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RiOact
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

namespace PositivityTheory.HtPt.Ri

theorem oact_int : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (P : Out.PolAV (Geo.Tor.Sp O)), Nonempty (P.OAct ℤ) := by
  intro O _ _ _ P
  obtain ⟨R, P₀, φ, hft, -, h₁, h₂⟩ := GlobalTheory.KeyTf.exists_polAV_finiteType_subring O P
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨o, -⟩ := GlobalTheory.exists_oAct_int GlobalTheory.allSixLaws.1.cube _ P₀
  obtain ⟨o', -⟩ := Geo.Tor.polOActPull _ _ _ P₀ P φ h₁ h₂.symm ℤ o
  exact ⟨o'⟩

end PositivityTheory.HtPt.Ri
end

