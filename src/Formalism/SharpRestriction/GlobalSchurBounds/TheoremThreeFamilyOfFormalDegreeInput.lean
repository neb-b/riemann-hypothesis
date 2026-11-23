module

public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0005
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.FamilyPartFiveOfExplicitConstants
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0006
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0016
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0004
public import Formalism.PeriodIntegrals.ExplicitFormulaCounts.WeylForK
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Formalism.LocalToGlobal.GlobalTheory.GL5.LocalEndomorphismContinuous

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.StandardLattice.HarishChandraReduction

open Formalism.BasicNotions Formalism.MainNotions

theorem content_bound_clause (D : D7) (Lv : LevelData D) : adm17 D Lv :=
  column_lemma_of_definite_form D Lv (UnusedSlot33.division_rational_lattice D) (GlobalTheoryTheory.gram0Def D)

theorem levels_pro_g_on_columns (D : D7) (Lv : LevelData D) : Conclusion4p D Lv :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.levels_pro_g D Lv

theorem column_stabilisers_trivial (D : D7) (Lv : LevelData D) : SmallOrderPrimeLogSumBound D Lv :=
  levelDimension_of_admissible D Lv (content_bound_clause D Lv) (levels_pro_g_on_columns D Lv)

theorem rankFormula_of_classNumber (D : D7) (Lv : LevelData D) (hn : ClassNumberFormula₂ D Lv) : Conclusion4f D Lv :=
  level_rank_of_trivial_stabilisers D Lv (column_stabilisers_trivial D Lv) hn

section Fam

variable {eps : ℝ} (Fm : FamP eps)

theorem familyRankFormula_of_classNumber (hn : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev) :
    ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion4f (Fm.D x i) (Fm.ex x hx i).lev :=
  fun x hx i => rankFormula_of_classNumber _ _ (hn x hx i)

theorem chosenProviso_4f (C0 : ℝ) (hC0 : Real.exp 1 ≤ C0)
    (h4f : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion4f (Fm.D x i) (Fm.ex x hx i).lev)
    (hR : RankTiesF Fm) : ChosenProviso Fm C0 := by
  obtain ⟨x2, hR⟩ := rankHypF_of Fm hR
  refine ⟨max (Fm.x1 + 1) x2, fun x hx i => ?_⟩
  have e1 : Fm.x1 < x := by
    have := (le_max_left (Fm.x1 + 1) x2).trans hx
    linarith
  exact LinkB.proviso_mono _ (Real.exp_pos 1) hC0
    (proviso_e (Fm.L x i) (LinkB.rank_formula_of_part_four _ (h4f x e1 i) (hR x ((le_max_right _ _).trans hx) i))
      (StandardLattice.factDuStar_fam Fm x e1 i) (StandardLattice.factDstar_fam Fm x e1 i))

theorem chosenProviso_min (C0 : ℝ) (hC0 : Real.exp 1 ≤ C0)
    (hn : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (hR : RankTiesF Fm) : ChosenProviso Fm C0 :=
  chosenProviso_4f Fm C0 hC0 (familyRankFormula_of_classNumber Fm hn) hR


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem explicitConstants_family_of_volume_eq_mass (h2v : flipTwoThree.fam0 Fm BaseVolumeEqualsMass) (h3 : flipTwoThree.fam0 Fm SigmaDegreeTwoSidedBoundOfGap) : FamilyVandermondeCountExplicit Fm :=
  division_level_prime_family Fm (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.siegel_mass_ratio_family Fm) h2v h3


end Fam

def cTmin (y : ℝ) : ℝ := max 11 (16 + 3 * max 5 (y + 1))


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem tuSize_min {eps : ℝ} (Fm : FamP eps) (hle : cTmin Fm.CYL ≤ Fm.CTu)
    (h2v : flipTwoThree.fam0 Fm BaseVolumeEqualsMass) (h3 : flipTwoThree.fam0 Fm SigmaDegreeTwoSidedBoundOfGap) : TuSize Fm := by
  obtain ⟨x0, hx0⟩ := explicitConstants_family_of_volume_eq_mass Fm h2v h3 (max 5 (Fm.CYL + 1)) (max 5 (Fm.CYL + 1))
  obtain ⟨x1, hx1⟩ := GlobalTheoryTheory.rowsAF_fam Fm (max 5 (Fm.CYL + 1))
  refine GlobalTheoryTheory.tuSize_fam Fm (cTmin Fm.CYL) (max x0 x1) (fun x hx hxx i => ?_) hle
  exact part_five_all_of_explicit _ _ _ _ _ (hx0 x (le_trans (le_max_left _ _) hx) hxx i)
    (fun Δ w hB => hx1 x (le_trans (le_max_right _ _) hx) hxx i Δ w hB) (le_max_left _ _) (le_max_right _ _)


section Fam3

variable {eps : ℝ} (Fm : FamP eps)



end Fam3

section Inputs

variable {eps : ℝ} (Fm : FamP eps)




end Inputs

end Formalism.MainNotions.StandardLattice.HarishChandraReduction

end
