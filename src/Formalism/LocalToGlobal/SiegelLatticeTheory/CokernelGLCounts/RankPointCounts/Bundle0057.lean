module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0052
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXFinsetSum
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0053
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GflagSwap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Transfer
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.NilpotentMeasureRecursion
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntPFmat
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs PI.NRCW IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable (D : D7)

theorem intP_fmat (P : HeightOneSpectrum (𝓞 D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E}
    (G : LFlag (D.sp.Y 0) D.R.rS T) (m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hm : m ∈ NLam Λ G)
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (hz : G.fl.z ∈ Λ)
    (c b : Fin (D.R.rS + 1)) : IntP P (fmat D G m c b) := by
  have hfLP : ∀ c, frame G c ∈ LP P Λ := by
    intro c
    induction c using Fin.lastCases with
    | last => rw [frame_last]; exact mem_localization_of_mem₃ P hz
    | cast i => rw [frame_castSucc]; exact e_mem_LP P hC hP i
  have hmLP : m (frame G b) - frame G b ∈ LP P Λ :=
    sub_mem_localization P (LP_map P (m : (VS D).V →ₗ[D.host.E] (VS D).V) (fun v hv => nlam_mem hm hv) (hfLP b)) (hfLP b)
  have h01 : ∀ (t : Prop) [Decidable t], IntP P (if t then (1 : D.host.E) else 0) := by
    intro t _
    split_ifs
    · simpa using intP_O P 1
    · simpa using intP_O P 0
  unfold fmat
  apply intP_add P (h01 _)
  split_ifs with h
  · exact coef_intP P hC hP hmLP (frame_d_mem G hm b) _
  · simpa using intP_O P 0

theorem frame_nm (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (G₁ : LFlag (D.sp.Y 0) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (b : Fin (D.R.rS + 1)) :
    n (m (frame G₁ b)) = ∑ d, (fmat D G n * fmat D G₁ m) d b • frame G d +
      n (∑ c, fmat D G₁ m c b • (frame G₁ c - frame G c)) := by
  rw [(stepExp D Λ G₁ m hm).2 b]
  have e1 : ∑ c, fmat D G₁ m c b • frame G₁ c =
      ∑ c, fmat D G₁ m c b • frame G c + ∑ c, fmat D G₁ m c b • (frame G₁ c - frame G c) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← smul_add, add_sub_cancel]
  rw [e1, map_add (f := _)]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, (stepExp D Λ G n hn).2, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ => ?_))
  rw [mul_comm]

theorem cong_at (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (G₁ G₂ : LFlag (D.sp.Y 0) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (hfr : ∀ a, frame G₂ a = n (m (frame G₁ a))) (hC : IsFixedConv Λ (gS D) G)
    (hC₁ : IsFixedConv Λ (gS D) G₁) (hA1 : AdmWit Λ (gS D) G G₁ 1) (hA2 : AdmWit Λ (gS D) G G₂ 1)
    (hz₁ : G₁.fl.z ∈ Λ) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (hg : ((gS D : ℕ) : D.host.E) ≠ 0) (d : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    IntP P ((fmat D G n * fmat D G₁ m - 1) d.castSucc b / (gS D : D.host.E)) := by
  have hw : ∀ c, frame G₁ c - frame G c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hA1.2.2 c P hP
    rw [frameAct_one] at this
    exact this
  have hw2 : ∀ c, frame G₂ c - frame G c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hA2.2.2 c P hP
    rw [frameAct_one] at this
    exact this
  have hNU := (stepExp D Λ G n hn).1
  have hMU := (stepExp D Λ G₁ m hm).1

  set Y := ∑ d', (fmat D G n * fmat D G₁ m - 1) d' b • frame G d' with hYdef
  have hYeq : Y = (frame G₂ b - frame G b) - n (∑ c, fmat D G₁ m c b • (frame G₁ c - frame G c)) := by
    rw [hfr b, frame_nm D Λ G G₁ n m hn hm b, hYdef]
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]
    have e1 : ∑ d', (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) d' b • frame G d' = frame G b := by
      simp [Matrix.one_apply]
    rw [e1]
    abel
  have hYLg : Y ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    rw [hYeq]
    refine sub_mem (hw2 b) ?_
    exact LP_map P (n : (VS D).V →ₗ[D.host.E] (VS D).V) (nlam_gLam hn _)
      (LP_sum P _ _ fun c _ => smul_mem_localization P (intP_fmat D P Λ G₁ m hm hC₁ hP hz₁ c b) (hw c))

  have hlast : (fmat D G n * fmat D G₁ m - 1) (Fin.last D.R.rS) b = 0 := by
    rw [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_eq_single (Fin.last D.R.rS)]
    · rw [(hNU _ _).2 rfl, one_mul, Matrix.one_apply]
      by_cases hb : Fin.last D.R.rS = b
      · rw [(hMU _ _).2 hb, if_pos hb, sub_self]
      · have hlt : b < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last b) (Ne.symm hb)
        rw [(hMU _ _).1 hlt, if_neg hb, sub_self]
    · intro c _ hc
      have hlt : c < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last c) hc
      rw [(hNU _ _).1 hlt, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hYsum : Y = ∑ d' : Fin D.R.rS, (fmat D G n * fmat D G₁ m - 1) d'.castSucc b • G.fl.e d' := by
    rw [hYdef, Fin.sum_univ_castSucc, hlast, zero_smul, add_zero]
    refine Finset.sum_congr rfl (fun d' _ => ?_)
    rw [frame_castSucc]
  have hYX : Y ∈ G.fl.X := by
    rw [hYsum]
    exact Submodule.sum_mem _ fun d' _ => Submodule.smul_mem _ _ (e_mem_X _ d')
  have hcoef := coef_intP_g P hC hP hg hYLg hYX d
  have hYd : G.fl.coefX Y d = (fmat D G n * fmat D G₁ m - 1) d.castSucc b := by
    rw [hYsum, coefX_finset_sum _ _ _ (fun d' => Submodule.smul_mem _ _ (e_mem_X _ d'))]
    simp only [coefX_smul_e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hYd] at hcoef
  exact hcoef

end Cong

end Formalism.L2.SG.Pf.FibQ
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LamOfTermScal
section
noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SumFr

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem lam_of_termScal {γ γ' : TermDef.Term D u u' F0 what₂} (h : Corank.TermScal D γ γ') : γ'.lam = γ.lam := by
  obtain ⟨p, h1, h2, -⟩ := h
  rw [← h1, ← h2]
  rfl

theorem sumFr_of (hD : TupFun M δ u u' F0 what₂) (hC : RepAtTup M δ u u' F0 what₂) (hB : OrbZT M δ u u' F0 what₂)
    (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hP : PrimeHyp D u (Tu D u'))
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hR : IsRowReps D F0 what₂)
    (hfin : ∀ Λ ∈ what₂, ∀ Z : PairVal.MatR D, CntLocal.cntE (CntLocal.Tn u') F0 Λ Z ≠ ⊤) :
    SumFr M δ u u' F0 what₂ := by
  intro γ w _ w' hG' _ Z hZ
  have hpre : Pre M δ u u' F0 what₂ := ⟨hA, hT, hP, hN, hR, eligRel_holds⟩
  have hclsFin : (clsSet F0 u' γ.lam Z).Finite :=
    Set.encard_ne_top_iff.1 (by rw [← cntE_eq]; exact hfin γ.lam γ.mem Z)
  have hfrSub : frPart γ Z ⊆ clsSet F0 u' γ.lam Z := by
    rintro O ⟨F', hF', -, rfl⟩
    exact ⟨F', hF', rfl⟩
  let S : Set (TermDef.Term D u u' F0 what₂) :=
    {γ' | (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z}
  have hlam : ∀ γ' ∈ S, γ'.lam = γ.lam := fun γ' h => lam_of_termScal h.1.1
  have hrep : ∀ γ' ∈ S, RepIn u u' F0 what₂ γ' Z := fun γ' h => hC hpre γ' w' hG' Z hZ h.1.2 h.2
  have hsub : ∀ γ' ∈ S, PairVal.orbT D u u' F0 what₂ γ' Z ⊆ frPart γ Z := by
    rintro γ' h O ⟨F', hF', hr, rfl⟩
    refine ⟨F', ?_, ⟨γ', h.1.1, hr⟩, ?_⟩
    · have e := hlam γ' h
      rw [e] at hF'
      exact hF'
    · have e := hlam γ' h
      ext F''
      simp only [Set.mem_setOf_eq]
      rw [e]
      exact Iff.rfl
  have horbFin : ∀ γ' ∈ S, (PairVal.orbT D u u' F0 what₂ γ' Z).Finite := fun γ' h =>
    (hclsFin.subset hfrSub).subset (hsub γ' h)
  have hne : ∀ γ' ∈ S, (PairVal.orbT D u u' F0 what₂ γ' Z).Nonempty := by
    intro γ' h
    obtain ⟨F', hF', hr⟩ := hrep γ' h
    exact ⟨_, F', hF', hr, rfl⟩
  have hnc : ∀ γ' ∈ S, (PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard = (PairVal.orbT D u u' F0 what₂ γ' Z).ncard := by
    intro γ' h
    rw [Set.ncard_def, Set.ncard_def, hB hpre γ' w' Z h.1.2 hZ (hrep γ' h)]
  have hSfin : S.Finite := by
    have hU : S ⊆ ⋃ O ∈ frPart γ Z,
        {γ' : TermDef.Term D u u' F0 what₂ | γ'.lam = γ.lam ∧ O ∈ PairVal.orbT D u u' F0 what₂ γ' Z} := by
      intro γ' h
      obtain ⟨O, hO⟩ := hne γ' h
      simp only [Set.mem_iUnion]
      exact ⟨O, hsub γ' h hO, hlam γ' h, hO⟩
    refine Set.Finite.subset (Set.Finite.biUnion (hclsFin.subset hfrSub) (fun O _ => ?_)) hU
    refine Set.Subsingleton.finite (fun γ₁ h₁ γ₂ h₂ => ?_)
    exact orbT_disj (h₁.1.trans h₂.1.symm) h₁.2 h₂.2

  have hbU : (hclsFin.subset hfrSub).toFinset =
      hSfin.toFinset.biUnion (fun γ' => if h : γ' ∈ S then (horbFin γ' h).toFinset else ∅) := by
    ext O
    simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion]
    constructor
    · rintro ⟨F', hF', ⟨γ', hsc, hr⟩, rfl⟩
      have e := lam_of_termScal hsc
      obtain ⟨Λ, m, c⟩ := γ
      obtain ⟨Λ', m', c'⟩ := γ'
      simp only at e
      subst e
      obtain ⟨hpd, hc⟩ := hr
      have hγ' : (⟨Λ', m', c'⟩ : TermDef.Term D u u' F0 what₂) = termOf Λ' m' F' (pd_of_ez hF') := by
        exact congrArg (fun cls => TermDef.Term.mk Λ' m' cls) hc.symm
      have hS' : (⟨Λ', m', c'⟩ : TermDef.Term D u u' F0 what₂) ∈ S := by
        refine ⟨⟨hsc, ?_⟩, ?_⟩
        · rw [hγ']
          exact eligAt_termOf Λ' m' hZ hF'
        · rw [hγ']
          exact hD hpre _ w' Z (eligAt_termOf Λ' m' hZ hF') hZ (repIn_termOf Λ' m' hF')
      refine ⟨⟨Λ', m', c'⟩, hS', ?_⟩
      simp only [dif_pos hS', Set.Finite.mem_toFinset]
      exact ⟨F', hF', ⟨hpd, hc⟩, rfl⟩
    · rintro ⟨γ', hγ'S, hO⟩
      have hO' : O ∈ (horbFin γ' hγ'S).toFinset := by simpa only [dif_pos hγ'S] using hO
      exact hsub γ' hγ'S ((Set.Finite.mem_toFinset _).1 hO')
  have hdisj : ∀ γ₁ ∈ hSfin.toFinset, ∀ γ₂ ∈ hSfin.toFinset, γ₁ ≠ γ₂ →
      Disjoint (if h : γ₁ ∈ S then (horbFin γ₁ h).toFinset else ∅)
        (if h : γ₂ ∈ S then (horbFin γ₂ h).toFinset else ∅) := by
    intro γ₁ h₁ γ₂ h₂ hne12
    rw [Set.Finite.mem_toFinset] at h₁ h₂
    rw [dif_pos h₁, dif_pos h₂, Finset.disjoint_left]
    intro O hO₁ hO₂
    rw [Set.Finite.mem_toFinset] at hO₁ hO₂
    exact hne12 (orbT_disj ((hlam γ₁ h₁).trans (hlam γ₂ h₂).symm) hO₁ hO₂)
  have hcount : ((frPart γ Z).ncard : ℝ) =
      ∑ γ' ∈ hSfin.toFinset, ((PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ (hclsFin.subset hfrSub), hbU, Finset.card_biUnion hdisj]
    push_cast
    refine Finset.sum_congr rfl (fun γ' hγ' => ?_)
    have h := (Set.Finite.mem_toFinset hSfin).1 hγ'
    rw [dif_pos h, hnc γ' h, Set.ncard_eq_toFinset_card _ (horbFin γ' h)]
  refine ⟨hclsFin.subset hfrSub, ?_⟩
  haveI : Fintype {γ' : TermDef.Term D u u' F0 what₂ //
      (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z} := hSfin.fintype
  have hs := hasSum_fintype (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
      (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z} =>
    ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ))
  have h1 : ∑ γ' ∈ hSfin.toFinset, ((PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard : ℂ) =
      ∑ γ' : {γ' : TermDef.Term D u u' F0 what₂ //
        (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z},
        ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ) :=
    Finset.sum_subtype hSfin.toFinset (fun γ' => Set.Finite.mem_toFinset hSfin) _
  have h2 : (((frPart γ Z).ncard : ℝ) : ℂ) =
      ∑ γ' ∈ hSfin.toFinset, ((PairVal.orbT D u u' F0 what₂ γ' (zT γ')).ncard : ℂ) := by
    rw [hcount]
    push_cast
    rfl
  have key := h1.symm.trans h2.symm
  have key' : ∑ γ' : {γ' : TermDef.Term D u u' F0 what₂ //
        (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = tupZ M δ u u' Z},
        ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ) = ((frPart γ Z).ncard : ℂ) := by
    rw [key]
    push_cast
    rfl
  exact Eq.mpr (congrArg (HasSum _) key'.symm) hs

end SumFr

end Formalism.L2.SG.Pf.FibPart
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorEqPointMinor
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem leadingMinor_eq_pointMinor {D : D7} {n : ℕ} (w : Point D.host.E n) (l : ℕ) (hl : l ≤ n) :
    Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (ptMat w) l = Formalism.MainNotions.S.LocalSplitGroups.Dmin w l := by
  unfold Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor Formalism.MainNotions.S.LocalSplitGroups.Dmin
  rw [dite_eq_left hl]
  let e : Fin l ≃ {i : Fin n // (i : ℕ) < l} :=
    { toFun := fun j => ⟨Fin.castLE hl j, by simp⟩
      invFun := fun i => ⟨i.1, i.2⟩
      left_inv := fun j => by ext; simp
      right_inv := fun i => by ext; simp }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem conjF_star' {D : D7} (x : D.host.E) : D.conjF x = star x :=
  (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host) x).symm

theorem GPt_junk (D : D7) (u u' : D.what₂.Word) :
    GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) (toPts (Formalism.L2.SG.PairVal.junkPoint D u u')) = 0 := by
  have h := (Formalism.MainNotions.S.Inh.zero_of_gram_point_exists D u u').choose_spec
  unfold Formalism.MainNotions.S.LocalSplitGroups.Gpt at h
  unfold Formalism.L2.SG.PairVal.junkPoint GPt
  rw [LeadingMinorIntegrality.dlast_eq, LeadingMinorIntegrality.dr_eq, leadingMinor_eq_pointMinor _ _ le_rfl, leadingMinor_eq_pointMinor _ _ (Nat.le_succ _),
    ← conjF_star', ← conjF_star']
  convert h using 3
  all_goals first
    | rfl
    | (push_cast; rfl)
    | norm_cast

theorem GPt_ne_of_NGPt {D : D7} (TT : ℕ) (γ : PN.Pts D.host.E D.R.rS) (h : 1 ≤ NGPt D.host.rdE TT γ) :
    GPt TT γ ≠ 0 := by
  unfold NGPt at h
  intro h0
  rw [h0] at h
  simp [Fintype.card_ne_zero] at h
  linarith

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem gval_occ (t : TauC Y u u')
    (hG : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t)) :
    Gval (lf D (X.Fu u)) t.frame = GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t) := by
  have hne := GPt_ne_of_NGPt _ _ hG
  by_cases h : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant
  · obtain ⟨F', ⟨hP, hmk⟩, -, hcell⟩ := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm h
    have h1 := LeadingMinorIntegrality.gpt_eq (T := Tu D u) (T' := Tu D u') (lf D (X.Fu u)) F' _ hcell
    rw [show ptPN t = toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm) from rfl, h1, ← Formalism.L2.SG.Pf.SatGram.gterm_G Y t]
    have hΛ := (Y.rowsOK u).1 t.lam t.mem
    show Formalism.L2.SG.TermDef.Gt _ _ _ t.toTerm.cls = _
    rw [← hmk]
    exact Formalism.L2.SG.TermDef.Gt_mk ((Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).1) _
  · exfalso
    apply hne
    show GPt _ (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) = 0
    unfold Formalism.L2.SG.PairVal.ptOf
    rw [dite_eq_right h]
    exact GPt_junk D u u'

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLeaves
section
noncomputable section

open MeasureTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

theorem hinfCompact_holds : MassDataMassesW.HinfCompact :=
  PIW.MassDataColumns.hinfCompact_of Formalism.L2.SG.Closed.AdBridgeIso_holds Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity
    Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion (fun X u => Formalism.L2.SG.Pf.hinf_compact X u)

theorem finHA_eq_eFin {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) :
    finHA X hb x = Formalism.L2.SG.Pf.Meas.eFin X.B.I hb x := rfl

theorem kCompactOpen_holds : MassDataMassesW.KCompactOpen := by
  intro D X
  have hb := Formalism.L2.SG.Closed.AdBridgeIso_holds X.B.I
  have hs : Function.Surjective (finHA X hb) := by
    intro y
    obtain ⟨x, hx⟩ := (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).surjective y
    exact ⟨x, by rw [finHA_eq_eFin]; exact hx⟩
  have himg : ((MassDataMassesW.KX X : Subgroup _) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) =
      Formalism.L2.SG.Pf.Meas.eFin X.B.I hb '' X.B.I.Kset := by
    rw [MassDataMassesW.KX, PIW.MassDataColumns.kf_eq_image X hb hs]
    rfl
  rw [himg]
  exact ⟨(Formalism.L2.SG.Closed.AutKCompact_holds X.B.I).image (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).continuous,
    (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).isOpenMap _ (Formalism.L2.SG.Pf.kset_open X.B.I)⟩

theorem dc_finite_mono {G : Type} [Group G] (Γ K' K : Subgroup G) (h : K' ≤ K)
    (hf : Finite (DoubleCoset.Quotient (Γ : Set G) (K' : Set G))) :
    Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) := by
  haveI : Finite (Quotient (DoubleCoset.setoid (Γ : Set G) (K' : Set G))) := hf
  have hr : ∀ a b : G, (DoubleCoset.setoid (Γ : Set G) (K' : Set G)) a b → (DoubleCoset.setoid (Γ : Set G) (K : Set G)) a b := by
    intro a b hab
    rw [DoubleCoset.rel_iff] at hab ⊢
    obtain ⟨x, hx, y, hy, hxy⟩ := hab
    exact ⟨x, hx, y, h hy, hxy⟩
  show Finite (Quotient (DoubleCoset.setoid (Γ : Set G) (K : Set G)))
  refine Finite.of_surjective (Quotient.map' id hr) ?_
  intro q
  induction q using Quotient.inductionOn' with
  | h a => exact ⟨Quotient.mk'' a, rfl⟩

theorem hermitian_level_le {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) :
    PIW.MassDataColumns.unitaryLevelClosureSubgroup X hb u ≤ MassDataMassesW.KH X u := by
  rw [PIW.MassDataColumns.unitaryLevelClosureSubgroup, Subgroup.closure_le]
  rintro ⟨h, hh⟩ hk
  obtain ⟨y, ⟨k, hk2, rfl⟩, hy⟩ := hk
  show h ∈ MassDataMassesW.KX X
  have hy' : finHA X hb (X.xu u) * finHA X hb k * (finHA X hb (X.xu u))⁻¹ = h := hy
  rw [← hy']
  have hxu : finHA X hb (X.xu u) ∈ MassDataMassesW.KX X :=
    (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 (X.xu_K u)
  have hkK : finHA X hb k ∈ MassDataMassesW.KX X :=
    (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 ((Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 k hk2)
  exact (MassDataMassesW.KX X).mul_mem ((MassDataMassesW.KX X).mul_mem hxu hkK) ((MassDataMassesW.KX X).inv_mem hxu)

theorem classFinite_holds : MassDataMassesW.ClassFinite := by
  intro D X u
  have hb := Formalism.L2.SG.Closed.AdBridgeIso_holds X.B.I
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hF := Formalism.L2.SG.Closed.ClassFin_holds X u hK
  have hc := PIW.MassDataColumns.class_sets_equal_card X hb hK u (Formalism.L2.SG.Closed.AdBridgeGF_holds X.B.I)
    (Formalism.L2.SG.Closed.level_subgroup_properties X)
  have hne : Nonempty (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK)) := inferInstance
  haveI : Finite (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK)) := hF
  have hfin : Finite (PIW.MassDataColumns.ClsHA X hb u) := by
    have hpos : 0 < Nat.card (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK)) :=
      Nat.card_pos
    exact Nat.finite_of_card_ne_zero (hc ▸ hpos.ne')
  exact dc_finite_mono _ _ _ (hermitian_level_le X hb u) hfin

end Formalism.L2.SG.Pf.MassDataX
end
end

