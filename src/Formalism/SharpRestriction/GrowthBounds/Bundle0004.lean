module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeAlternative
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TotalDegreeEplus
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FirstCoefficientFacts
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.LeAndHalfLeProdOneSubExpNegOfBounds
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CardEqChainSum
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ChainDim
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0010
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountLow
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockInj
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0011
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0008
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeRatioConsecutive
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairCount
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0009
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WtBound
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0013
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bracket
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0014
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreesLargeOfStd
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseThresholdRatioConsecutive
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0012
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSidePos
public import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ComponentsInFiltrationContractionSingle
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.AntitoneOfAppend
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.EqEmptyIffSplit
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.JointTypeLatticeSaturated
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.IntegralJointTypeSum
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftSubstitutionCoeffDivisible
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.CanonicalTranslateJetIdentity
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.PlaneGramTheoremOfLemmas
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SecondValuationOfAdmitted
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrRenExpandMonomial
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsDef
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0037
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0034

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem closed_extendedAllConclusions {D : Formalism.BasicNotions.D7} (h3 : adm3 D) (hU : RestUp) (hL : RestLow) (hL1 : PartnersToFactors)
    (hLift : RestLift) : Closed (ExtendedAllConclusions D) :=
  have hA2 : RemainderSegmentBoundSecond D := restAlt2_of (restSegLow_of hL) (dimHH_of h3) charZeroAt
  closed_of_rests (fun _ _ _ => segment_statement_holds D _ _ _) (restFree D) (remainderSegmentBoundFirst D) (rest2 D) (restAlt3 D)
    (one_segment_of_upper_lower hU hL) hA2 (restExt_of restRk hL1 hLift hA2)

theorem dimYAt_of_adm {D : Formalism.BasicNotions.D7} (hA : admitted D) : DimYAt :=
  dimY_of (D := D) hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.1 (stWeylAt D)

def Open : Prop := RestPairLift

theorem stmtEExt_of {D : Formalism.BasicNotions.D7} (h : admitted D → Open) : ExtendedClosedForm D := fun hA =>
  have hPL := h hA
  have hY := dimYAt_of_adm hA
  have hCD : ChainDimAt := chainDim_of hY
  have hNB : NumBranchAt := numBranch_of hA.2.1 hA.2.2.1
  have hT : RestTail := restTail_of hCD hNB restPairCount (restNotKeptWt_of (wtBound_of hCD) (restBracket_of (restPairFacts_of restNUp) coarse_degrees_large_holds))
  have hK2 : LeadingRowsBeyondThreshold := top_rows_bound_holds
  have hB : BlockRankAt := blockRankAt
  have hK4 : KeptBlocksBeyondThreshold := kept_blocks_holds
  have hL1 : PartnersToFactors := partners_to_factors_holds
  have hCU : RestCountUp := upper_count_of_top_rows hCD hNB hK2
  have hMU : RestMatchUp := restMatchUp_of (restFirstRows_of (restSTopRows_of hK2))
  have hCL : RestCountLow := restCountLow_of'' hCD hT hMU hK4
  closed_extendedAllConclusions hA.2.2.1 (restUp_of hB hY charZeroAt hCU) (restLow_of hB hY charZeroAt hCL) hL1 (restLift_of (restLiftVec_of hPL))

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths
section
noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

theorem nested_sets_lemma_of_admitted (D : Formalism.BasicNotions.D7) (h14 : JointComponentsPaths D) (h16 : PairedPathIndependence D) : ConclusionB3 D :=
  lemma_B3 D h16 (lemma_B2 D) (integral_joint_type_sum D h14 h16)

end Formalism.MainNotions.LemmaBAlt
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments
section
noncomputable section

namespace Formalism.MainNotions.PlaneGram

open Formalism.MainNotions.G

theorem stmt (D : Formalism.BasicNotions.D7) {CH : ℝ} (hCH : 26 ≤ CH) : Formalism.MainNotions.PlaneGramData.Stmt D CH 2 24 60 := by
  intro p O _ _ _ _ hSet hAdm
  obtain ⟨⟨S⟩, n', hG⟩ := hSet
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := hAdm
  exact Br.plane_gram_of_theorem_at S hG
    (plane_gram_theorem_of_five_lemmas le_rfl (second_valuation_of_admitted h2) (brSPAN S h3) (brPROJ S h4) (brDIG D S hG h5)
      (brDER S h6)) hCH

theorem stmtE (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.PlaneGramData.ClosedFormOfAdmitted D :=
  ⟨26, 2, 24, 60, by norm_num, by norm_num, by norm_num, by norm_num, fun _ hCH => stmt D hCH⟩

end Formalism.MainNotions.PlaneGram
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsCg
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VS

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {σ τ : Type} [Finite σ]

def UImg (V : VF C) (A : σ → MvPowerSeries τ C) (Φ : MvPowerSeries τ C) : Prop :=
  ∃ U : MvPowerSeries σ C, IsIU V U ∧ MvPowerSeries.subst A U = Φ

def GImg (V : VF C) (A : σ → MvPowerSeries τ C) (a : Fin dd → MvPowerSeries τ C) : Prop :=
  ∃ P : Fin dd → MvPowerSeries σ C, VP.GoodPt V P ∧ ∀ i, MvPowerSeries.subst A (P i) = a i

def Cg (V : VF C) (A : σ → MvPowerSeries τ C) (f g : MvPowerSeries τ C) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ MvPowerSeries.constantCoeff g = 0 ∧ UImg V A (mvExp (f - g))

variable {A : σ → MvPowerSeries τ C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)

include hA

theorem UImg.one : UImg V A 1 := ⟨1, IsIU.one, VP.subst_one hA⟩

theorem UImg.mul {Φ Ψ : MvPowerSeries τ C} (h : UImg V A Φ) (h' : UImg V A Ψ) : UImg V A (Φ * Ψ) := by
  obtain ⟨U, hU, rfl⟩ := h
  obtain ⟨U', hU', rfl⟩ := h'
  exact ⟨U * U', hU.mul hU', VP.subst_mul hA _ _⟩

theorem UImg.pow {Φ : MvPowerSeries τ C} (h : UImg V A Φ) (k : ℕ) : UImg V A (Φ ^ k) := by
  obtain ⟨U, hU, rfl⟩ := h
  exact ⟨U ^ k, ⟨hU.1.pow k, by rw [map_pow, V.v.map_pow, hU.2, smul_zero]⟩, VP.subst_pow' hA _ _⟩

theorem UImg.exp_neg {f : MvPowerSeries τ C} (hf : MvPowerSeries.constantCoeff f = 0) (h : UImg V A (mvExp f)) :
    UImg V A (mvExp (-f)) := by
  obtain ⟨U, hU, e⟩ := h
  obtain ⟨U', hU'i, hUU⟩ := VP.intInv hU.1 hU.2
  have hU'0 : V.v (MvPowerSeries.constantCoeff U') = 0 := by
    have h1 := congrArg (fun x => V.v (MvPowerSeries.constantCoeff x)) hUU
    simp only [map_mul, map_one, V.v.map_mul, V.v.map_one, hU.2, add_zero] at h1
    exact h1
  refine ⟨U', ⟨hU'i, hU'0⟩, ?_⟩
  have h2 : MvPowerSeries.subst A U' * mvExp f = 1 := by
    rw [← e, ← VP.subst_mul hA, hUU, VP.subst_one hA]
  have h3 : mvExp (-f) * mvExp f = 1 := by
    rw [← VP.exp_add (by rw [map_neg, hf, neg_zero]) hf, neg_add_cancel, rtj_mvExp_zero]
  calc MvPowerSeries.subst A U' = MvPowerSeries.subst A U' * (mvExp (-f) * mvExp f) := by rw [h3, mul_one]
    _ = (MvPowerSeries.subst A U' * mvExp f) * mvExp (-f) := by ring
    _ = mvExp (-f) := by rw [h2, one_mul]

theorem Cg.refl {f : MvPowerSeries τ C} (hf : MvPowerSeries.constantCoeff f = 0) : Cg V A f f :=
  ⟨hf, hf, by rw [sub_self, rtj_mvExp_zero]; exact UImg.one hA⟩

theorem Cg.symm {f g : MvPowerSeries τ C} (h : Cg V A f g) : Cg V A g f :=
  ⟨h.2.1, h.1, by
    have := UImg.exp_neg hA (by rw [map_sub, h.1, h.2.1, sub_zero]) h.2.2
    rwa [neg_sub] at this⟩

theorem Cg.trans {f g k : MvPowerSeries τ C} (h : Cg V A f g) (h' : Cg V A g k) : Cg V A f k :=
  ⟨h.1, h'.2.1, by
    have := UImg.mul hA h.2.2 h'.2.2
    rw [← VP.exp_add (by rw [map_sub, h.1, h.2.1, sub_zero]) (by rw [map_sub, h'.1, h'.2.1, sub_zero])] at this
    rwa [sub_add_sub_cancel] at this⟩

theorem Cg.add {f g f' g' : MvPowerSeries τ C} (h : Cg V A f g) (h' : Cg V A f' g') : Cg V A (f + f') (g + g') :=
  ⟨by rw [map_add (f := _), h.1, h'.1, add_zero], by rw [map_add (f := _), h.2.1, h'.2.1, add_zero], by
    have := UImg.mul hA h.2.2 h'.2.2
    rw [← VP.exp_add (by rw [map_sub, h.1, h.2.1, sub_zero]) (by rw [map_sub, h'.1, h'.2.1, sub_zero])] at this
    rwa [show f - g + (f' - g') = f + f' - (g + g') by ring] at this⟩

theorem Cg.sum {ι : Type} (s : Finset ι) {f g : ι → MvPowerSeries τ C} (h : ∀ i ∈ s, Cg V A (f i) (g i)) :
    Cg V A (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (Cg.refl hA (map_zero _) : Cg V A (0 : MvPowerSeries τ C) 0)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Cg.add hA (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Cg.nsmul {f g : MvPowerSeries τ C} (h : Cg V A f g) (k : ℕ) : Cg V A ((k : C) • f) ((k : C) • g) :=
  ⟨VP.cc_smul _ h.1, VP.cc_smul _ h.2.1, by
    rw [← smul_sub, VP.exp_nsmul (by rw [map_sub, h.1, h.2.1, sub_zero])]
    exact UImg.pow hA h.2.2 k⟩

theorem Cg.unit {f g : MvPowerSeries τ C} (h : Cg V A f g) :
    ∃ U : MvPowerSeries σ C, IsIU V U ∧ mvExp f = MvPowerSeries.subst A U * mvExp g := by
  obtain ⟨U, hU, e⟩ := h.2.2
  refine ⟨U, hU, ?_⟩
  rw [e, ← VP.exp_add (by rw [map_sub, h.1, h.2.1, sub_zero]) h.2.1, sub_add_cancel]

theorem cg_of {F G : MvPowerSeries σ C} (hF : MvPowerSeries.constantCoeff F = 0)
    (hG : MvPowerSeries.constantCoeff G = 0) (hi : IntS V (mvExp (F - G))) :
    Cg V A (MvPowerSeries.subst A F) (MvPowerSeries.subst A G) :=
  ⟨VP.cc_subst hA hF, VP.cc_subst hA hG, mvExp (F - G), VP.isIU_of_exp hi rfl, by
    rw [VP.subst_exp hA (by rw [map_sub, hF, hG, sub_zero]), VP.subst_sub' hA]⟩

theorem GImg.zero : GImg V A (fun _ : Fin dd => (0 : MvPowerSeries τ C)) :=
  ⟨fun _ => 0, VP.GoodPt.zero, fun _ => VP.subst_zero' hA⟩

variable (Y : FBChart C V O dd)

theorem GImg.add {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    GImg V A (VP.addAt Y a b) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  exact ⟨VP.addAt Y P Q, hP.add Y hQ, fun i => VP.addAt_subst Y hA hP.1 hQ.1 i⟩

theorem GImg.act (x : O) {a : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) : GImg V A (VP.actAt Y x a) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  exact ⟨VP.actAt Y x P, hP.act Y x, fun i => VP.actAt_subst Y hA hP.1 x i⟩

omit Y in
theorem GImg.map {Y : FBChart C V O dd} {φ : Pt C 1 dd} (hφ : IsEndo Y φ) {a : Fin dd → MvPowerSeries τ C}
    (ha : GImg V A a) : GImg V A (VP.mapAt φ a) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  exact ⟨VP.mapAt φ P, ⟨VP.cc_mapAt hφ.cc hP.1, fun i =>
    IntS.subst (a := fun q : Fin 1 × Fin dd => P q.2) (fun q => hP.1 q.2) (fun q => hP.2 q.2) (hφ.int i)⟩,
    fun i => VP.mapAt_subst hA φ hP.1 i⟩

theorem gauge_congr_additive_left {a b c : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) (hc : GImg V A c) :
    Cg V A (VP.hAt Y (VP.addAt Y a b) c) (VP.hAt Y a c + VP.hAt Y b c) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain ⟨R, hR, e''⟩ := hc
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  obtain rfl : (fun i => MvPowerSeries.subst A (R i)) = c := funext e''
  have c1 := VP.cc_hAt Y hP.1 hR.1
  have c2 := VP.cc_hAt Y hQ.1 hR.1
  have c3 := VP.cc_hAt Y (VP.cc_addAt Y hP.1 hQ.1) hR.1
  have h := cg_of (V := V) hA (F := VP.hAt Y P R + VP.hAt Y Q R) (G := VP.hAt Y (VP.addAt Y P Q) R)
    (by rw [map_add (f := _), c1, c2, add_zero]) c3 (by
      rw [← VP.first_partial_law_at_points Y hP.1 hQ.1 hR.1]
      exact IntS.subst (VP.constantCoeff_triple_substitution hP.1 hQ.1 hR.1) (VP.integral_triple_substitution hP.2 hQ.2 hR.2) Y.intPh1)
  rw [VP.subst_add' hA, VP.hAt_subst Y hA hP.1 hR.1, VP.hAt_subst Y hA hQ.1 hR.1,
    VP.hAt_subst Y hA (VP.cc_addAt Y hP.1 hQ.1) hR.1, funext (VP.addAt_subst Y hA hP.1 hQ.1)] at h
  exact Cg.symm hA h

theorem gauge_congr_additive_right {a b c : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) (hc : GImg V A c) :
    Cg V A (VP.hAt Y a (VP.addAt Y b c)) (VP.hAt Y a b + VP.hAt Y a c) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain ⟨R, hR, e''⟩ := hc
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  obtain rfl : (fun i => MvPowerSeries.subst A (R i)) = c := funext e''
  have c1 := VP.cc_hAt Y hP.1 hQ.1
  have c2 := VP.cc_hAt Y hP.1 hR.1
  have c3 := VP.cc_hAt Y hP.1 (VP.cc_addAt Y hQ.1 hR.1)
  have h := cg_of (V := V) hA (F := VP.hAt Y P Q + VP.hAt Y P R) (G := VP.hAt Y P (VP.addAt Y Q R))
    (by rw [map_add (f := _), c1, c2, add_zero]) c3 (by
      rw [← VP.second_partial_law_at_points Y hP.1 hQ.1 hR.1]
      exact IntS.subst (VP.constantCoeff_triple_substitution hP.1 hQ.1 hR.1) (VP.integral_triple_substitution hP.2 hQ.2 hR.2) Y.intPh2)
  rw [VP.subst_add' hA, VP.hAt_subst Y hA hP.1 hQ.1, VP.hAt_subst Y hA hP.1 hR.1,
    VP.hAt_subst Y hA hP.1 (VP.cc_addAt Y hQ.1 hR.1), funext (VP.addAt_subst Y hA hQ.1 hR.1)] at h
  exact Cg.symm hA h

theorem cg_sy {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    Cg V A (VP.hAt Y b a) (VP.hAt Y a b) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  have h := cg_of (V := V) hA (F := VP.hAt Y Q P) (G := VP.hAt Y P Q) (VP.cc_hAt Y hQ.1 hP.1) (VP.cc_hAt Y hP.1 hQ.1) (by
      rw [← VP.sy_at Y hP.1 hQ.1]
      exact IntS.subst (VP.constantCoeff_pair_substitution hP.1 hQ.1) (VP.integral_pair_substitution hP.2 hQ.2) Y.intSy)
  rwa [VP.hAt_subst Y hA hQ.1 hP.1, VP.hAt_subst Y hA hP.1 hQ.1] at h

theorem cg_ad (x : O) {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    Cg V A (VP.hAt Y (VP.actAt Y x a) b) (VP.hAt Y a (VP.actAt Y (star x) b)) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  have h := cg_of (V := V) hA (F := VP.hAt Y (VP.actAt Y x P) Q) (G := VP.hAt Y P (VP.actAt Y (star x) Q))
    (VP.cc_hAt Y (VP.cc_actAt Y x hP.1) hQ.1) (VP.cc_hAt Y hP.1 (VP.cc_actAt Y _ hQ.1)) (by
      rw [← VP.ad_at Y hP.1 hQ.1]
      exact IntS.subst (VP.constantCoeff_pair_substitution hP.1 hQ.1) (VP.integral_pair_substitution hP.2 hQ.2) (Y.intAd x))
  rwa [VP.hAt_subst Y hA (VP.cc_actAt Y x hP.1) hQ.1, VP.hAt_subst Y hA hP.1 (VP.cc_actAt Y _ hQ.1),
    funext (VP.actAt_subst Y hA hP.1 x), funext (VP.actAt_subst Y hA hQ.1 (star x))] at h

theorem cg_adj {φ φ' : Pt C 1 dd} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ' : ∀ i, MvPowerSeries.constantCoeff (φ' i) = 0)
    (hadj : IntS V (FB.expS C (ev (n := 2) ![comp1 φ (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 φ' (pt C dd 1)] Y.h)))
    {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    Cg V A (VP.hAt Y (VP.mapAt φ a) b) (VP.hAt Y a (VP.mapAt φ' b)) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  have h := cg_of (V := V) hA (F := VP.hAt Y (VP.mapAt φ P) Q) (G := VP.hAt Y P (VP.mapAt φ' Q))
    (VP.cc_hAt Y (VP.cc_mapAt hφ hP.1) hQ.1) (VP.cc_hAt Y hP.1 (VP.cc_mapAt hφ' hQ.1)) (by
      rw [← VP.cmp_at Y hφ hφ' hP.1 hQ.1]
      exact IntS.subst (VP.constantCoeff_pair_substitution hP.1 hQ.1) (VP.integral_pair_substitution hP.2 hQ.2) hadj)
  rwa [VP.hAt_subst Y hA (VP.cc_mapAt hφ hP.1) hQ.1, VP.hAt_subst Y hA hP.1 (VP.cc_mapAt hφ' hQ.1),
    funext (VP.mapAt_subst hA φ hP.1), funext (VP.mapAt_subst hA φ' hQ.1)] at h

end VS

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsPack
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0 RowTiePProj

namespace GmPackP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}

theorem half [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0) (ε : O)
    (hε : ∃ y, ε * ε - ε = (V.l : O) * y) (hε1 : ∀ a, V.MM (p.em a ε - 1))
    (hεx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, ε * x = (V.l : O) * y) (M : ℕ → O) (φ : Pt C 1 dd)
    (hT : ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (φ i)) :
    (∀ a, comp1 φ (Y.B.A.act a) = comp1 (Y.B.A.act a) φ) ∧
      ∀ v : Fin dd → C, ∃ b : I0 → C, linAct φ v = ∑ c, b c • p.e c := by
  have hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := const_of_lim Y hT
  have act0 : ∀ x i, MvPowerSeries.constantCoeff (Y.B.A.act x i) = 0 := Y.B.A.const
  refine ⟨?_, ?_⟩
  · intro a
    funext i
    have L := TendsS.comp1 (φ := fun n => Y.B.A.act (M n * ε ^ V.l ^ n)) (b := fun _ => Y.B.A.act a)
      (fun _ => act0 a) (act0 a) hT (fun _ => TendsS.const _) i
    have R := TendsS.comp1 (φ := fun _ => Y.B.A.act a) (b := fun n => Y.B.A.act (M n * ε ^ V.l ^ n))
      (fun n => act0 _) hφ0 (fun _ => TendsS.const _) hT i
    have eq : (fun n => comp1 (Y.B.A.act (M n * ε ^ V.l ^ n)) (Y.B.A.act a) i) =
        fun n => comp1 (Y.B.A.act a) (Y.B.A.act (M n * ε ^ V.l ^ n)) i := funext fun n => by
      rw [← Y.B.A.mul_act, ← Y.B.A.mul_act, mul_comm]
    rw [eq] at L
    exact L.unique R
  · obtain ⟨E, -, -, -, hET⟩ := StartSelf.lim_endo Y p.em p.em_int p.hd p.em_conj ε hε hεx (fun _ => 1)
      (fun N a => by rw [sub_self, map_zero]; exact VF.Ge.zero _)
    have hElim : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (MvPowerSeries.coeff μ (E i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i)) := by
      intro N i μ
      obtain ⟨n0, h⟩ := hET i μ N
      exact ⟨n0, fun n hn => by simpa only [one_mul] using h n hn⟩
    have hEspan := hLie C V O dd Y d I0 p ε hε hε1 hεx E hElim
    have hEφ : comp1 E φ = φ := by
      funext i
      have L := TendsS.comp1 (φ := fun n => Y.B.A.act (1 * ε ^ V.l ^ n)) (b := fun n => Y.B.A.act (M n * ε ^ V.l ^ n))
        (fun n => act0 _) hφ0 hET hT i
      have hdiv : ∀ n, ((V.l : O) ^ (n + 1)) ∣ (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n) - M n * ε ^ V.l ^ n := by
        intro n
        have e1 : (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n) - M n * ε ^ V.l ^ n =
            M n * (ε ^ V.l ^ n * ε ^ V.l ^ n - ε ^ V.l ^ n) := by ring
        rw [e1]
        exact dvd_mul_of_dvd_right (sq_cong hε n) _
      have R := tendsS_of_small RowTiePLSmall.lSmall_holds Y
        (x := fun n => (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n)) (x' := fun n => M n * ε ^ V.l ^ n) hdiv hT i
      have eq : (fun n => comp1 (Y.B.A.act (1 * ε ^ V.l ^ n)) (Y.B.A.act (M n * ε ^ V.l ^ n)) i) =
          fun n => Y.B.A.act ((1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n)) i := funext fun n => by
        rw [Y.B.A.mul_act (1 * ε ^ V.l ^ n) (M n * ε ^ V.l ^ n)]
      rw [eq] at L
      exact L.unique R
    intro v
    obtain ⟨b, hb⟩ := hEspan (linAct φ v)
    exact ⟨b, by rw [← hb, ← VP.linAct_comp1 E φ hφ0, hEφ]⟩

theorem one_entry [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0)
    (M : ℕ → O) (t : ZMod d → C) (hMt : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (t a - p.em a (M N))) :
    ∃ γ γ' : Pt C 1 dd, IsEndo Y γ ∧ IsEndo Y γ' ∧
      (∀ a, comp1 γ (Y.B.A.act a) = comp1 (Y.B.A.act a) γ) ∧
      (∀ a, comp1 γ' (Y.B.A.act a) = comp1 (Y.B.A.act a) γ') ∧
      (∀ c, linAct γ (p.e c) = t (p.ty0 c) • p.e c) ∧
      (∀ c, linAct γ' (p.e c) = t (p.ty0 c + p.hd) • p.e c) ∧
      (∀ v : Fin dd → C, ∃ b : I0 → C, linAct γ v = ∑ c, b c • p.e c) ∧
      (∀ v : Fin dd → C, ∃ b : I0 → C, linAct γ' v = ∑ c, b c • p.e c) ∧
      IntS V (FB.expS C (ev (n := 2) ![comp1 γ (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 γ' (pt C dd 1)] Y.h)) := by
  obtain ⟨ε, hε, hε1, hεx⟩ := p.em_unr
  have hM : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (p.em a (M (N + 1) - M N)) := by
    intro N a
    have e2 : p.em a (M (N + 1) - M N) = (t a - p.em a (M N)) - (t a - p.em a (M (N + 1))) := by
      rw [map_sub]; ring
    rw [e2]
    exact (hMt N a).sub ((hMt (N + 1) a).mono (by push_cast; linarith))
  have ht : ∀ a, Tends V (fun n => p.em a (M n)) (t a) := fun a =>
    tends_of_nat fun N => ⟨N, fun n hn => (hMt n a).mono (by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      push_cast; linarith)⟩
  have hεs := star_rel hε
  have hεs1 : ∀ a, V.MM (p.em a (star ε) - 1) := fun a => by rw [p.em_conj]; exact hε1 _
  have hεsx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, star ε * x = (V.l : O) * y := by
    intro x hx
    obtain ⟨y, hy⟩ := hεx (star x) fun a => by rw [p.em_conj]; exact hx (a + p.hd)
    refine ⟨star y, ?_⟩
    have h := congrArg star hy
    simp only [star_mul, star_star, star_natCast] at h
    rw [mul_comm, h, mul_comm]
  have hMs : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (p.em a (star (M (N + 1)) - star (M N))) := fun N a => by
    rw [← star_sub, p.em_conj]; exact hM N (a + p.hd)
  have cvA := StartSelf.actCv_of Y p.em ε hε (fun a => p.em_int a ε) hεx M hM
  have cvB := StartSelf.actCv_of Y p.em (star ε) hεs (fun a => p.em_int a _) hεsx (fun N => star (M N)) hMs
  have sA : (fun n => star (M n * ε ^ V.l ^ n)) = fun n => star (M n) * star ε ^ V.l ^ n :=
    funext fun n => by rw [star_mul', star_pow]
  have sB : (fun n => star (star (M n) * star ε ^ V.l ^ n)) = fun n => M n * ε ^ V.l ^ n :=
    funext fun n => by rw [star_mul', star_pow, star_star, star_star]
  obtain ⟨γ, γb, hγI, -, hγl, hγbl, hhom, hexp⟩ := endomorphism_limit_integral Y (fun n => M n * ε ^ V.l ^ n) cvA (by rw [sA]; exact cvB)
  obtain ⟨γ2, -, hγ2I, -, hγ2l, -, hhom2, -⟩ := endomorphism_limit_integral Y (fun n => star (M n) * star ε ^ V.l ^ n) cvB
    (by rw [sB]; exact cvA)
  have hT : ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (γ i) := tends_of_endomorphism_limit Y hγl
  have hTb : ∀ i, TendsS V (fun n => Y.B.A.act (star (M n) * star ε ^ V.l ^ n) i) (γb i) := by
    have h := tends_of_endomorphism_limit Y hγbl
    simpa only [star_mul', star_pow] using h
  have hT2 : ∀ i, TendsS V (fun n => Y.B.A.act (star (M n) * star ε ^ V.l ^ n) i) (γ2 i) := tends_of_endomorphism_limit Y hγ2l
  have heq : γ2 = γb := funext fun i => (hT2 i).unique (hTb i)
  subst heq
  obtain ⟨hc, hi⟩ := half hLie Y p ε hε hε1 hεx M γ hT
  obtain ⟨hc', hi'⟩ := half hLie Y p (star ε) hεs hεs1 hεsx (fun N => star (M N)) γ2 hT2
  refine ⟨γ, γ2, ⟨hγI, const_of_lim Y hT, hhom⟩, ⟨hγ2I, const_of_lim Y hT2, hhom2⟩, hc, hc', ?_, ?_, hi, hi', hexp⟩
  · exact fun c => StartSelf.lin_of_lim Y p M ε hε1 t ht γ hT c
  · exact fun c => StartSelf.lin_of_lim Y p (fun N => star (M N)) (star ε) hεs1 (fun a => t (a + p.hd))
      (fun a => by simp only [p.em_conj]; exact ht (a + p.hd)) γ2 hT2 c

end GmPackP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}

theorem gmPack_of_lie [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0]
    (p : SelfData Y d I0) : GmPackSt Y p := by
  choose Mm hMm using fun N : ℕ => p.gm_lim (N + 1)
  have h := fun r s : Fin 2 => GmPackP.one_entry hLie Y p (fun N => Mm N r s) (fun a => p.gm a r s)
    (fun N a => hMm N a r s)
  choose γ γ' h1 h2 h3 h4 h5 h6 h7 h8 h9 using h
  exact ⟨γ, γ', ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

theorem gmPack_of [NeZero d] (hE : RowTiePKey.KeyEigSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0]
    (p : SelfData Y d I0) : GmPackSt Y p := gmPack_of_lie (projLieSelf_of hE) Y p

theorem gmPack_holds [NeZero d] (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0) :
    GmPackSt Y p := gmPack_of RowTiePKey.keyEig_holds Y p

end Formalism.L2.FormalSeriesBounds
end
end

