module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0010
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TamagawaPeterssonLambdaSqNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0021
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.SupremumConstantLogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
section
section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.CovTop
theorem PublishedHodgeBundleTheorems.toClassicalTheorems : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.Hypotheses'' := fun h => h.toClassicalTheoremsOf GlobalTheory.T.toroidalFlagProportionality_of_goodChernWeil
end GlobalTheory.CovTop
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_topology_refinement : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.Hypotheses'' := by
  first | exact @_root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems | exact _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems | (intros; apply _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleAmpleOnRegularLocus
section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem hodge_bundle_ample_at_regular_point : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ la : AllWt.Weight Dw, GapGe 1 la → ∀ y ∈ U₀ TF.X Z, ∃ mu : AllWt.Weight Dw, GapGe 0 mu ∧ ∃ m : ℕ, 0 < m ∧ AmpleAt (L₀ TF.X Z (m • la - mu)) y := by
  intro hP hN hS hC E _ _ _ H Dw l Xo c TF Z hF la hla y hy
  obtain ⟨A, hA⟩ := GlobalTheory.exists_isAmpleLB_of_isProjOver TF.Y.proj
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.T.relativelyAmple_comp_of_exists_weight hP hN E H Dw l Xo c TF Z hF
  obtain ⟨n, hn⟩ := hρ A hA.isLB hA
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.T.hodgeBundle_dominates_of_large_weight hP hN hS hC E H Dw l Xo c TF Z hF
  obtain ⟨m, s, -, hs⟩ := hχ y hy (lbPow A n) (isLB_lbPow hA.isLB n)
  obtain ⟨mu, hmu, M, hM, e⟩ := exists_dominant_sub la (m • χ - ρ) hla
  exact ⟨mu, hmu, M, hM, e ▸ AmpleTwist.ampleAt_of_sec E H Dw l Xo c TF Z A hA.isLB ρ χ n m hn y s hs⟩
end GlobalTheory.HSApp
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_bundle_ample_on_regular_locus : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ la : AllWt.Weight Dw, GapGe 1 la → ∀ y ∈ U₀ TF.X Z, ∃ mu : AllWt.Weight Dw, GapGe 0 mu ∧ ∃ m : ℕ, 0 < m ∧ AmpleAt (L₀ TF.X Z (m • la - mu)) y := by
  first | exact @_root_.GlobalTheory.HSApp.hodge_bundle_ample_at_regular_point | exact _root_.GlobalTheory.HSApp.hodge_bundle_ample_at_regular_point | (intros; apply _root_.GlobalTheory.HSApp.hodge_bundle_ample_at_regular_point <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralCuspSlopePowerBound
section
section
section
noncomputable section
namespace UpperTheory.Lit.Tam
end UpperTheory.Lit.Tam
end
end
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
namespace GlobalTheory.SupModel
open Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.SupModel
end
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
noncomputable section
namespace GlobalTheory.LevGeo.RankBd
variable {D : D7} {r : ℕ} {Comp : Type} [Fintype Comp] {X : Comp → Data D.host.E r}
open scoped TensorProduct
open scoped TensorProduct
variable {D : D7} {r : ℕ} {Comp : Type} [Fintype Comp] {X : Comp → Data D.host.E r}
open Module
end GlobalTheory.LevGeo.RankBd
end
end
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
namespace GlobalTheory.LamPet
open scoped ENNReal
end GlobalTheory.LamPet
end
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.LamMuMax
end GlobalTheory.LamMuMax
end
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
namespace GlobalTheory
end GlobalTheory
end
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
namespace GlobalTheory
end GlobalTheory
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.BergComp
open MeasureTheory
end GlobalTheory.BergComp
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.ConstSzRows
end GlobalTheory.ConstSzRows
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.BergRank
open ReciprocityTheory.ChartRestriction.G.FD
end GlobalTheory.BergRank
namespace GlobalTheory.BergRank
theorem _root_.UpperTheory.Lit.Tam.tamagawa_number_formula : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 20 * Lb → ∀ Z, BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ SupBdWt Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ Real.log (Y.rkC la Z) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  intro hP
  refine ⟨4000, by norm_num, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hsz hfr ho la hla hS Z
  have hL := (GlobalTheory.T.deepLevelCover_principalLevel_laws_galois D T j Y e o hT hj hY hY.unit hY.modelW).1
  set S : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set n : ℝ := (Module.finrank ℚ D.host.E : ℝ) with hn
  have hn1 : 1 ≤ n := by
    have : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    rw [hn]; exact_mod_cast this
  have hnlog : Real.log n ≤ 3 * Lb := (log_finrank_le_fieldSz _).trans hsz
  set w : ℝ := 2 * n * S + 1 with hw
  have hnS : 0 ≤ n * S := mul_nonneg (by linarith) hS0
  have hw1 : 1 ≤ w := by rw [hw]; nlinarith
  have hlogw : Real.log w ≤ 25 * Lb := by
    have hint : S = (((∑ τ, ∑ k, |la τ k|) : ℤ) : ℝ) := by rw [hSdef]; push_cast; rfl
    have hz : (0 : ℤ) ≤ ∑ τ, ∑ k, |la τ k| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    rcases hz.eq_or_lt with h0 | h1
    · have : S = 0 := by rw [hint, ← h0]; simp
      rw [hw, this]; simp; linarith
    · have hS1 : 1 ≤ S := by rw [hint]; exact_mod_cast h1
      have hwle : w ≤ 3 * (n * S) := by rw [hw]; nlinarith
      have hlS : Real.log S ≤ 20 * Lb := hS
      have e1 : Real.log w ≤ Real.log (3 * (n * S)) := Real.log_le_log (by linarith) hwle
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity)] at e1
      have h3 : Real.log 3 < 2 := by
        have := Real.log_two_lt_d9; have h4 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
        have : Real.log 4 = 2 * Real.log 2 := by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith
      linarith
  obtain ⟨hβ1, hβ⟩ := UpperTheory.Lit.Tam.supConst2Bounds D Y.d.l₂.M Lb w (by have := Y.d.l₂.three_le; omega) hLb hM hsz hfr hw1 hlogw
  set β := MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d Y.d.l₂.M w with hβdef
  have hβexp : β ≤ Real.exp (4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3) := by
    rw [← Real.exp_log (by linarith : 0 < β)]; exact Real.exp_le_exp.2 hβ
  have hsp : ∀ σ k, ∑ τ, ((Y.U σ).X k).spread (AllWt.modelWt (Y.U σ) (wtOf _ la 0) k) τ ≤ w := fun σ k =>
    (sum_spread_modelWt_le _ la k).trans (by rw [hw]; linarith)
  have hB : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la β := fun σ hσ y hy =>
    UpperTheory.Lit.Tam.tamagawaPeterssonLambdaSq_nonneg trivial D j _ _ _ _ _ Y.U Y.dict hL σ hσ (wtOf _ la 0) (AllWt.even_wtOf la 0) w (by linarith) (hsp σ) Z y hy
  have hBexp : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) :=
    fun σ hσ y hy => (hB σ hσ y hy).trans (ENNReal.ofReal_le_ofReal hβexp)
  refine ⟨hBexp, ?_, ?_⟩
  · refine SupBdWt.of_bergOn (Real.exp_pos _).le ?_ hBexp
    intro σ hσ g
    obtain ⟨th, hr, -, hd⟩ := hY.dictU σ hσ
    exact Formalism.L2.Pj.dict_dom_of hd g
  · have hrk := _root_.GlobalTheory.RankBergman.rkC_le_of_bergLe D T.toCore j Y e o hY la Z β (by linarith) hB
    have hpos : 0 ≤ 4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by positivity
    rcases (show (0 : ℝ) ≤ Y.rkC la Z by unfold Deep.rkC; positivity).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; exact hpos
    · exact (Real.log_le_log h0 hrk).trans hβ
end GlobalTheory.BergRank
end
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.LamCore
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.LamCore
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogCanonicalReflOfBoundary
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogCanonicalReflexive
theorem logCanonical_refl_of_boundary : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str (tens (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z b).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs).mul ω₀.ω ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z hF hKS hV ω₀ b s hs m
  have hoff : ∀ z, z ∈ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off ↔ z ∈ U₀ TF.X Z := fun z => by
    rw [Modif.off_eq]; rfl
  haveI : IsReduced (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X := isReduced_Y₀ TF.X Z
  have hdense : Dense ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off : Set (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) := by
    rw [Modif.off_eq]; exact (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).dense
  have hpole : SimplePoleAlong (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs) ω₀.ω := by
    intro y hy
    have hy' : y ∉ U₀ TF.X Z := fun h => hy ((hoff y).2 h)
    obtain ⟨V, hyV, t, h1, h2⟩ := _root_.GlobalTheory.T.boundary_divisor_has_reduced_equation hP E H Dw l Xo c TF Z hF hV y hy'
    obtain ⟨V', hyV', hle, i, j, u, hi, hj, hu, hpl⟩ :=
      _root_.GlobalTheory.T.exists_simple_log_pole_along_boundary hP hG E H Dw l Xo c TF Z hF hKS hV ω₀ y hy' V hyV t h1 h2
    refine ⟨V', hyV', (i, j), fun z hz => ⟨hi hz, (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).mem _ _ _).2 (hj hz)⟩,
      fun z hz => (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).mem _ _ _).2 (hj hz),
      fun z hz => ⟨hi hz, (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).mem _ _ _).2 (hj hz)⟩,
      resG _ hle t, u, fun z hz => ?_, hu, fun W hW f hf z hz => ?_, fun z hz ho => ?_⟩
    · erw [ger_resG, hoff]; exact h1 z (hle hz)
    · erw [ger_resG]
      exact h2 W (hW.trans hle) f (fun z hz hz' => hf z hz fun h => hz' ((hoff z).1 h)) z hz
    · erw [ger_resG]; exact hpl z hz ho _
  refine ⟨fun ⟨g, hg, e⟩ => ?_, fun ⟨G, hG⟩ => ?_⟩
  · obtain ⟨G, hG'⟩ := _root_.GlobalTheory.LogCanonicalReflexive.exists_extend_mul_of_simplePole hdense _ ω₀.ω hpole (H0.pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top g) (fun y hy i hi => by
      have e := H0.germ_pull (p := str₀ TF.X Z) (B := L₀ TF.X Z s) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top i y (memTop y) hi g
      rw [e]
      have h := hg y (fun h => hy ((hoff y).2 h)) (i PUnit.unit) (mem_pull.1 hi)
      exact map_nonunit ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ.stalkMap y).hom _ h)
    refine ⟨G, hG'.trans ?_⟩
    subst e
    congr 1
    exact (restr_pull (isLB_L₀ TF.X Z s) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top le_top g).trans (H0.pull_restr (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off_eq.le g).symm
  · obtain ⟨g', hv, hr⟩ := GlobalTheory.T.extends_vanishing_of_simplePole_mul_extends hdense _ ω₀.ω hpole G ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m) hG
    haveI : IsOpenImmersion (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ := inferInstanceAs (IsOpenImmersion (𝟙 _))
    obtain ⟨g, rfl⟩ := ((isoOver_of_isOpenImmersion (O := ⊤) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ (fun x _ => ⟨x, rfl⟩)).bijective_pull
      (p := str₀ TF.X Z) (isLB_L₀ TF.X Z s) (W := ⊤) le_top le_top).2 g'
    refine ⟨g, fun y hy i hi => ?_, ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).bijective_pullOff (isLB_L₀ TF.X Z s)).1 ?_⟩
    · have h := hv y (fun h => hy ((hoff y).1 h)) (pIdx _ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ i) (mem_pIdx.2 hi)
      have e := H0.germ_pull (p := str₀ TF.X Z) (B := L₀ TF.X Z s) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top (pIdx _ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ i) y (memTop y) (mem_pIdx.2 hi) g
      erw [e] at h
      intro hu
      exact h (hu.map _)
    · rw [← hr]
      exact (H0.pull_restr (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off_eq.le g).trans (restr_pull (isLB_L₀ TF.X Z s) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ le_top le_top g).symm
end GlobalTheory.LogCanonicalReflexive
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logCanonical_divisor_refl : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str (tens (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z b).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs).mul ω₀.ω ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m) := by
  first | exact @_root_.GlobalTheory.LogCanonicalReflexive.logCanonical_refl_of_boundary | exact _root_.GlobalTheory.LogCanonicalReflexive.logCanonical_refl_of_boundary | (intros; apply _root_.GlobalTheory.LogCanonicalReflexive.logCanonical_refl_of_boundary <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogMeasureRatioBounded
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
namespace GlobalTheory.OneMeasureRatio
theorem log_covolume_ratio_le : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L), Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i μ 𝓕) ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  intro hP D Tu C t0 hC i P μ 𝓕 hF L hL
  have h0 := _root_.GlobalTheory.T.fundamentalDomain_volume_ne_zero hP D Tu C t0 hC i P μ 𝓕 hF
  have ht := _root_.GlobalTheory.T.quotient_measure_lt_top_of_finite_covolume hP D Tu C t0 hC i P μ 𝓕 hF
  have hv := _root_.MainStatements.Tam.Plug.tamagawa_pairs_compatible hP D Tu C t0 hC i P μ 𝓕 hF L hL
  have hd : ∀ τ, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L :=
    _root_.GlobalTheory.OneMeasDim.log_dimAt_le D i L hL
  have hd1 : ∀ τ, 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ := GlobalTheory.DimAtOne.one_le_dimAt D i
  have hvpos : 0 < (μ 𝓕).toReal := ENNReal.toReal_pos h0 ht
  have hdpos : ∀ τ, 0 < GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ := fun τ => zero_lt_one.trans_le (hd1 τ)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio
  rw [Real.log_mul hvpos.ne' (Finset.prod_pos fun τ _ => hdpos τ).ne',
    Real.log_prod (fun τ _ => (hdpos τ).ne')]
  have hsum : ∑ τ, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ∑ _τ : D.what₂.Tau, 3 / 2 * (D.R.r : ℝ) ^ 2 * L :=
    Finset.sum_le_sum fun τ _ => hd τ
  rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at hsum
  have hlog := log_r_add_three_le D L hL
  have hL0 : 0 ≤ L := le_trans (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) D.R.r; linarith)) hlog
  have hfr : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hlog hfr
  have h4 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L := mul_nonneg hfr hL0
  nlinarith
end GlobalTheory.OneMeasureRatio
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_measure_ratio_bounded : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L), Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i μ 𝓕) ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  first | exact @_root_.GlobalTheory.OneMeasureRatio.log_covolume_ratio_le | exact _root_.GlobalTheory.OneMeasureRatio.log_covolume_ratio_le | (intros; apply _root_.GlobalTheory.OneMeasureRatio.log_covolume_ratio_le <;> assumption)
end
end

