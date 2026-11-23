module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0021
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0012
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0015
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.SupremumConstantLogBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringShiftPreservesGoodAt
section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovTop.ShiftGood
variable {D : D7} {T : Core D} {j : ℕ}
end GlobalTheory.CovTop.ShiftGood
namespace GlobalTheory.CovTop.ShiftGood
theorem covering_goodAt_shift : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : ℤ), Even n → (∀ τ, Antitone ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ)) → (∀ τ, 1 ≤ gap ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  intro hP D T hT j hp hq hf hj Y e o hY a n s hn hA hg
  obtain ⟨m, rfl⟩ := hn
  have hmul : ∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • (laOf (T.Q.Dw j) a (m + m) + s • hodgeWt (T.Q.Dw j))) 0) := by
    intro k
    refine (_root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hf hj Y e o hY _ (fun τ => ?_) (fun τ => ?_)).1
    · intro x y hxy
      simp only [Pi.smul_apply]
      exact nsmul_le_nsmul_right (hA τ hxy) _
    · have := hg τ
      simp only [Pi.smul_apply]
      unfold gap at this ⊢
      split_ifs at this ⊢ with h1
      · simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at this ⊢
        have hk : (1 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos k
        rw [← mul_sub]
        exact this.trans (le_mul_of_one_le_left (by linarith) hk)
      · exact this
  refine goodAt_of_exZ hY ?_ ⟨hasGram_nrm_of_good D T.toCore j Y e o hY _,
    _root_.GlobalTheory.T.shifted_weight_lattice_fg hP D T hT j hp hq hf hj Y e o hY _ hA hg hmul m,
    _root_.GlobalTheory.T.weight_lattice_spanned_by_weights hP D T hT j hp hq hf hj Y e o hY _ hA hg hmul m⟩
  rw [← two_mul, GlobalTheory.CovTop.Model.exZ_shiftG]
  rfl
end GlobalTheory.CovTop.ShiftGood
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_shift_preserves_goodAt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : ℤ), Even n → (∀ τ, Antitone ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ)) → (∀ τ, 1 ≤ gap ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  first | exact @_root_.GlobalTheory.CovTop.ShiftGood.covering_goodAt_shift | exact _root_.GlobalTheory.CovTop.ShiftGood.covering_goodAt_shift | (intros; apply _root_.GlobalTheory.CovTop.ShiftGood.covering_goodAt_shift <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleDominatesOfLargeWeight
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
namespace GlobalTheory.HodgeDominates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
theorem exists_weight_hodgeBundle_dominates : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : AllWt.Weight Dw, ∀ y ∈ U₀ TF.X Z, ∀ A : LB TF.Y.X, A.IsLB → ∃ (m : ℕ) (s : (LB.div (lbPow (L₀ TF.X Z χ) m) (A.pull (inc₀ TF.X Z ≫ TF.X.π))).Sec), 0 < m ∧ y ∈ nonzeroLocus s := by
  intro hP _ hS hF E _ _ _ H Dw l Xo c TF Z _
  obtain ⟨ω, hω, e, h⟩ := exists_lb_dominates (E := E) (H := H) (Dw := Dw) (l := l) (Xo := Xo) (c := c) hP.p22 hS hF TF
  refine ⟨FlagMod.mu0 Dw, fun y hy A hA => ?_⟩
  obtain ⟨w, hw⟩ : ∃ w, TF.Y.j w = (inc₀ TF.X Z ≫ TF.X.π) y := hy
  obtain ⟨m, hm, s, hs⟩ := h w A hA
  have hD := LB.isLB_div (isLB_lbPow hω m) hA
  have hL := isLB_L₀ TF.X Z (FlagMod.mu0 Dw)
  have hT := LB.isLB_div (isLB_lbPow hL m) (pull_isLB hA (inc₀ TF.X Z ≫ TF.X.π))
  have e' : cls _ hL = CechPic.pull (inc₀ TF.X Z ≫ TF.X.π) (cls ω hω) := by
    rw [CechPic.pull_comp, ← e]
    exact cls_pull (TF.X.isLB_Llam _) _ _
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hT (pull_isLB hD (inc₀ TF.X Z ≫ TF.X.π))
    ((cls_eq_iff hT (pull_isLB hD _)).1 (by
      rw [cls_div (isLB_lbPow hL m) (pull_isLB hA _), cls_lbPow hL, cls_pull hA, cls_pull hD,
        cls_div (isLB_lbPow hω m) hA, cls_lbPow hω, map_sub, map_nsmul, e'])) (lbSecPull _ s _)
  refine ⟨m, t, hm, ?_⟩
  rw [ht, nonzeroLocus_lbSecPull]
  exact (hw ▸ hs : (inc₀ TF.X Z ≫ TF.X.π) y ∈ nonzeroLocus s)
end GlobalTheory.HodgeDominates
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
theorem _root_.GlobalTheory.T.hodgeBundle_dominates_of_large_weight : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : AllWt.Weight Dw, ∀ y ∈ U₀ TF.X Z, ∀ A : LB TF.Y.X, A.IsLB → ∃ (m : ℕ) (s : (LB.div (lbPow (L₀ TF.X Z χ) m) (A.pull (inc₀ TF.X Z ≫ TF.X.π))).Sec), 0 < m ∧ y ∈ nonzeroLocus s := by
  first | exact @_root_.GlobalTheory.HodgeDominates.exists_weight_hodgeBundle_dominates | exact _root_.GlobalTheory.HodgeDominates.exists_weight_hodgeBundle_dominates | (intros; apply _root_.GlobalTheory.HodgeDominates.exists_weight_hodgeBundle_dominates <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.PlugPairs
section
section
noncomputable section
namespace MainStatements.Tam.Plug
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
theorem tamagawa_pairs_compatible : _root_.GlobalTheory.T.CovolumeRatioIdentity := _root_.MainStatements.Tam.Plug.tamagawa_number_upper_bound
theorem tamagawa_pairs_product : _root_.GlobalTheory.T.FieldOfDefinitionDescentProp := fun _ => low
section
open ReciprocityTheory.L2DbarEstimates GlobalTheory.SupConstSize Real
end
end MainStatements.Tam.Plug
end
end
end

