module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0023
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0011
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0028
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
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
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0024

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCuspValueNeZeroLowLevel
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
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.LowNonzero
theorem exists_cusp_value_ne_zero_low_level (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hT : GlobalTheory.Published.ToroidalChartsForFan)
    (hN : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7}
    {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hD : 1 ≤ FlagTan.dimFlag (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j))
    (hla : GapGe (((FlagTan.dimFlag (T.Q.Dw j) + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap (T.Q.Dw j))) :
    ∃ f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0), f ≠ 0 := by
  have hP1 := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨TF⟩ := _root_.GlobalTheory.T.torFlag_nonempty_of_one_le_dimFlag hP1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have hfree := _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP1 hG hQ hP.q15 hP.q16 hS hT hN _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ hla
    ⟨_root_.GlobalTheory.CompHS.cusp_extends_comp _ _ _ Y _ _ hY hf Z TF _, vanBd_le_space _ _ _ Y _ _ hY hf Z TF _⟩
  haveI := (GlobalTheory.T.flagSpace_component_smooth_projective_connected _ _ _ _ _ _ TF Z hY.geo).2.2
  haveI : ConnectedSpace (Y₀ TF.X Z) := GeometricallyConnected.connectedSpace_of_subsingleton (str₀ TF.X Z)
  obtain ⟨s, hs, hs0⟩ := ne_zero_of_noBase hfree (dense_U₀ TF.X Z).nonempty
  refine ⟨(ofSpace TF.X Z Y.U _ ⟨s, hs⟩).1, (ofSpace TF.X Z Y.U _ ⟨s, hs⟩).2, fun h0 => hs0 ?_⟩
  have h1 : ofSpace TF.X Z Y.U _ ⟨s, hs⟩ = 0 := Subtype.ext h0
  exact congrArg Subtype.val (ofSpace_injective TF.X Z Y.U _ (h1.trans (map_zero _).symm))
end GlobalTheory.CovTop.LowNonzero
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
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsWeightHodgeBundleGenerated
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
theorem exists_weight_sections_nonvanishing : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)), WtBig P → (∀ i ≤ P.T, Y.GoodAt (wtOf _ (P.wt i) 0)) → ∃ (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif), Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict := by
  intro hP hGD hQ hN hPr hS hT hL D T j Y e o hY hf Z P hB hG
  have hD := hB.one_le
  obtain ⟨TF⟩ := @_root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt hP _ _ _ _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have hV := @GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ _ _ _ TF Z hY.geo
  have hC : ∀ la, CuspIso TF.X Z Y.U la := fun la =>
    ⟨_root_.GlobalTheory.CompHS.cusp_extends_comp D T j Y e o hY hf Z TF la, @GlobalTheory.HSApp.vanBd_le_space D T j Y e o hY hf Z TF la⟩
  have hW := GlobalTheory.HSApp.gaps_of_wtBig _ _ _ P hB
  have h₁ : FreeOnOpen TF.X Z Y.U P.u₁ :=
    _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP hGD hQ hN hPr hS hT hL _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ (hW _ (by simp)).2 (hC _)
  have h₂ : FreeOnOpen TF.X Z Y.U P.u₂ :=
    _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP hGD hQ hN hPr hS hT hL _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ (hW _ (by simp)).2 (hC _)
  obtain ⟨R⟩ := GlobalTheory.CompHS.nonempty_choice hPr _ _ _ _ _ _ TF Z _ Y.U P hV h₁ h₂
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    by_contra h
    have h0 : (T.Q.Dw j).p + (T.Q.Dw j).q = 0 := by omega
    have : dimFlag (T.Q.Dw j) = 0 := by simp [dimFlag, h0]
    omega
  obtain ⟨ω⟩ := @GlobalTheory.CompHS.canId_nonempty hP.p5 _ _ _ _ _ _ _ _ _ TF.Y TF.X Z R.toModif
    (fun K _ _ y => _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_iso hP hGD _ _ _ _ _ _ K y hpq)
  obtain ⟨w₁, w₂⟩ := _root_.GlobalTheory.T.hodge_bundle_degree_squeeze hP hGD _ _ _ _ _ _ TF Z _ Y.U P R ω hY.geo h₁
  exact ⟨TF, R, ω,
    { conn := GlobalTheory.CompHS.Modif.geometricallyConnected_str _ _ _ _ _ R.toModif hV.1 hV.2.2 (dense_U₀ _ _)
      one_le := hD
      le_T := hB.le_T
      ext₁ := (hC _).1
      ext₂ := (hC _).1
      free₁ := h₁
      free₂ := h₂
      good := fun i hi => GlobalTheory.HSApp.goodOn_of_goodAt D T j Y e o hY hf Z _ (hG i hi)
      global_le := fun i _ => w₁ i (hC _)
      le_global := w₂ (hC _) }⟩
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
theorem _root_.GlobalTheory.T.exists_weight_hodge_bundle_generated : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)), WtBig P → (∀ i ≤ P.T, Y.GoodAt (wtOf _ (P.wt i) 0)) → ∃ (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif), Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict := by
  first | exact @_root_.GlobalTheory.HSApp.exists_weight_sections_nonvanishing | exact _root_.GlobalTheory.HSApp.exists_weight_sections_nonvanishing | (intros; apply _root_.GlobalTheory.HSApp.exists_weight_sections_nonvanishing <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightPrincipalisationBound
section
section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option autoImplicit false
namespace GlobalTheory.DegVal
theorem birOn_of_weight_gaps_large : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) := by
  intro hX hG hQ hS hP hN hPr D T hT j hp hq Y e o hY u hu Z
  obtain ⟨f₀, hf₀, hne⟩ := _root_.GlobalTheory.T.exists_centre_cusp_generic_value_ne_zero hX hG hQ hS hP hN hPr D T hT j hp hq Y e o hY u hu Z
  obtain ⟨σ, A, B, hA, hB, hBA, hBr, hAtop, hsep⟩ := _root_.GlobalTheory.T.cusp_values_separate_generic_points hX hG hQ hS hP hN hPr D T hT j hp hq Y e o hY u hu Z
  have key := exists_mul_eq_of_generic_unique_complexPoint _ _ σ A B hA hB hBA hsep
  refine ⟨fun h => hne ?_, eq_top_iff.2 ?_⟩
  · have := LinearMap.congr_fun h ⟨f₀, hf₀⟩
    simpa [genPoint] using this
  · rw [← hAtop, IntermediateField.adjoin_le_iff]
    intro a ha
    obtain ⟨p, hp', q, hq', hq0, hpq⟩ := key a ha
    rw [eq_div_of_mul_eq hq0 hpq]
    exact IntermediateField.div_mem _ (hBr p hp') (hBr q hq')
end GlobalTheory.DegVal
end

section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) := by
  first | exact @_root_.GlobalTheory.DegVal.birOn_of_weight_gaps_large | exact _root_.GlobalTheory.DegVal.birOn_of_weight_gaps_large | (intros; apply _root_.GlobalTheory.DegVal.birOn_of_weight_gaps_large <;> assumption)
end
end

