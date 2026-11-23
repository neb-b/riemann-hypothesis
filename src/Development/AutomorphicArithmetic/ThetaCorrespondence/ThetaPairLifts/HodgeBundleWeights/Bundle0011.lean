module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.Bundle0004
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.Bundle0002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0047
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0014
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfA
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfB
public import CompanionTheory.AutomorphicTheory.KrullDimension.TopologicalKrullDimModel
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0013
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0076
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0021
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightInvertiblePair
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2415
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDeterminantLinearisationEquivariantPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionTrivialOfFixedPointResidueField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ChowFormHeightComparison
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
theorem ChowFormHeightComparison₂.chow_form_height_bound (h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : PositivityTheory.UnitarySelfGeneration.ChowFormHeight :=
  ChowFormHeightComparison₂.CF.chowFormHeight_of_arch (ChowFormHeightComparison₂.CF.stArch ChowFormHeightComparison₂.CF.stPts (ChowFormHeightComparison₂.CF.stCharts ChowFormHeightComparison₂.CF.stPts)) _root_.GlobalTheory.CompanionTheory.Ar.Short.mahlerSection h.p4.arExists
theorem ChowFormHeightComparison₂.chow_form_height_comparison : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (t a : ℝ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a → a ≤ (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t)) :=
  fun h => _root_.PositivityTheory.UnitarySelfGeneration.weil_height_inequality (_root_.ChowFormHeightComparison₂.chow_form_height_bound h) h
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsFlatUnitBoundedAnyLevel
section
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlatAnyLevel
section Span
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
end Span
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
section Laws
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
end Laws
section Chain
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
section Cancel
open Filter Topology
variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c}
end Cancel
end Chain
end GlobalTheory.FlatAnyLevel
end
section Cover
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.FlatCore GlobalTheory.FlatLine GlobalTheory.AllWt in
theorem GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H), ∃ s i : Rul Y.d.Xo₂ Y.d.c₂, s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C) := by
  intro _ D T j Y e o hG _
  refine ⟨1, one_pos, fun Z τ => ?_⟩
  obtain ⟨A⟩ := GlobalTheory.FlatAnyLevel.archEx (GlobalTheory.FlatAnyLevel.neatUnf_of_good D T j Y e o hG) (xiR D) Z τ
  simp only [Nat.cast_one, one_smul]
  refine ⟨A.sig, A.inv, A.sig_mem, A.inv_mem, A.idem_sig, A.idem_inv, A.mul_inv, fun σ hσ => ?_⟩
  have hg : goodOf Y.d.c₂ σ = σ := if_pos hσ
  have hn := A.norm_inf σ
  rw [hg] at hn
  refine ⟨max (A.cInf σ) (A.cInf σ)⁻¹, fun z hz => ?_⟩
  have hs : homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0) A.sig z = A.cInf σ := by
    have := hn ▸ Set.mem_image_of_mem _ hz
    exact this
  obtain ⟨hdom, hlies⟩ := hz
  have hpos := A.cInf_pos σ
  have ht := tested_of_homN_ne (U := Y.U σ) (x := xiR D) hdom (hs.trans_ne hpos.ne')
  have hi := homN_idem (U := Y.U σ) (x := xiR D) hdom hlies ht
  have hm := homN_mul (Y.U σ) (xiR D) (G := wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)
    (G' := -(wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)) ⟨0, by simp [wtOf_snd]⟩ ⟨0, by simp [wtOf_snd]⟩ A.sig A.inv z hdom
  rw [add_neg_cancel, A.mul_inv, hi, hs] at hm
  refine ⟨hs ▸ le_max_left _ _, ?_⟩
  have : homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)) A.inv z = (A.cInf σ)⁻¹ := by
    field_simp
    linarith
  rw [this]; exact le_max_right _ _
end Cover
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
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_unit_exists_at_every_level : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H), ∃ s i : Rul Y.d.Xo₂ Y.d.c₂, s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C) := by
  first | exact @_root_.GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level | exact _root_.GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level | (intros; apply _root_.GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HeightLowerBoundOfRegulator
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
namespace ChowFormHeightComparison₂.SmallGenerators
end ChowFormHeightComparison₂.SmallGenerators
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem ChowFormHeightComparison₂.height_lower_bound_of_regulator : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t, ∀ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 → (∀ (k : L.B.ι) (x : X) (hx : x ∈ L.B.U k), (p x).asIdeal = ⊥ → GlobalTheory.Cartier.RegAt x (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) ^ (8 * i))) → ∀ (k : L.B.ι) (x : X) (hx : x ∈ L.B.U k), GlobalTheory.Cartier.RegAt x (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) ^ (8 * i)) := by
  intro _ D T j Y e o _ _ Z u X _ p L ψ s t hG hB _ _ hM i _ f hf w hw hgen k x hx
  by_cases hp : (p x).asIdeal = ⊥
  · exact hgen k x hx hp
  · exact ChowFormHeightComparison₂.SmallGenerators.reg_of_val hM (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) (8 * i)
      (fun la O h1 h2 => ChowFormHeightComparison₂.SmallGenerators.fin_small_gen Y.U Z _ hG.2.1 hG.2.2 hB la (O.valuation.comap ψ) h1 h2 (8 * i) f
        fun v hv => hf.1 la v hv) w hw k x hx hp
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeLineBundleRationalLinearEquivClass
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HodgeLin
theorem hodgeLineBundle_rationally_linear : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed (Xo := Xo) (c := c) → ∃ (δ : LB (X₀ TF.Y Z)) (hδ : δ.IsLB), CechPic.pull (π₀ TF.X Z) (cls δ hδ) = cls (L₀ TF.X Z (hodgeWt Dw)) (isLB_L₀ TF.X Z _) ∧ ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → RatLin ρ' (δ.pull φ) (LB.isLB_pull hδ φ) := by
  intro hP E _ _ _ H Dw l Xo c TF Z hpq hA hF
  obtain ⟨hI, -⟩ := GlobalTheory.BaseVar.isVariety_barComp E H Dw l Xo c TF Z hF
  obtain ⟨φ₀, f₀, hφ₀, hD⟩ := _root_.GlobalTheory.EigDiv.exists_detDiv E H Dw l Xo c TF Z
  obtain ⟨D, hDp, hDe⟩ := hD (GlobalTheory.HodgeLin.offCM H)
  refine ⟨toLB D, isLB_toLB D, ?_, ?_⟩
  · rw [hDp]
    have key : ∀ (L L' : LB (Y₀ TF.X Z)) (hL : L.IsLB) (hL' : L'.IsLB), L = L' → cls L hL = cls L' hL' := by
      rintro _ _ _ _ rfl; rfl
    exact key _ _ _ _ (congrArg (LL₀ TF.X Z) (GlobalTheory.HodgeLin.exOf_hodgeWt Dw)).symm
  · intro I g hI' hMb Γ _ _ ι ρ hU hAct X' _ φ ℓ ρ' hN hP' hO hj heq
    obtain ⟨G', _, ψ, act', m, hE⟩ := _root_.GlobalTheory.T.equivariant_linearization_pullback_compat hP E H Dw l Xo c TF Z hpq hA hF I g hI' hMb Γ ι ρ hU hAct X' φ ℓ ρ' hN hP' hO hj heq
    obtain ⟨v, hv⟩ := GlobalTheory.GenInterior.exists_j₀_eq_genericPoint E H Dw l Xo c TF Z
    have hd : IsDominant φ := ⟨by
      refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
      rw [← (genericPoint_spec (X₀ TF.Y Z)).def]
      exact closure_mono (Set.singleton_subset_iff.2 ⟨ℓ v, by rw [← Scheme.Hom.comp_apply, hj, hv]⟩)⟩
    haveI : Nonempty (V₀ TF.Y Z) := ⟨v⟩
    haveI : IsDominant ℓ := ⟨ℓ.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
    have hρ : ∀ γ, (ρ' γ).asIso.hom ≫ φ ≫ s₀ TF.Y Z = φ ≫ s₀ TF.Y Z := fun γ => by
      refine ext_of_isDominant ℓ ?_
      rw [← Category.assoc, ← heq, Category.assoc, ← Category.assoc ℓ φ, hj]
      exact hAct.1 γ
    exact _root_.GlobalTheory.HodgeLin.ratLin_pull E H Dw l Xo c TF Z φ₀ f₀ (GlobalTheory.HodgeLin.offCM H) D hφ₀ hDe Γ X' φ ρ' hd hρ G' ψ act' m hE
end GlobalTheory.HodgeLin
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeLineBundle_rational_linear_equiv_class : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed (Xo := Xo) (c := c) → ∃ (δ : LB (X₀ TF.Y Z)) (hδ : δ.IsLB), CechPic.pull (π₀ TF.X Z) (cls δ hδ) = cls (L₀ TF.X Z (hodgeWt Dw)) (isLB_L₀ TF.X Z _) ∧ ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → RatLin ρ' (δ.pull φ) (LB.isLB_pull hδ φ) := by
  first | exact @_root_.GlobalTheory.HodgeLin.hodgeLineBundle_rationally_linear | exact _root_.GlobalTheory.HodgeLin.hodgeLineBundle_rationally_linear | (intros; apply _root_.GlobalTheory.HodgeLin.hodgeLineBundle_rationally_linear <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IsNefHodgeBundleHeadWeight
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefHodge
section Step
open GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM)
open GlobalTheory.QCoh (pullbackSections)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z C : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (g : C ⟶ Z) (σ : E →+* ℂ)
  (f : ∀ M : MChart Y, Fin M.n → Γ(Lie Y.t.G, M.U))
end Step
theorem isNef_hodgeBundle_headWeight : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (τ : Psi H) (k : ℕ), k < Dw.p → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.headWt τ k)) := by
  intro hS _ hN E _ _ _ H Dw l Xo c TF Z _ τ k hk
  rw [NefStep.L₀_headWt TF.X Z τ k hk]
  exact isNef_stepEx hS hN.1 TF.X Z τ.1 (by rw [FlagMod.mult_of_mem τ]; exact hk)
end GlobalTheory.NefHodge
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_headWeight_nef : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (τ : Psi H) (k : ℕ), k < Dw.p → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.headWt τ k)) := by
  first | exact @_root_.GlobalTheory.NefHodge.isNef_hodgeBundle_headWeight | exact _root_.GlobalTheory.NefHodge.isNef_hodgeBundle_headWeight | (intros; apply _root_.GlobalTheory.NefHodge.isNef_hodgeBundle_headWeight <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IsNefHodgeBundleTailWeight
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefStep
theorem isNef_hodgeBundle_tailWeight : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (τ : Psi H) (k : ℕ), Dw.p ≤ k → k + 1 < Dw.p + Dw.q → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.tailWt τ k)) := by
  intro h _ hN E _ _ _ H Dw l Xo c TF Z _ τ k hk _
  letI := algebraΓOfHom (str₀ TF.X Z)
  rw [L₀_tailWt TF.X Z τ k hk]
  have hq := FlagMod.mult_conj (Dw := Dw) τ
  exact isNef_pull_LL_stepEx TF.X.F h hN.1 c.F (inc₀ TF.X Z) _ (by omega)
end GlobalTheory.NefStep
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_tailWeight_nef : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (τ : Psi H) (k : ℕ), Dw.p ≤ k → k + 1 < Dw.p + Dw.q → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.tailWt τ k)) := by
  first | exact @_root_.GlobalTheory.NefStep.isNef_hodgeBundle_tailWeight | exact _root_.GlobalTheory.NefStep.isNef_hodgeBundle_tailWeight | (intros; apply _root_.GlobalTheory.NefStep.isNef_hodgeBundle_tailWeight <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RegulatorLowerBound
section
section
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
namespace ChowFormHeightComparison₂.RegularPointExistence
theorem regulator_bound_all : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t, ∀ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 → ∀ (k : L.B.ι) (x : X) (hx : x ∈ L.B.U k), GlobalTheory.Cartier.RegAt x (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) ^ (8 * i)) := by
  intro _ D T j Y e o _ _ Z u X _ p L ψ s t hG hB _ _ hM i _ f hf w hw k x hx
  exact reg_of_val hM (8 * i) (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂))
    (fun la O h1 h2 => fin_small_gen Y.U Z _ hG.2.1 hG.2.2 hB la O.valuation h1 h2 (8 * i) f fun v hv => hf.1 la v hv)
    w hw k x hx
end ChowFormHeightComparison₂.RegularPointExistence
theorem ChowFormHeightComparison₂.regulator_lower_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t, ∀ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 → ∀ (k : L.B.ι) (x : X) (hx : x ∈ L.B.U k), (p x).asIdeal = ⊥ → GlobalTheory.Cartier.RegAt x (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) ^ (8 * i)) :=
  fun hP D T j Y e o hY hE Z u X _ p L ψ s t hG hB hN hd hM i hi f hf w hw k x hx _ =>
    _root_.ChowFormHeightComparison₂.RegularPointExistence.regulator_bound_all hP D T j Y e o hY hE Z u X p L ψ s t hG hB hN hd hM i hi f hf w hw k x hx
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToroidalFlagNonempty
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
namespace GlobalTheory.CompHS.TorFlagEx
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
theorem nonempty_torFlag_alt (hP : _root_.GlobalTheory.CovTop.Hypotheses'') :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ dimFlag Dw → Nonempty (TorFlag Xo c) := by
  intro E _ _ _ H Dw l Xo c hd
  obtain ⟨Y, hs, hb, hk⟩ := hP.p1 E H Dw (one_le_of_dimFlag hd) l Xo c
  exact torFlag_of_model Y hs hb hk
    (pushInvertible_of_hasTheta Y (GlobalTheory.ThetaNormal.hasTheta_of_smooth E H Dw (one_le_of_dimFlag hd) l Xo c Y hs))
end GlobalTheory.CompHS.TorFlagEx
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
theorem _root_.GlobalTheory.T.torFlag_nonempty_of_one_le_dimFlag : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ dimFlag Dw → Nonempty (TorFlag Xo c) := by
  first | exact @_root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt | exact _root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt | (intros; apply _root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt <;> assumption)
end
end

