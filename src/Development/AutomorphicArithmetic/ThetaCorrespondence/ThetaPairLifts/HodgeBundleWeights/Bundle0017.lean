module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightRuleReadsNonvanishingDetSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuOntoC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
public import Development.WeilBound.CoreStatements.NefModelVolumes.NV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ArchimedeanSectionIntegralFrame
section
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
namespace GlobalTheory.FlatCore.Bdry
theorem nval_evI_eq_zero_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0 := by
  intro hP hQ2 E _ _ _ H Dw l Xo c r U x hL Z τ s T io y₀ hv hZ
  obtain ⟨s₀, hs₀⟩ := _root_.GlobalTheory.T.boundary_isUnit_at_eqChar_points hP hQ2 E H Dw l Xo c r U x hL Z τ ⟨s⟩
  obtain ⟨a, ha, hsa⟩ := GlobalTheory.T.constLengthArchSection_eq_smul_of_same_weight E H Dw l Xo c r U x hL.unf hL.geo Z (flatWt Dw τ) s₀ s
  have h0 : io a ≠ 0 := (map_ne_zero io).2 ha
  rw [hsa, evI_smul, nval_mul, hs₀ T io y₀ hv hZ, nval_of_ne h0, hv a ha]
  simp
end GlobalTheory.FlatCore.Bdry
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_section_integral_frame_of_laws : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0 := by
  first | exact @_root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt | exact _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt | (intros; apply _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatAtOfSplitCovering
section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.FlatLine GlobalTheory.FlatTw
namespace GlobalTheory.FlatSplit
section Congr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}
end Congr
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ)
end Weights
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem flat_at_of_split_covering (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i) (hY : GoodCov p i Y) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems)
    (hDG : DeepGoodAt p i Y)
    (hc : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict ∧ (∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q) ∧
      FlatExists Y.U (xiR D) ∧
      (∀ τ, |c1 Y.U (xiR D) τ + (((dat p i).p : ℝ) - (dat p i).q) / 2 * (ofRecord D L p.Del p.h0).logOm| ≤
        3 * (dat p i).q * L.sc.L) ∧
      logSum (badPrimes p.T.Q.H Y.d.l₂) ≤ 40 * L.sc.L)
    {CA PP PP' A : ℝ} (hA : AnchorAt p i CA) (hW : WtNum p i PP) (hH : HostNum D L PP' A 0) :
    FlatAt p i Y (11 * CA + 83) := by
  obtain ⟨hcx, hgood, hflat, hc1, hlog⟩ := hc
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, by have := i.2; omega⟩
  have hUn := _root_.GlobalTheory.T.unramified_points_of_deep_cover hP D p.T ((i : ℕ) + 1) Y _ _ p.fw.laws hj hY.1
  have hrank : 1 ≤ (dat p i).p + (dat p i).q := Inhab.rank_pos p.T.toCore p.fw.laws.pins ((i : ℕ) + 1) hj
  have hev : Even (p.κ i).n := hW.dom.2
  have hFL := ((GlobalTheory.T.flatLine_thetaRoot_twist_twistingSection hP.p5 D p.T.Q.H (dat p i) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (fun _ => D.sp.W ((i : ℕ) + 1))
    Y.dict hcx hY.1.geo hrank hgood hflat hUn (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1))
    ((p.κ i).n / 2)).2 (uM p i) 0).2 hDG.2.2.2.1
  obtain ⟨-, hrk, hdeg⟩ := hFL
  have hex : exZ (dat p i) (Gs p i (-(cZero D ((i : ℕ) + 1)))) = exZ (dat p i)
      (wtOf (dat p i) (uM p i + parWt (dat p i) (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1)))
        ((0 : ℤ) + (((p.κ i).n / 2 : ℕ) : ℤ))) := by
    have := exZ_shift_neg (dat p i) (wtA (p.κ i)) ((p.κ i).n / 2) (D.R.k - 1) (cZero D ((i : ℕ) + 1))
    rwa [Nat.two_mul_div_two_of_even hev] at this
  have hcg := congr_exZ Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict hY.1.unf hex
  have hR0 := hDG.2.2.2.2.1
  unfold FlatAt
  have e1 : Y.mu (Gs p i (-(cZero D ((i : ℕ) + 1)))) = slopeW_sq Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict
      (wtOf (dat p i) (uM p i + parWt (dat p i) (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1)))
        ((0 : ℤ) + (((p.κ i).n / 2 : ℕ) : ℤ))) := hcg.2.2
  have e2 : Y.rk (Gs p i (-(cZero D ((i : ℕ) + 1)))) = rankW Y.U (wtOf (dat p i) (uM p i) 0) := hcg.2.1.trans hrk
  have hR : (0 : ℝ) < (rankW Y.U (wtOf (dat p i) (uM p i) 0) : ℝ) := by rw [← e2]; exact_mod_cast hR0
  rw [degW_eq, degW_eq, hrk] at hdeg
  rw [e1]
  have hb1 : 1 ≤ L.sc.b := by have := hH.room; rwa [Real.rpow_zero] at this
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hL := hH.big.2.1
  have hll := hH.big.2.2.2
  have k1 : (1 : ℝ) ≤ D.R.f * D.R.m := by nlinarith
  have k2 : (1 : ℝ) ≤ D.R.f * D.R.m * L.sc.L := by nlinarith
  have k3 : (1 : ℝ) ≤ D.R.f * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) := by nlinarith
  have k4 : (1 : ℝ) ≤ D.R.f * D.R.m * L.sc.b * Real.log (Real.log L.sc.x) := by nlinarith
  have hbE : L.sc.b ≤ unitE p := by
    rw [hW.unit]; nlinarith [mul_le_mul_of_nonneg_left k3 (by linarith : (0 : ℝ) ≤ L.sc.b)]
  have hLE : L.sc.L ≤ unitE p := by
    rw [hW.unit]; nlinarith [mul_le_mul_of_nonneg_left k4 (by linarith : (0 : ℝ) ≤ L.sc.L)]
  have hfr : (((Module.finrank ℚ D.host.E / 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℝ)) = (D.R.f : ℝ) * D.R.r := by
    rw [hH.deg, hW.sig.2.2, Nat.mul_div_cancel_left _ (by norm_num)]; push_cast; ring
  have hm : 2 * ((((p.κ i).n / 2 : ℕ) : ℝ)) ≤ (D.R.nV : ℝ) := by
    have := Nat.mul_div_le (p.κ i).n 2
    rw [hW.cols] at this
    rw [hW.cols]; exact_mod_cast (by omega : 2 * (D.R.nV / 2) ≤ D.R.nV)
  have num := twice_twist_ge (fun τ => (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)) (c1 Y.U (xiR D))
    (((dat p i).p : ℝ) - (dat p i).q) ((dat p i).q : ℝ) (ofRecord D L p.Del p.h0).logOm L.sc.L L.sc.b (unitE p) (mainT p i) CA
    (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E) ((((p.κ i).n / 2 : ℕ) : ℝ))
    (((Module.finrank ℚ D.host.E / 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℝ)) (D.R.nV : ℝ)
    (logSum (badPrimes p.T.Q.H Y.d.l₂)) hc1 hA.1 hA.2.1 (Nat.cast_nonneg _) (lrd_le hH) hL hm (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by rw [hfr]; exact hA.2.2) hbE hLE hlog
  rw [← mul_add] at hdeg
  have key := le_of_mul_le_mul_left hdeg hR
  show slopeW_sq Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict (wtOf (dat p i) (uM p i) 0) - mainT p i -
    (11 * CA + 83) * unitE p ≤ _
  linarith
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
end GlobalTheory.FlatSplit
end
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.InverseOfFlatUnitIsIntegral
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
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.FlatUnitInt
theorem flat_unit_inverse_integral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (n : ℤ) (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H) (s i : Rul Y.d.Xo₂ Y.d.c₂), (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C)) → ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • i) :=
  _root_.GlobalTheory.FlatDenom.unit_pow_clears_denominator_flat_model
end GlobalTheory.FlatUnitInt
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
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_of_flat_unit_isIntegral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (n : ℤ) (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H) (s i : Rul Y.d.Xo₂ Y.d.c₂), (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C)) → ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • i) := by
  first | exact @_root_.GlobalTheory.FlatUnitInt.flat_unit_inverse_integral | exact _root_.GlobalTheory.FlatUnitInt.flat_unit_inverse_integral | (intros; apply _root_.GlobalTheory.FlatUnitInt.flat_unit_inverse_integral <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LocalUnitMapSurjective
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
theorem PositivityTheory.Xj7N.local_unit_map_surjective : PositivityTheory.Xj7N.NV → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : GlobalTheory.CompHS.TorFlag Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ P ∈ holSub (Y.U σ).X (modelWt (Y.U σ) (wtOf (T.Q.Dw j) u 0)), ∃ (m : ℕ) (as : Fin m → ℂ) (fs : Fin m → Rul Y.d.Xo₂ Y.d.c₂), (∀ i, fs i ∈ GlobalTheory.CompanionTheory.Ar.OntoDef.extVanZ TF.X (exOf (T.Q.Dw j) u 0)) ∧ ∀ w ∈ framesOn (Y.U σ) Z, P w.1 w.2 = ∑ i, as i * rdU (Y.U σ) (fs i) w.1 w.2 := by
  intro hNV _ D T j Y e o hY _ Z TF u _ hB σ hσ P hP
  have hU := hY.unf σ hσ
  obtain ⟨κ⟩ := GlobalTheory.HSApp.VanishingBound.keySec D T j Y e o hY σ hσ
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    have hr := hU.1
    have h1 : 1 ≤ D.R.r := by
      have := D.R.two_le_m
      unfold Formalism.BasicNotions.Ranks.r
      omega
    omega
  have hdec : ∀ (τ : D.host.E →+* ℂ) (i j' : ℕ), i ≤ j' → j' < (T.Q.Dw j).mult τ →
      (wtOf (T.Q.Dw j) u 0).1 (τ, j') ≤ (wtOf (T.Q.Dw j) u 0).1 (τ, i) := by
    have hne : ∀ (τ : D.host.E →+* ℂ) (m : ℕ), m + 1 < (T.Q.Dw j).mult τ →
        (wtOf (T.Q.Dw j) u 0).1 (τ, m + 1) ≤ (wtOf (T.Q.Dw j) u 0).1 (τ, m) := fun τ m hm => by
      by_contra hlt
      refine hB.1 (LinearMap.ext fun f => ?_)
      have h0 : (f : Rul Y.d.Xo₂ Y.d.c₂) = 0 :=
        GlobalTheory.NonDomVanish.eq_zero_of_lt f.2.1.1 τ ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl (not_le.1 hlt)
      rw [show f = 0 from Subtype.ext h0, map_zero, map_zero]
    intro τ i j' hij hj'
    induction j', hij using Nat.le_induction with
    | base => exact le_refl _
    | succ n hn ih => exact (hne τ n hj').trans (ih (by omega))
  obtain ⟨m, as, fs, h1, h2⟩ := PositivityTheory.UnitarySelfGeneration.VuOnto.exists_comb hσ hU TF (e := exOf (T.Q.Dw j) u 0) rfl
    (PositivityTheory.UnitarySelfGeneration.VuOnto.tw_of_dec hσ hU κ (fun a n hD => hNV _ _ _ _ _ _ σ hpq a n hD) (wtOf (T.Q.Dw j) u 0) rfl hdec)
    (GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ hP)
  exact ⟨m, as, fs, h1, fun w hw => h2 w.1 w.2 hw.1⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RefExpPadicValLeShiftOfWeightFree
section
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.RefSum.WFree
theorem refExp_padicVal_le_shift_of_weightFree : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → FlatExists Y.U (xiR D) → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (w₀ : Psi T.Q.H → ℤ) (m : ℕ) (cst : ℝ) (q : ℕ), q.Prime → refExp_vp Y.U cst (wtOf (T.Q.Dw j) u 0) q ≤ refExp_vp Y.U cst (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m) q + (((if q ∈ badPrimes T.Q.H Y.d.l₂ then (m * (D.R.f * D.R.r) * (different_vp D.host.E q : ℝ) + 1) else 0 : ℝ)) : EReal) := by
  intro hP D T j Y e o hT hj hY _ _ hF u w₀ m cst q hq
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hL := _root_.GlobalTheory.LawsDeep.laws_deep D T j Y e o hT hj hY
  have hp := hT.pins
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2
    simp only [Ranks.sigW, Ranks.r]; omega
  have h2 := two_mul_sum_mult (T.Q.Dw j)
  rw [StandardLattice.finrank_host D, hr, mul_assoc] at h2
  exact refExp_vp_le_of_laws hL (_root_.GlobalTheory.UnramPoint.unramPts hP.q18 hP.q1 hP.p5 _ _ _ _ _ _ hL.pos) hF u w₀ m cst hq
    (by exact_mod_cast Nat.eq_of_mul_eq_mul_left two_pos h2)
end GlobalTheory.RefSum.WFree
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reference_exponent_valuation_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → FlatExists Y.U (xiR D) → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (w₀ : Psi T.Q.H → ℤ) (m : ℕ) (cst : ℝ) (q : ℕ), q.Prime → refExp_vp Y.U cst (wtOf (T.Q.Dw j) u 0) q ≤ refExp_vp Y.U cst (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m) q + (((if q ∈ badPrimes T.Q.H Y.d.l₂ then (m * (D.R.f * D.R.r) * (different_vp D.host.E q : ℝ) + 1) else 0 : ℝ)) : EReal) := by
  first | exact @_root_.GlobalTheory.RefSum.WFree.refExp_padicVal_le_shift_of_weightFree | exact _root_.GlobalTheory.RefSum.WFree.refExp_padicVal_le_shift_of_weightFree | (intros; apply _root_.GlobalTheory.RefSum.WFree.refExp_padicVal_le_shift_of_weightFree <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShortSpanCompositionClosed
section
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
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
namespace GlobalTheory.ShortSpanComp
end GlobalTheory.ShortSpanComp
namespace GlobalTheory.ShortSpanComp
set_option maxHeartbeats 2000000 in
theorem short_span_comp_mem : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 10 * Lb → ∀ Z, ∃ s : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)), s ⊆ (latOn Y.U Z (wtOf (T.Q.Dw j) la 0) : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0) σ y ≤ Real.exp (C * (((D.R.f : ℝ) * D.R.r * Lb) ^ 3 * (∑ τ, ∑ k, |(la τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * Lb) ^ 5)) := by
  intro hP
  obtain ⟨CG, hCG0, hGM⟩ := _root_.GlobalTheory.CovGmin.minimal_level_cover_is_good hP
  obtain ⟨CB, hCB0, hBad⟩ := _root_.GlobalTheory.T.log_sum_bad_primes_bound_of_covering hP
  refine ⟨11 * CG + CB + 500, by positivity, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hEs hfr ho c₁ hc₁ hc₁b la hanti hgap hla Z
  have hL := GlobalTheory.LawsDeep.laws_deep D T j Y e o hT hj hY
  have hrk : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    obtain ⟨h1, h2, -⟩ := hT.pins.2.2.2 j hj
    obtain ⟨hj1, hj2⟩ := hj
    rw [h1, h2]; unfold Formalism.BasicNotions.Ranks.sigW Formalism.BasicNotions.Ranks.r; simp only; omega
  have hcard : Nat.card (Psi T.Q.H) = D.R.f := by
    have hpin := hT.pins.1
    have hb : Function.Bijective (fun t : D.what₂.Tau => (⟨DV.tauEmb D t, hpin.2.2.2 t⟩ : Psi T.Q.H)) :=
      ⟨fun s t h => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val h), fun τ => by
        obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hpin τ.1 τ.2
        exact ⟨t, Subtype.ext ht.symm⟩⟩
    rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, D.what₂.card_Tau]
  have hf1 : 1 ≤ D.R.f := by
    have hn : 0 < D.R.ord := D.R.ord_pos
    show 1 ≤ 2 * D.R.ord
    omega
  have hr1 : 1 ≤ D.R.r := by omega
  set m : ℕ := D.R.f * D.R.r + 1 with hm
  have hgap' : ∀ τ, ((2 * (4 * m) + 2 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1) := fun τ => by
    have h := hgap τ
    have e8 : 2 * (4 * m) + 2 = 8 * D.R.f * D.R.r + 10 := by rw [hm]; ring
    rw [e8]; exact h
  obtain ⟨a, hDom, hlaOf, hbig⟩ := GlobalTheory.T.exists_thetaWeight_exponents_of_large_gap D.host.E T.Q.H (T.Q.Dw j) (4 * m) la hp hanti hgap'
  have hn2 : 2 * (4 * m) / 2 = 4 * m := by omega
  set n₀ : Psi T.Q.H → ℤ := fun τ => 1 + ((4 * m : ℕ) : ℤ) - la τ ⟨(T.Q.Dw j).p - 1, by omega⟩ with hn₀
  obtain ⟨hsizeK, hN0⟩ := _root_.GlobalTheory.spanShortSize D.host.E T.Q.H (T.Q.Dw j) a (2 * (4 * m)) la n₀ hp hlaOf
    (fun τ => by rw [hn2])
  have hrkR : (((T.Q.Dw j).p + (T.Q.Dw j).q : ℕ) : ℝ) = D.R.r := by exact_mod_cast hrk
  rw [hrkR, hcard, hn2] at hsizeK
  rw [hcard, hn2] at hN0
  have hcast : ((4 * m : ℕ) : ℝ) + 1 = 4 * ((D.R.f : ℝ) * D.R.r + 1) + 1 := by rw [hm]; push_cast; ring
  rw [hcast] at hsizeK hN0
  have hS : ∃ N : ℕ, (∑ τ, ∑ k, |(la τ k : ℝ)|) = N :=
    ⟨∑ τ, ∑ k, (la τ k).natAbs, by push_cast [Nat.cast_natAbs]; rfl⟩
  have hsz0 : 0 ≤ sizeK (T.Q.Dw j) a (2 * (4 * m)) := sizeK_nonneg _ _ _
  have hsz : Real.log (sizeK (T.Q.Dw j) a (2 * (4 * m))) ≤ 20 * Lb :=
    GlobalTheory.T.log_le_twenty_mul_of_bounds D.R.f D.R.r Lb _ _ (by exact_mod_cast hf1) (by exact_mod_cast hr1) hLb hfr hS hla hsz0
      (by rw [mul_comm (D.R.r : ℝ) (D.R.f : ℝ)] at hsizeK ⊢; linarith)
  obtain ⟨s₀, hs₀lat, hs₀span, hs₀bd⟩ := hGM D T hT j hp hq hE hj Y e o hY Lb hLb hM hEs hfr ho a (2 * (4 * m))
    hDom ⟨4 * m, by ring⟩ (by rw [hm]; nlinarith) hbig hsz
  obtain ⟨hKey, hth⟩ := GlobalTheory.T.exists_keyUnit_pow_twistingSection_on_component D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) hL.unf hL.xi hL.geo
    hL.pos hL.good
  obtain ⟨t₁, ht₁lo, ht₁c⟩ := hth Z m
  have hUn := _root_.GlobalTheory.T.unramified_points_of_deep_cover hP D T j Y e o hT hj hY
  have hPts : HasPts Y.U Z := GlobalTheory.FlatLine.hasPts Y.U hL.pos hL.good hL.unf Z
  obtain ⟨t₂, ht₂lo, ht₂c⟩ := _root_.GlobalTheory.FlatShort.exists_short_flat_section D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D)
    (badPrimes T.Q.H Y.d.l₂) hKey hL.unf hL.pos badPrimes_prime hUn c₁ hc₁ Z hPts (fun τ => -n₀ τ)
  have hW := cuspW_laOf (Dw := T.Q.Dw j) Y.U hL.unf a (2 * (4 * m)) ⟨4 * m, by ring⟩
  have hs₀c : Subtype.val '' s₀ ⊆ (cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m)))
      ((2 * (4 * m) / 2 : ℕ) : ℤ)) : Set (Rul Y.d.Xo₂ Y.d.c₂)) := by
    rintro _ ⟨f, -, rfl⟩
    rw [SetLike.mem_coe, ← hW]
    exact f.2
  have hs₀i : ∀ f ∈ Subtype.val '' s₀, ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v f := by
    rintro _ ⟨f, hf, rfl⟩
    exact (AllWt.mem_supLat).1 (hs₀lat hf)
  have hs₀s : cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m)))
      ((2 * (4 * m) / 2 : ℕ) : ℤ)) ≤ Submodule.span Y.d.c₂.F (Subtype.val '' s₀) := by
    rw [← hW]
    intro g hg
    set_option synthInstance.maxHeartbeats 400000 in
    have h1 : (⟨g, hg⟩ : Y.V (wtZ a (2 * (4 * m)))) ∈ Submodule.span Y.d.c₂.F s₀ := by
      rw [hs₀span]; exact Submodule.mem_top
    exact Submodule.apply_mem_span_image_of_mem_span (Y.V (wtZ a (2 * (4 * m)))).subtype h1
  have hlo : ∀ w, 0 ≤ (t₁.mul t₂).lo w := fun w => add_nonneg (ht₁lo w) (ht₂lo w)
  have hGG : wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m))) ((2 * (4 * m) / 2 : ℕ) : ℤ) +
      (wtOf (T.Q.Dw j) 0 (-(4 * (m : ℤ))) + wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => -n₀ τ) 0) =
      wtOf (T.Q.Dw j) la 0 := by
    rw [← AllWt.wtOf_add, ← AllWt.wtOf_add, hlaOf, hn2]
    congr 1
    · funext τ k; simp [parWt]
    · push_cast; ring
  have key := _root_.GlobalTheory.SpanShortProd.exists_span_mul_twSec D T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z _ _
    (t₁.mul t₂) hL.unf (AllWt.even_wtOf _ _) hlo _ hs₀c hs₀i hs₀s
  rw [hGG] at key
  obtain ⟨s, hslat, hsspan, hsbd⟩ := key
  refine ⟨s, hslat, hsspan, fun y hy σ => ?_⟩
  obtain ⟨f, ⟨f₀, hf₀, rfl⟩, hfbd⟩ := hsbd y hy
  have hP1 : petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m)))
      ((2 * (4 * m) / 2 : ℕ) : ℤ)) σ (f₀ : Rul Y.d.Xo₂ Y.d.c₂) ≤
      Real.exp (CG * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a (2 * (4 * m))) := by
    rw [petOn_congr Y.U (xiR D) (fun _ => D.sp.W j) Y.dict hL.unf Z
      (exZ_laOf (T.Q.Dw j) a (2 * (4 * m)) ⟨4 * m, by ring⟩)]
    exact (hs₀bd f₀ hf₀ σ).2 Z
  have hc1 : t₁.cInf σ ≤
      Real.exp (((D.R.f : ℝ) * D.R.r + 1) * (2 * ((D.R.f : ℝ) * D.R.r) * Real.log (2 * Real.pi))) := by
    have h := ht₁c σ
    have hNR : ((Nat.card (Psi T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℝ) = (D.R.f : ℝ) * D.R.r := by
      rw [hcard, hrk]; push_cast; ring
    rw [hNR, Real.log_le_iff_le_exp (t₁.cInf_pos σ)] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [hm]; push_cast; ring
  have hc2 : t₂.cInf σ ≤ Real.exp ((|c₁| + ((T.Q.Dw j).q : ℝ) * lrd D.host.E) * ∑ τ, |(n₀ τ : ℝ)| +
      logSum (badPrimes T.Q.H Y.d.l₂) + Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ)) + 1) := by
    have h := ht₂c σ
    simp only [Int.cast_neg, abs_neg] at h
    rwa [Real.log_le_iff_le_exp (t₂.cInf_pos σ)] at h
  have hdd : Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ)) ≤
      391 / 2 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
    have h := hY.rd
    have hpos : (0 : ℝ) < Module.finrank ℚ Y.d.c₂.F := by exact_mod_cast Module.finrank_pos
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hlrd := lrd_bounds D.host.E
  have hq_r : ((T.Q.Dw j).q : ℝ) ≤ D.R.r := by exact_mod_cast (show (T.Q.Dw j).q ≤ D.R.r by omega)
  have hSnn : 0 ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| := by positivity
  have hNnn : 0 ≤ ∑ τ, |(n₀ τ : ℝ)| := by positivity
  have hfin := _root_.GlobalTheory.covol_numerical_collect CG CB D.R.f D.R.r Lb (∑ τ, ∑ k, |(la τ k : ℝ)|) (∑ τ, |(n₀ τ : ℝ)|)
    (sizeK (T.Q.Dw j) a (2 * (4 * m))) c₁ ((T.Q.Dw j).q) (lrd D.host.E) (logSum (badPrimes T.Q.H Y.d.l₂))
    (Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ))) hCG0 hCB0 (by exact_mod_cast hf1)
    (by exact_mod_cast hr1) hLb hSnn (Nat.cast_nonneg _) hq_r hlrd.1 (hlrd.2.trans hEs) hc₁b hNnn (by linarith [hN0])
    hsz0 (by linarith [hsizeK]) (hBad D T hT j hj Y e o hY Lb hLb hM hEs hfr) hdd
  refine (hfbd σ).trans ?_
  show t₁.cInf σ * t₂.cInf σ * _ ≤ _
  have hpet0 : 0 ≤ petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m)))
      ((2 * (4 * m) / 2 : ℕ) : ℤ)) σ (f₀ : Rul Y.d.Xo₂ Y.d.c₂) := AllWt.petAt_nonneg _ _ _ _ _ _ _
  calc t₁.cInf σ * t₂.cInf σ * _ ≤ Real.exp (((D.R.f : ℝ) * D.R.r + 1) * (2 * ((D.R.f : ℝ) * D.R.r) * Real.log (2 * Real.pi))) *
        Real.exp ((|c₁| + ((T.Q.Dw j).q : ℝ) * lrd D.host.E) * ∑ τ, |(n₀ τ : ℝ)| +
          logSum (badPrimes T.Q.H Y.d.l₂) + Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ)) + 1) *
        Real.exp (CG * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a (2 * (4 * m))) := by
        have h1 := (t₁.cInf_pos σ).le
        have h2 := (t₂.cInf_pos σ).le
        gcongr
    _ = Real.exp (_ + _ + _) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.2 hfin
end GlobalTheory.ShortSpanComp
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_span_composition_closed : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 10 * Lb → ∀ Z, ∃ s : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)), s ⊆ (latOn Y.U Z (wtOf (T.Q.Dw j) la 0) : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0) σ y ≤ Real.exp (C * (((D.R.f : ℝ) * D.R.r * Lb) ^ 3 * (∑ τ, ∑ k, |(la τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * Lb) ^ 5)) := by
  first | exact @_root_.GlobalTheory.ShortSpanComp.short_span_comp_mem | exact _root_.GlobalTheory.ShortSpanComp.short_span_comp_mem | (intros; apply _root_.GlobalTheory.ShortSpanComp.short_span_comp_mem <;> assumption)
end
end

