module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.CountT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UMatMulLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0441
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0438
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0021
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0414
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0419
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdmissibleFamilySatisfiesRowEstimates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0411
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0439
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountParameterConditionsOfSizeHypotheses
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem countClauses_of_sizeHyp : ∀ (D : D7) (L : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (n0 : ℕ) (A C cb7 : ℝ),
    0 ≤ C → 0 < cb7 → 2 * Cg ≤ A → (n0 : ℝ) ≤ D.R.k → 2 ≤ Cl → 2 * C ≤ Cl →
    Real.log L.sc.L ≤ cb7 * D.R.k → ArithmeticConditionsOfDatum D → StandingHypotheses D L C' Cl Cg cb Cu cT CT →
    AdmissibleBoundsFromSource.CountTheoremHypotheses D L n0 A C cb7 ∧ 4 * D.R.r < D.host.g 1 := by
  intro D L C' Cl Cg cb Cu cT CT n0 A C cb7 hC hcb hA hn0 hCl2 hCl3 hll hAr hH
  have d1 := data1 L
  have d11 : SplitsE D (D.host.g 0) := hAr.2.1
  have d13 : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 := hAr.2.2.2
  obtain ⟨-, -, -, -, H5, -, H7, H8, -, -, H11, H12, H13, ContinuousCyclotomicCharacter₂, ContinuityOfCyclotomicCharacter, CyclotomicCharacterContinuous, -, -, H19, LocalHeightDeterminant, H21, -, -, -, -⟩ := hH
  have hk5 := Formalism.MainNotions.S.five_le_k (D := D)
  have hf1 := Formalism.MainNotions.S.one_le_f (D := D)
  have hkr := Formalism.MainNotions.S.k_le_r (D := D)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hL1 := one_lt_scL L
  have hlogb := log_scb L
  have hb2 := two_le_scb L
  have hb0 : 0 < L.sc.b := lt_of_lt_of_le two_pos hb2
  refine ⟨?_, ?_⟩
  swap
  · have h5 : (4 : ℝ) * D.R.r < D.host.g 1 := four_r_lt_g_of_bounds hk5 (by linarith only [hb2]) r_le_two_k ContinuousCyclotomicCharacter₂
    exact_mod_cast h5
  have hlr : 1 ≤ Real.log (D.R.r : ℝ) := one_le_log_of_five_le (le_trans hk5 hkr)
  obtain ⟨hmsq, hLk, hClL⟩ := k_ge_of_chain_bound hm2 hL1 hCl2 H7
  have hrd2 : 2 ≤ D.host.rdE := by
    have h : D.host.v = D.host.rdE / 2 := rfl
    rw [h] at H19; linarith only [H19]
  have hlrd0 : 0 ≤ Real.log D.host.rdE := Real.log_nonneg (by linarith only [hrd2])
  have hDel0 : 0 ≤ (D.s.Del : ℝ) := le_trans (Real.rpow_nonneg (by positivity) _) LocalHeightDeterminant
  have hm1 : 1 ≤ D.R.m := le_trans (by norm_num) D.R.two_le_m
  have hb1nn : ∀ τ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ bOne D τ j := fun τ j h1 h2 =>
    le_trans (by positivity) (H8 τ j h1 h2)
  have hbsq : ∀ τ j, 1 ≤ j → j ≤ D.R.m → bOne D τ j ≤ L.sc.b ^ 2 := fun τ j h1 h2 => by
    have := (CyclotomicCharacterContinuous τ j h1 h2).2
    rwa [Real.rpow_two] at this
  refine ⟨d13, ?_, ?_, ?_, ?_, ?_, ?_, d11, ?_, ?_, hb2, ?_⟩
  · have h2 : n0 ≤ D.R.k := by exact_mod_cast hn0
    have h3 := D.R.two_le_m
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  · have h1 : D.R.m ^ 2 ≤ D.R.k := by exact_mod_cast hmsq
    have h2 : D.R.rS + 1 ≤ D.R.m := by
      have := D.R.two_le_m
      unfold Ranks.rS; omega
    have h3 : (D.R.rS + 1) ^ 2 ≤ D.R.m ^ 2 := Nat.pow_le_pow_left h2 2
    have h4 : D.R.k ≤ D.R.r := by exact_mod_cast hkr
    omega
  · have h1 := Real.log_le_self hlrd0
    have h2 : L.sc.L / Cl ≤ L.sc.L := div_le_self (by linarith only [hL1]) (by linarith only [hCl2])
    linarith only [h1, h2, H11, hLk, hkr]
  · intro τ i
    refine lamS_abs_le τ _ (fun l h1 h2 => ⟨(d1 τ l h1 h2).1, ?_⟩) (fun j h1 h2 => ⟨hb1nn τ j h1 h2, hbsq τ j h1 h2⟩) i
    exact le_of_le_four_mul_of_mul_le_chain (by linarith only [hk5]) hDel0 hCl2 hm2 (d1 τ l h1 h2).2 (H8 τ 1 le_rfl hm1) (hbsq τ 1 le_rfl hm1)
  · unfold gg
    have h1 : (D.host.g 0 : ℝ) * D.host.g 1 ≤ L.sc.b ^ Cg * L.sc.b ^ Cg :=
      mul_le_mul H13 ContinuityOfCyclotomicCharacter (by positivity) (by positivity)
    rw [← Real.rpow_add hb0] at h1
    exact le_trans h1 (Real.rpow_le_rpow_of_exponent_le (by linarith only [hb2]) (by linarith only [hA]))
  · have h5 : (4 : ℝ) * D.R.r < D.host.g 0 := four_r_lt_g_of_bounds hk5 (by linarith only [hb2]) r_le_two_k H12
    exact_mod_cast h5
  · intro τ a c hac
    have hX : 0 ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 := by positivity
    have hle := gap_product_le_of_bounds hC hX hL1 hCl2 hCl3 H11
    have hG0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by positivity
    have hg := gapAtLeast_of τ _ hG0 (fun l h1 h2 => (d1 τ l h1 h2).1) (hb1nn τ 1 le_rfl hm1) (H21 τ) a c hac
    rw [Real.log_mul hb0.ne' (by linarith only [hrd2]), hlogb]
    linarith only [hle, hg]
  · refine le_trans H5 (Real.sqrt_le_sqrt ?_)
    have : D.R.rS ≤ D.R.r := by
      have h4 := D.R.m_add_three_le_k
      have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
      unfold Ranks.rS; omega
    exact_mod_cast this
  · rw [hlogb]
    have h1 := mul_le_mul_of_nonneg_left (k_le_rank_product hk5 hkr hf1 hlr) hcb.le
    linarith only [h1, hll]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBesselJFactorAllWordsOfGap
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JFactTie

theorem jFactN_all : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → JFactN hI C hB u u' := by
  intro D X Y hF hI C hB u u' hGap t hG hr
  have hex : ∃ s : TT Y u u', s.toTerm = tc hI t :=
    Formalism.L2.SG.Pf.liftOntoC_of Formalism.L2.SG.Pf.WittFlags.LatIso_holds D X Y u u' (tc hI t)
  have hs : hex.choose.toTerm = tc hI t := hex.choose_spec
  have hrel : hex.choose.relevant := by
    show hex.choose.toTerm.relevant
    rw [hs]
    exact (hI.relevant t).1 hr
  have hsG : hex.choose.G ≠ 0 := by
    show hex.choose.toTerm.G ≠ 0
    rw [hs]
    intro h0
    apply hG
    apply (algebraMap D.host.F D.host.E).injective
    rw [gterm_val hI t, h0, map_zero]
  have hP : HasPin hex.choose := GlobalTheory.T.relevantLift_normalisedData_exist D X Y u u' hex.choose hrel hsG
  have hx := hP.choose_spec
  have hJ : JtOf hI t = Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') hex.choose := by
    unfold JtOf; rw [dite_eq_left hex]
  have hV : volRC hI t = (hP.choose.2.1 hP.choose.2.2).toReal := by
    unfold volRC covR; rw [dite_eq_left ⟨hr, hG, hex⟩, dite_eq_left hP]
  have hinv : ∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (hex.choose.pt.1 v), ∀ y,
      Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((hex.choose.pt.1 v)⁻¹ * (r * y))) =
        Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((hex.choose.pt.1 v)⁻¹ * y)) := by
    intro v
    obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := X.pl.symm.surjective v
    obtain ⟨p, hp⟩ := _root_.GlobalTheory.RelPtLift.relPt_lift D X Y hF hI 1 C u u' t hex.choose hs hG hr τ
    exact GlobalTheory.StabInv.stab_inv D X 1 C hB u u' τ (hex.choose.pt.1 (vOf X τ)) p hGap hp
  obtain ⟨μl, νl, hH, hQ, hR, hA⟩ := GlobalTheory.T.normalisedLift_amplitude_eq_covolume_mul_local D X Y 1 C u u' hex.choose hP.choose hrel hsG hx.1 hx.2.1 hx.2.2 hinv
  have hloc : ∀ τ, j1 hI C hB t τ = Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) *
      hsNormSq (haveI := FiniteDimensional.completeSpace ℂ (X.Vloc u (vOf X τ));
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (hex.choose.pt.1 (vOf X τ))) := by
    intro τ
    have : SigmaFinite (μl (vOf X τ)) := (hH (vOf X τ)).1
    exact GlobalTheory.T.localAmplitude_wittLift_eq_quotientIntegral D X Y hF hI C hB u u' t hex.choose hs hG hr hGap τ (μl (vOf X τ)) (νl (vOf X τ)) inferInstance
      (hQ (vOf X τ)) (hR τ)
  have hK := GlobalTheory.T.amplitudeConstant_eq_prod_covolumes D X Y hF 1 C hB u u' one_pos hGap
  have hre : (∏ τ, hsNormSq (haveI := FiniteDimensional.completeSpace ℂ (X.Vloc u (vOf X τ));
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (hex.choose.pt.1 (vOf X τ)))) =
      ∏ v, hsNormSq (haveI := FiniteDimensional.completeSpace ℂ (X.Vloc u v);
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (hex.choose.pt.1 v)) :=
    Fintype.prod_equiv X.pl.symm _ _ (fun τ => rfl)
  have hcov : covN (Y := Y) C u * covN (Y := Y) C u' =
      ((Measure.pi (fun _ : D.what₂.Tau => muNB D 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal * (Measure.pi (fun _ : D.what₂.Tau => muNB D 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u')).toReal) := rfl
  rw [hJ, hV, hA, hcov]
  unfold P1
  rw [Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, hre, hK]
  ring

end GlobalTheory.JFactTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopRowBoundsAlongFamilyLargeGaps
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂ Formalism.L2.SG.RowsU

noncomputable section

namespace GlobalTheory.LoopRowBoundsGap

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_along_family : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 cV CGam : ℝ, ∃ C₀ thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), Fm.CGam = CGam → thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) ∧ ∀ (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1), rows_TiesF Fm C1 X Y → (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairTermInjective (X x hx i) (Y x hx i u u')) → (∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') → (OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', VanishingOnXAndXPlus.TermVolumeSmallCellBound (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1 (Y x hx i u u') C' Cl Cg cb Cu cT CT C0 A cV) → ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsND (X x hx i) (Y x hx i u u') C ∧ RowsDeg (X x hx i) (Y x hx i u u') C ∧ RowsOne (X x hx i) (Y x hx i u u') C := by
  intro hSMR hH hBp Cg cb Cu cT CT C0 A C1 cV CGam
  obtain ⟨c3, cH, cS, c4, thr1, HC⟩ := _root_.GlobalTheory.RowCounts.uniform_counts hSMR Cg cb Cu cT CT C0 A
  obtain ⟨Ca, C2, Ch, thr2, hCa, hCh, HA⟩ := _root_.GlobalTheory.GapAmpUniform.amplitude_bounds_uniform_gap hSMR hH hBp Cg cb Cu cT CT C0 A C1
  let U : UC := ⟨c3, cH, cV, cS, c4, fun _ => Ca, fun _ => C2, fun _ => Ch⟩
  refine ⟨c0U CT A C0 CGam U, max 40 (max thr1 thr2), fun eps Fm hG hs hl hR => ?_⟩
  have hs1 : thr1 ≤ sC' Fm := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hl1 : thr1 ≤ sCl Fm := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hs2 : thr2 ≤ sC' Fm := (le_max_right _ _).trans ((le_max_right _ _).trans hs)
  have hl2 : thr2 ≤ sCl Fm := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  have h40 : 40 ≤ sCl Fm := (le_max_left _ _).trans hl
  have h3 : VanishingOnXAndXPlusMass.Conclusion3Family Fm := fun x _ i u => _root_.GlobalTheory.Mass.RowsRawMass.main (Fm.D x i) u
  obtain ⟨a10a, a6, a7, a8, a10b, hform⟩ :=
    GlobalTheory.CritLevelGap.along_family hH.2.2.2 eps Fm Cg cb Cu cT CT C0 A h40 hR h3
  refine ⟨hform, fun X Y hT hTI hBL hVol C hC => ?_⟩
  obtain ⟨LocalHeightDeterminant, H27, H4, H21⟩ := HC eps Fm hs1 hl1
  have hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U :=
    ⟨LocalHeightDeterminant, H27, hVol, H4, H21, fun Cpr => ⟨hCh, hCa, fun δ hδ => HA eps Fm hs2 hl2 hR Cpr δ hδ⟩⟩
  exact _root_.GlobalTheory.RowsFive.rows_three_bounds eps Fm C1 X Y Cg cb Cu cT CT C0 A a10a a6 a7 a8 a10b hT hTI hBL U hU C (by rw [hG]; exact hC)

end GlobalTheory.LoopRowBoundsGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TypePOfLargeGapDiscreteSeriesBessel
section
namespace GlobalTheory.TypeAsm.TopGap

theorem typeBound_of_gap :
    GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → Formalism.L2.SG.RowsPos.TypeP := by
  intro hH hBW

  have hAmp : GlobalTheory.TypeAsm.AmpP :=
    _root_.GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound (GlobalTheory.TypeAsm.locDatC_of_besselOfW hBW) (_root_.GlobalTheory.TypeAsm.TailTopGap.tailP_of_gap hH)

  have hPairs : GlobalTheory.TypeAsm.PairsP :=
    _root_.GlobalTheory.TypeAsm.pair_count_bound_of_siegel_mass GlobalTheory.Mass.MaxFormula.main GlobalTheory.Mass.siegelMassRatio_holds
  exact GlobalTheory.TypeAsm.typeBound_of_amplitude_pairs hAmp hPairs

end GlobalTheory.TypeAsm.TopGap
end

