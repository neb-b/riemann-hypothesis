module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0442
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHaarMeasuresPullbackRealGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0289
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0013
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.StandardHypothesesOfScaleHyp
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CriticalLevelLowOfRefined
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DegreeRatioFormulaStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0421
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormSqLeadMinorTurnP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0212

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeConstantEqProdCovolumes
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AmplitudeConst

theorem normSq_inv_mul_sqrt (l d l' d' : ℝ) (hl : 0 < l) (hl' : 0 < l') (hd : 0 ≤ d) (hd' : 0 ≤ d') :
    Complex.normSq ((((l / d : ℝ) : ℂ))⁻¹ * ((Real.sqrt (l / d * d' / l') : ℝ) : ℂ)) = d / l * (d' / l') := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.normSq_ofReal]
  have hs : 0 ≤ l / d * d' / l' := by positivity
  have e : (l / d)⁻¹ * Real.sqrt (l / d * d' / l') * ((l / d)⁻¹ * Real.sqrt (l / d * d' / l')) =
      (l / d)⁻¹ * (l / d)⁻¹ * (Real.sqrt (l / d * d' / l') * Real.sqrt (l / d * d' / l')) := by ring
  rw [e, Real.mul_self_sqrt hs]
  rcases hd.eq_or_lt with h | h
  · subst h; simp
  · field_simp

theorem const_eq (P P' L L' K M H M' H' V V' : ℝ) (hK : 0 < K) (hM : 0 < M) (hH : 0 < H) (hM' : 0 < M')
    (hH' : 0 < H') (hL : 0 < L) (hL' : 0 < L') (hV : L * V = M * H) (hV' : L' * V' = M' * H')
    (hP : 0 ≤ P) (hP' : 0 ≤ P') :
    P / L * (P' / L') = ((Real.sqrt (K * M * H / P * (K * M' * H' / P')))⁻¹ * K) ^ 2 * (V * V') := by
  rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), mul_inv, inv_div, inv_div]
  have eV : V = M * H / L := by field_simp; linarith
  have eV' : V' = M' * H' / L' := by field_simp; linarith
  subst eV eV'
  field_simp

theorem prod_finrank_loc {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    ∏ τ : D.what₂.Tau, (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) = (Module.finrank ℂ (X.Vpi u) : ℝ) := by
  rw [Formalism.L2.SG.Pf.finrank_Vpi, Nat.cast_prod]
  exact Fintype.prod_equiv X.pl.symm _ _ fun τ => rfl

theorem prod_normSq_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word), 0 < θ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∏ τ, Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * ((Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal * (Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u')).toReal) := by
  intro D X Y hF θ C hB u u' hθ hG
  have hK0 : 0 ≤ X.volK2 := ENNReal.toReal_nonneg
  have hv := hF.volPos u
  have hv' := hF.volPos u'
  have hN : 0 < X.volK2 * (X.muN u (Y.FN u)).toReal := hv.1
  have hN' : 0 < X.volK2 * (X.muN u' (Y.FN u')).toReal := hv'.1
  have hK : 0 < X.volK2 := pos_of_mul_pos_left hN ENNReal.toReal_nonneg
  have hNu : 0 < (X.muN u (Y.FN u)).toReal := pos_of_mul_pos_right hN hK0
  have hNu' : 0 < (X.muN u' (Y.FN u')).toReal := pos_of_mul_pos_right hN' hK0
  have hHu : 0 < (X.muH u Set.univ).toReal := hv.2
  have hHu' : 0 < (X.muH u' Set.univ).toReal := hv'.2
  obtain ⟨hl, hp⟩ := _root_.GlobalTheory.ProductL2.l2prod D X Y θ C hB u hθ hG hNu hHu
  obtain ⟨hl', hp'⟩ := _root_.GlobalTheory.ProductL2.l2prod D X Y θ C hB u' hθ hG hNu' hHu'
  have hτ : ∀ τ, Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) =
      (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) / (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal *
        ((Module.finrank ℂ (X.Vloc u' (vOf X τ)) : ℝ) / (l2SG (C.nuS u' τ) (phiOf hB u' τ)).toReal) := by
    intro τ
    unfold sclOf cOf
    exact normSq_inv_mul_sqrt _ _ _ _ (hl τ) (hl' τ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [Finset.prod_congr rfl fun τ _ => hτ τ, Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_div_distrib, prod_finrank_loc, prod_finrank_loc]
  unfold Formalism.L2.SG.TermOp.scl Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X
  exact const_eq _ _ _ _ _ _ _ _ _ _ _ hK hNu hHu hNu' hHu' (Finset.prod_pos fun τ _ => hl τ)
    (Finset.prod_pos fun τ _ => hl' τ) hp hp' (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end GlobalTheory.AmplitudeConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAmplitudeLeCovolumeLocalAmplitudes
section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem factC_of (hP : PullC) (hTn : TensC) (hC : ConstC) : FactC := by
  intro D X Y u C hB hG hcov t hrel μ ν K hμν hK
  obtain ⟨μR, νl, hνl, hH, hQ, hμR, hmap⟩ := hP D X Y u C t μ ν hμν
  have hFA := Formalism.L2.SG.Pf.formAllC_holds D X Y u u t μR (Measure.pi νl) K
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u t hrel) hH hQ hK.1 hK.2
  have hT := hTn D X u t.pt.1 νl hνl
  obtain ⟨hc, hconst⟩ := hC D X Y u C hB hG hcov
  have hloc : ∀ τ, Real.sqrt (hsNormSq ((locS hB u u τ).J (ν τ) (gamT C t τ))) =
      (cOf hB u τ)⁻¹ * Real.sqrt (hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ))
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u (vOf X τ)) (t.pt.1 (vOf X τ)))) := by
    intro τ
    rw [← hmap τ]
    unfold gamT
    rw [Formalism.L2.SG.Pf.LocJEq.locJ_map_eq' C hB u u τ]
    refine (congrArg Real.sqrt (Formalism.L2.SG.Pf.LTL.hsNormSq_smul _ _)).trans ?_
    rw [(hc τ).2, mul_one, map_inv₀, Complex.normSq_ofReal, Real.sqrt_mul', Real.sqrt_inv,
      Real.sqrt_mul_self (hc τ).1.le]
    · rfl
    · exact Formalism.L2.SG.Pf.LTL.hsNormSq_nonneg _
  have hv : ‖(Y.tO u u).vec t‖ = wt t * ‖Formalism.L2.SG.PackageTie.hsEmb
      (ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t)‖ := by
    show ‖Formalism.L2.SG.TermOp.vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t‖ = _
    unfold Formalism.L2.SG.TermOp.vec
    rw [← norm_smul_of_nonneg (show 0 ≤ wt t from Real.sqrt_nonneg _) (Formalism.L2.SG.PackageTie.hsEmb
      (ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t)), ← Complex.coe_smul]
    refine Eq.trans ?_ (PiLp.norm_single 2
      (fun _ : {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u} => Formalism.L2.SG.PackageTie.HS (X.Vpi u) (X.Vpi u))
      ((⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩) : {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u}) _)
    congr 2
    ext q
    simp [Pi.single_apply]
  have hs0 : 0 ≤ scl (Y.FN u) (Y.FN u) (X := X) (u := u) (u' := u) * X.volK2 := by
    unfold scl HidaSetting.volK2
    positivity
  have hamp : ‖Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t)‖ =
      (scl (Y.FN u) (Y.FN u) (X := X) (u := u) (u' := u) * X.volK2) * ((μR K).toReal *
        ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) t.pt.1)‖) := by
    unfold ampN
    rw [map_smul, map_smul, norm_smul, norm_smul, Formalism.L2.SG.Pf.FibreCounting.norm_chiN, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hs0, hFA, ← Complex.coe_smul, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hprod : ∏ τ, Real.sqrt (hsNormSq ((locS hB u u τ).J (ν τ) (gamT C t τ))) =
      (∏ τ, cOf hB u τ)⁻¹ * ∏ v, Real.sqrt (hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (t.pt.1 v))) := by
    rw [Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    congr 1
    exact Fintype.prod_equiv X.pl.symm _ _ (fun τ => rfl)
  have hPc : 0 < ∏ τ, cOf hB u τ := Finset.prod_pos fun τ _ => (hc τ).1
  rw [hv, hamp, ← hμR K hK.1, hprod]
  set N := ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) t.pt.1)‖ with hN
  set Pv := ∏ v, Real.sqrt (hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (t.pt.1 v))) with hPv
  set Pc := ∏ τ, cOf hB u τ with hPcd
  set s := scl (Y.FN u) (Y.FN u) (X := X) (u := u) (u' := u) * X.volK2 with hsd
  set a := wt t with had
  set m := (μR K).toReal with hmd
  set cv := (covN C Y u).toReal with hcv
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hcv0 : 0 ≤ cv := ENNReal.toReal_nonneg
  have hPv0 : 0 ≤ Pv := Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _
  have hNP : N ≤ Pv := hT
  have hSJ : 0 ≤ Pc⁻¹ * Pv := mul_nonneg (inv_nonneg.2 hPc.le) hPv0
  calc a * (s * (m * N)) * cv = (a * m * cv * s) * N := by ring
    _ ≤ (a * m * cv * s) * (Pc * (Pc⁻¹ * Pv)) := by
        rw [mul_inv_cancel_left₀ hPc.ne']
        exact mul_le_mul_of_nonneg_left hNP (by positivity)
    _ = (a * (m * (Pc⁻¹ * Pv))) * (s * Pc * cv) := by ring
    _ ≤ (a * (m * (Pc⁻¹ * Pv))) * 1 := mul_le_mul_of_nonneg_left hconst (by positivity)
    _ = a * (m * (Pc⁻¹ * Pv)) := mul_one _

theorem factC_holds : FactC := factC_of _root_.GlobalTheory.PullbackComparison.pullC_holds _root_.GlobalTheory.TensHS.tensC_holds _root_.GlobalTheory.LocalConst.constC

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformAmplitudeBoundWideRangeLargeGap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

open MeasureTheory NumberField Formalism.FourierDecayAlt Finset

namespace GlobalTheory.UnifPTGap

open Formalism.MainNotions.BridgeLemma

theorem tFrame_of_dsig (hM : Formalism.HermitianLatticesTheory.SiegelMassRatio) (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC)
    {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ}
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) : PX.TFrame Fm Cg cb Cu cT CT C0 := by
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  exact level_frame_of_sizes Fm Cg cb Cu cT CT C0 1 (by linarith)
    (level_formula_family Fm C0 Cg cb Cu cT CT (fun x i => mass_ratio_of_siegel_cm_unramified hM (Fm.D x i)) (mass_two_bound_family_holds Fm) hR)
    (Formalism.L2.SG.Pf.SzHypFam.localSplitExponents_of_forty_le_sCl Fm h40 C0 Cg cb Cu cT CT)

theorem uniformPT_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps),
    thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn, (OwnEv Fm fun C' Cl x i =>
      VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) := by
  intro hM hH hBp Cg cb Cu cT CT C0 C1
  set Cβ : ℝ := max 2 (max Cu (max CT (1 / 8 + 2 * Cg))) with hCβ
  have hβ2 : 2 ≤ Cβ := le_max_left _ _
  have hu : Cu ≤ Cβ := (le_max_left _ _).trans (le_max_right _ _)
  have hT : CT ≤ Cβ * 1 := by rw [mul_one]; exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hg : 1 / 8 + 2 * Cg ≤ Cβ * 1 := by
    rw [mul_one]; exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  obtain ⟨Cb, Cg₀, hBP⟩ := (_root_.GlobalTheory.bp_forms_of_gapIn_thmBpDS hH hBp 1).imp fun _ h => h.imp fun _ h Cg hCg => (h Cg hCg).2.2
  obtain ⟨Cgf, hOB⟩ := _root_.GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp hH
  obtain ⟨Cf, hCf, hFrm⟩ := GlobalTheory.FrameTurn.frameChange_of_frames 1 Cgf 2 zero_le_one (by norm_num)
  obtain ⟨Ca, hCa, hAmp⟩ := _root_.GlobalTheory.AmpBesselGap.ampIsBessel hH Cg cb Cu cT CT C0 C1
  refine ⟨max (Ca + Cβ * (Cf + max Cb 0 + Cf * max Cb 0)) (max Cb 0), 1000, fun eps Fm _ hl hR Cn => ?_⟩
  obtain ⟨m₀, hA⟩ := hAmp Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  have hAmpF : OwnEv Fm fun C' Cl x i => Bridge.AmpIsBessel (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 Ca :=
    ⟨x0, fun x hx i => hA (Fm.D x i) (Fm.L x i) _ _ hl (hx0 x hx i).2.2.2.2.1 (hx0 x hx i).2.1
      (Fm.ties x i).cdScale_tie⟩
  obtain ⟨a', hFr⟩ := hFrm Cn
  have hStd := Formalism.MainNotions.BridgeLemma.stdHypS_of Fm Cg cb Cu cT CT C0 1 Cβ (by linarith) zero_le_one hβ2 hu hT hg
    (max Cg₀ a') (200 * Cn)
  have hTF := tFrame_of_dsig hM hH.2.2.2 Fm (by linarith) hR
  exact Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H =>
    AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity _ _ _ _ _ _ _ _ _ _ Cn C1 Ca 1 Cf (max Cg₀ a') (200 * Cn) Cβ (max Cb 0) _ H.1.1
      (hFr _ (le_max_right _ _) _ (Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus _ Cgf 2 le_rfl (hOB _)))
      H.1.2 H.2
      (OnePlaceEstimates.upper_bound_mono_constant _ one_pos (le_max_left _ _) (hBP _ (le_max_left _ _) _ Cn (200 * Cn) le_rfl))
      (by linarith) (le_max_right _ _) hCa hCf (le_max_left _ _) (le_max_right _ _)) ((hAmpF.and hStd).and hTF)

end GlobalTheory.UnifPTGap
end

