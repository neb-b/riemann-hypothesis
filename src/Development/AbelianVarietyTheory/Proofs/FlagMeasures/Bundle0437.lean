module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0435
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0369
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0303
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqAmplitudeDoubleCosetInvariant
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointTermAndLiftSameRealDoubleCoset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0397
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0384

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientSmoothDecayCapelliEigenStatement
section
open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesCoefficient_smooth_decay_capelliEigen_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (f : B.Mat k r → (Wq →L[ℂ] Wp)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f) → EigDec f (aOf r h - 1) mu := by
  first | exact @GlobalTheory.eigDec_of_isKFinCoefT_gap | exact GlobalTheory.eigDec_of_isKFinCoefT_gap | (intros; apply GlobalTheory.eigDec_of_isKFinCoefT_gap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormalisedLocalBesselDatumStatement
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_localBesselDatum : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 1 ≤ k → IsSection k r L.z L.z' μsec → ∃ Bs : B.RealPlaceData k r L.Wp L.Wq, IsStdOf L μsec Bs := by
  first | exact @GlobalTheory.ThA.exists_isStdOf | exact GlobalTheory.ThA.exists_isStdOf | (intros; apply GlobalTheory.ThA.exists_isStdOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProof
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.WeightsFamPf

theorem weightsFam_of (hS : PI.VolStabS.MassDataS.SWXS) : GlobalTheory.SnFam.WeightsFam := by
  intro Cg cb Cw cT CT C0
  obtain ⟨aH, bH, hH⟩ := _root_.GlobalTheory.HTieLeaf.main Cg cb Cw cT CT C0
  refine ⟨max aH 2, bH, fun C' Cl e1 e2 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire _hBk
    K S TS cls hFQ γ _hγ Fm hFT _hRel _hTerm hG5 => ?_⟩
  have hC' : (2 : ℝ) ≤ C' := le_trans (le_max_right _ _) e1
  have hCH : aH ≤ C' := le_trans (le_max_left _ _) e1

  have hk4 : 4 * D.R.rS + 7 ≤ D.R.k := four_rank_add_seven_le_k hc
  have hk5 : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k := by
    obtain ⟨⟨hH0, _, _⟩, _, _⟩ := hc
    unfold Formalism.MainNotions.S.StandingHypotheses at hH0
    dsimp only at hH0
    obtain ⟨-, h2, h3, -, -⟩ := hH0
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
    have hL : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
    have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm2
    have hf : ((D.R.m : ℝ)) ^ 4 ≤ (D.R.f : ℝ) := by exact_mod_cast h3
    have hm5 : (2 : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hm 5
    have hm4 : (2 : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hm 4
    have hmm : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 4 := by
      have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) := by linarith
      calc (D.R.m : ℝ) = (D.R.m : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
    have hf0 : (0 : ℝ) ≤ (D.R.f : ℝ) := by positivity
    have h64 : (64 : ℝ) ≤ C' * (D.R.m : ℝ) ^ 5 := by nlinarith
    have ha : 64 * (D.R.f : ℝ) ≤ C' * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) := mul_le_mul_of_nonneg_right h64 hf0
    have hb' : C' * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) ≤ C' * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L :=
      le_mul_of_one_le_right (by nlinarith) hL
    have hreal : (D.R.m : ℝ) + (D.R.f : ℝ) + 5 ≤ (D.R.k : ℝ) := by nlinarith
    have hnat : D.R.m + D.R.f + 5 ≤ D.R.k := by exact_mod_cast hreal
    omega

  have hLaw := _root_.GlobalTheory.FinitePlaceMassFactors.tied_mass_law Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc K S TS cls hFQ γ Fm hFT hG5
  obtain ⟨_w0, F, F', _Y0, _hw0, _hn, _hZ, _hTP, hBase, _hML, _hgenL⟩ := id hLaw
  have hcong := _root_.GlobalTheory.NormCong.norms_congr D (zOf Y) Fm.FP u u' F F' hBase.1 (fun p => (hBase.2.1 p).2.2.2.2.2.2)

  obtain ⟨hpos, hHp, w, G', hw, hzt, hTP', hcell, hglue⟩ := _root_.GlobalTheory.GenMassBound.genericMass_le_heightPow_mul_glueSum D X Y u u' hk4 Fm γ hG5.1 hLaw
  obtain ⟨-, -, -, -, -, -, ⟨_, _, -, -, -, -, -, hLT⟩, -⟩ := hc.2.2
  obtain ⟨s, hgl, hs⟩ := _root_.GlobalTheory.GlueCount.glueSum_le D X Y u u' hLT hk5 hcong G' hzt hTP'
  obtain ⟨hne, hngen⟩ := hglue s hgl
  obtain ⟨⟨Λ, hΛ, hEZ⟩, hgs⟩ := hs hne
  obtain ⟨hfac, hAA⟩ := _root_.GlobalTheory.CountConst.countConst_eq_unscaledConst hS Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hk5 hcong hb X0 ψ hT sd C Th F0 what₂
    vR Q i0 i0' νq
  obtain ⟨hDl, hNG, hLam⟩ := _root_.GlobalTheory.GenMass.Norms.norms_generic D X Y u u' hcong G' Λ w hzt hTP' hΛ hEZ hcell
  have hHT := hH C' Cl hCH e2 D large₂ X Y u u' hc TS cls (nmlOf Y u u') γ Fm hFT
  subst hw
  have hrd : 0 < D.host.rdE := by
    unfold Host.rdE
    apply Real.rpow_pos_of_pos
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero _)
  set HP := HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u' : ℕ)) (toPts w) with hHPdef
  have hHt1 : 1 ≤ Fm.toL.Htot := by
    show 1 ≤ ∏ p : {p // p ∈ Fm.P}, (Fm.FP p.1).Hp
    have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : {p // p ∈ Fm.P} => (1 : ℝ))
      (g := fun p => (Fm.FP p.1).Hp) (fun _ _ => zero_le_one) (fun p _ => hHp p.1 p.2)
    simpa using this
  have hH1 : 1 ≤ HP := by rw [hHT]; exact hHt1
  have hg1 : (1 : ℝ) ≤ (X.B.g : ℝ) := by
    obtain ⟨-, -, -, -, -, -, -, hg0, hg1, -⟩ := hc.2.1
    rw [X.g_eq]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hg0.ne_zero hg1.ne_zero)
  have hgS : ((gS D : ℕ) : ℝ) = (X.B.g : ℝ) := by rw [X.g_eq]; rfl
  have hND0 : 0 ≤ NDPt D.host.rdE (toPts w) := by
    unfold NDPt
    exact Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by positivity
  have hND : NDPt D.host.rdE (toPts w) ≤ HP := by
    have h1 : 1 ≤ ((X.B.g : ℝ) ^ ((2 * D.R.rS + 1) * Fintype.card (InfinitePlace D.host.E)))⁻¹ *
        NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) := by
      have hp : 0 < (X.B.g : ℝ) ^ ((2 * D.R.rS + 1) * Fintype.card (InfinitePlace D.host.E)) :=
        pow_pos (by linarith) _
      rw [inv_mul_eq_div, le_div_iff₀ hp, one_mul]
      calc _ ≤ (X.B.g : ℝ) ^ ((2 * D.R.rS + 2) * Fintype.card (InfinitePlace D.host.E)) :=
            pow_le_pow_right₀ hg1 (Nat.mul_le_mul_right _ (by omega))
        _ ≤ _ := hgS ▸ hNG
    rw [hHPdef]
    unfold HPt
    exact le_mul_of_one_le_left hND0 h1
  have hhaar := _root_.GlobalTheory.HaarWeight.gram_pow_le_haar D.host.E D.R.rS D.R.k (Tu D u * Tu D u') D.host.rdE HP (toPts w) hrd hDl hND
  rw [← hHT] at hngen
  have hY0 : 0 ≤ NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ^ (D.R.k - 1) := by
    apply pow_nonneg
    exact le_trans (pow_nonneg (by positivity) _) hNG
  have hHa : 0 < HP ^ (3 * (D.R.rS + 1) ^ 2) := pow_pos (by linarith) _
  have hNle : Fm.toL.ngenTot ≤ HP ^ (3 * (D.R.rS + 1) ^ 2) *
      (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) *
      NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ^ (D.R.k - 1) := by
    calc Fm.toL.ngenTot ≤ _ := hngen
      _ ≤ HP ^ (3 * (D.R.rS + 1) ^ 2) * (2 * ((bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA *
          Formalism.L2.SG.MassDataConc.ngFac D) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
            (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) := by
          rw [← hAA]; exact mul_le_mul_of_nonneg_left hgs hHa.le
      _ = _ := by rw [← mul_assoc 2, mul_assoc (2 * _), mul_comm (Formalism.L2.SG.MassDataConc.ngFac D), hLam]; ring
  have hc0 : 0 ≤ 2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA *
      PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f := by
    by_contra hneg
    push_neg at hneg
    have h1 : HP ^ (3 * (D.R.rS + 1) ^ 2) * (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA *
        PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hHa.le hneg.le
    have h2 := mul_nonpos_of_nonpos_of_nonneg h1 hY0
    linarith
  have hnP : 0 ≤ nPt D.host.rdE D.R.k ((Tu D u : ℕ) * (Tu D u' : ℕ)) (toPts w) := by
    unfold nPt
    exact Finset.prod_nonneg fun _ _ => mul_nonneg (pow_nonneg (by positivity) _)
      (Finset.prod_nonneg fun _ _ => pow_nonneg (by positivity) _)
  have hab : 3 * (D.R.rS + 1) ^ 2 + 6 * (2 * D.R.rS + 2) ≤ PN.eN D.R.rS := by
    unfold PN.eN
    generalize (D.R.rS + 1) ^ 2 = t
    omega
  refine ⟨hpos, ?_⟩
  calc Fm.toL.ngenTot ≤ _ := hNle
    _ ≤ HP ^ (3 * (D.R.rS + 1) ^ 2) * (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA *
        PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) * (HP ^ (6 * (2 * D.R.rS + 2)) *
          nPt D.host.rdE D.R.k (Tu D u * Tu D u') (toPts w)) :=
        mul_le_mul_of_nonneg_left hhaar (mul_nonneg hHa.le hc0)
    _ = (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) *
        HP ^ (3 * (D.R.rS + 1) ^ 2 + 6 * (2 * D.R.rS + 2)) *
          nPt D.host.rdE D.R.k (Tu D u * Tu D u') (toPts w) := by ring
    _ ≤ (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) *
        HP ^ PN.eN D.R.rS * nPt D.host.rdE D.R.k (Tu D u * Tu D u') (toPts w) := by
        gcongr
    _ = _ := by ring

end GlobalTheory.WeightsFamPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvMomentOfBessel
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem size_bound_inv {b v g x Cg Cu CT : ℝ} {r : ℕ} (hb : Real.exp 1 < b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b)
    (hg : 1 ≤ g) (hgb : g ≤ b ^ (2 * Cg)) (hCg : 8 ≤ Cg) (hx0 : 0 ≤ x)
    (hx : x ≤ max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ^ r) :
    x * (b ^ max 2 Cu) ^ (2 * r) ≤ b ^ ((2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (2 * r + 2 : ℝ)) := by
  have hb2 : 2 < b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hb
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hB : (2 : ℝ) ≤ max 2 Cu := le_max_left _ _
  have hp := Real.pi_gt_three
  have hg2 : 1 ≤ b ^ (2 * Cg) := hg.trans hgb
  have hM : max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ≤ b ^ (2 * Cg + 2) := by
    rw [Real.rpow_add hb0, Real.rpow_two]
    refine max_le ?_ ?_
    · have : Real.pi / v / g ≤ Real.pi :=
        (div_le_self (by positivity) hg).trans (div_le_self (by positivity) hv)
      have := Real.pi_le_four
      nlinarith
    · rw [div_div, inv_div, div_le_iff₀ (by positivity)]
      have h1 : v * g ≤ b ^ 2 * b ^ (2 * Cg) := mul_le_mul (by nlinarith) hgb (by linarith) (by positivity)
      have : 0 ≤ b ^ (2 * Cg) * b ^ 2 := by positivity
      nlinarith
  have h1 : x ≤ b ^ ((2 * Cg + 2) * r) := by
    rw [Real.rpow_mul_natCast hb0.le]
    exact hx.trans (pow_le_pow_left₀ (le_max_of_le_left (by positivity)) hM r)
  calc x * (b ^ max 2 Cu) ^ (2 * r) ≤ b ^ ((2 * Cg + 2) * r) * (b ^ max 2 Cu) ^ (2 * r) := by gcongr
    _ = b ^ ((2 * Cg + 2) * r + max 2 Cu * ((2 * r : ℕ) : ℝ)) := by
        rw [Real.rpow_add hb0, Real.rpow_mul_natCast hb0.le (max 2 Cu)]
    _ ≤ _ := by
        refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
        push_cast
        have := abs_nonneg CT
        nlinarith [mul_nonneg this hr, mul_nonneg (by linarith : 0 ≤ Cg) hr, mul_nonneg (by linarith : 0 ≤ max 2 Cu) hr]

theorem rpow_bridge {b C x : ℝ} {q : ℕ} (hb : 0 ≤ b) : b ^ (2 * C * x * q) = (b ^ (C * x)) ^ (2 * q) := by
  rw [← Real.rpow_mul_natCast hb]; congr 1; push_cast; ring

end GlobalTheory.TwoSidedMoments

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem hypTT_self (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0)
    (w : D.what₂.Word) : HypTT D w w := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, hg1, -, hg2, -, -, -, -, -, -, -, -, -, -, -⟩, hDat, -⟩ := hZ
  obtain ⟨-, -, -, -, -, -, -, -, hmod, -⟩ := hDat
  have hk : (1 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hbe : Real.exp 1 < large₂.sc.b := Real.exp_lt_exp.2 hL
  have hb2 : 2 < large₂.sc.b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hbe
  have hkb : 2 < (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have hg : (2 : ℝ) < D.host.g 0 := lt_of_lt_of_le hkb ((le_self_pow₀ (by linarith) (by norm_num)).trans hg1)
  have hg' : 2 < D.host.g 0 := by exact_mod_cast hg
  have hgg : (2 : ℝ) < D.host.g 1 := lt_of_lt_of_le hkb ((le_self_pow₀ (by linarith) (by norm_num)).trans hg2)
  have hgg' : 2 < D.host.g 1 := by exact_mod_cast hgg
  have hp := (D.mem w).A.T_prime
  have h3 : 3 ≤ (D.mem w).A.T := by
    rcases (D.mem w).A.T_prime.two_le.eq_or_lt with h | h
    · exfalso
      have hm := (hmod w).2
      rw [← h] at hm
      have hN : 4 < (D.host.g 0 * D.host.g 1) ^ 2 := by
        have h9 : 9 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_le_mul (show 3 ≤ D.host.g 0 from hg') (show 3 ≤ D.host.g 1 from hgg')
        nlinarith
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
      omega
    · omega
  exact ⟨hp, hp, h3, h3, Int.ModEq.refl _⟩

end GlobalTheory.TwoSidedMoments

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem rd_le_b (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hCl : 1000 ≤ Cl)
    (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0) : D.host.rdE ≤ large₂.sc.b := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hrdL, -, -, -, -, -, -, -, hv, -⟩, -, -⟩ := hZ
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have h0 : 0 < D.host.rdE := by rw [hrd]; linarith
  have h1 : large₂.sc.L / Cl ≤ large₂.sc.L := div_le_self (by linarith) (by linarith)
  show D.host.rdE ≤ Real.exp large₂.sc.L
  exact (Real.log_le_iff_le_exp h0).1 (hrdL.trans h1)

end GlobalTheory.TwoSidedMoments
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeWittLiftEqQuotientIntegral
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpLoc

theorem hsNormSq_amp_loc : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (τ : D.what₂.Tau) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → (∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) → hsNormSq ((locS hB u u' τ).J (nu1 hI C t τ) (gamR hI C t τ)) = Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) * hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Formalism.L2.SG.RealObj.Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (s.pt.1 (vOf X τ))) := by
  intro D X Y hF hI C hB u u' t s hs hG hr hGap τ μ ν hμ hq hroot
  have hW : ∀ τ', GoodW D τ' u u' 1 (locW C u u' τ') := fun τ' =>
    goodW_of C u u' τ' (Formalism.L2.SG.Pf.colsTypeTr C u τ') (Formalism.L2.SG.Pf.colsTypeTr C u' τ')
      (Formalism.L2.SG.Pf.zTr C u τ') (Formalism.L2.SG.Pf.zTr C u' τ') (Formalism.L2.SG.Pf.haarTr C τ')
  have e1 := Formalism.L2.SG.Pf.LocJEq.locJ_map_eq' C hB u u' τ (s.pt.1 (vOf X τ)) ν
  have hR2 : RMeas D (locW C u u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) 1
      (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ (s.pt.1 (vOf X τ)))) := by
    obtain ⟨p, hp⟩ := hroot
    refine ⟨p, _, hp, ?_⟩
    rw [ENNReal.ofReal_one, one_smul]
    exact _root_.GlobalTheory.quotMeas_besselModel_of_quotLoc D X 1 C τ (s.pt.1 (vOf X τ)) μ ν hμ hq
  obtain ⟨a, ha, a', ha', hga⟩ := _root_.GlobalTheory.TermCoset.dcoset D X Y hF hI 1 C u u' t s hs τ
  have hR4 : RMeas D (locW C u u' τ) (gamR hI C t τ) 1 (nu1 hI C t τ) := by
    have h := GlobalTheory.RMeasAll.rMeasEx_all D X Y hF hI C u u' hW t hG hr τ
    unfold nu1
    rw [dite_eq_left h]
    exact h.choose_spec
  obtain ⟨p0, hp0⟩ := relPtEx_holds hI C u u' t hG hr τ
  obtain ⟨hΦ, hΦ', hc, hc'⟩ := _root_.GlobalTheory.SlocTie.locS_phi_equiv_cont D X 1 C hB u u' τ hGap
  have h5 := _root_.GlobalTheory.AmpCoset.hsNormSq_amp_doubleCoset D τ u u' 1 (locW C u u' τ) (locS hB u u' τ) (hW τ)
    (Nat.cast_pos.2 (D.mem u).A.T_prime.pos) (Nat.cast_pos.2 (D.mem u').A.T_prime.pos) hΦ hΦ' hc hc'
    (gamR hI C t τ) a a' p0 (nu1 hI C t τ) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ (s.pt.1 (vOf X τ))))
    hp0 ha ha' hR4 (by rw [← hga]; exact hR2)
  rw [← h5, ← hga, e1]
  exact Formalism.L2.SG.LoopTerm.hsNormSq_smul _ _

end GlobalTheory.AmpLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTermAmplitudeEqMassMulPhase
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpTerm

theorem gval_of_movesTo {D : D7} {T T' : D.host.E} {F00 F : LFlag (D.sp.Y 0) D.R.rS T}
    {F'0 F' : LFlag (D.sp.Y 0) D.R.rS T'} {ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E}
    (h : MovesTo F00 F'0 F F' ρ U U') : Gval F F' = Gval F00 F'0 := by
  obtain ⟨hρ, hU, hU', hF, hF'⟩ := h
  have hZ : ZhatL F F' = U.conjTranspose * ZhatL F00 F'0 * U' := by
    ext a b
    have e1 : ZhatL F F' a b = (VS D).hT (ρ (frame F a)) (ρ (frame F' b)) := by
      rw [hρ]; rfl
    have hz : ∀ c d, ZhatL F00 F'0 c d = (VS D).hT (frame F00 c) (frame F'0 d) := fun _ _ => rfl
    rw [e1, hF a, hF' b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, hz, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Matrix.conjTranspose_apply, starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
    simp only [RingHom.id_apply]
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => ?_))
    ring
  have hD : ∀ l, Dl F.fl F'.fl l = Dl F00.fl F'0.fl l := by
    intro l
    have := Formalism.L2.SG.Pf.leadMinor_uni U.conjTranspose (ZhatL F00 F'0) U'
      (fun a c hac => by simp [Matrix.conjTranspose_apply, (hU c a).1 hac])
      (fun a => by simp [Matrix.conjTranspose_apply, (hU a a).2 rfl])
      (fun d b hbd => (hU' d b).1 hbd) (fun b => (hU' b b).2 rfl) l
    rw [← hZ] at this
    exact this
  simp only [Gval, Gflag, hD]

theorem G_eq_gval {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (t : TauC Y u u') :
    t.G = Gval (lf D (X.Fu u)) t.frame :=
  Formalism.L2.SG.TermDef.Gt_mk (Formalism.L2.SG.Pf.g_value_function _ _ _) ⟨t.frame, t.rep.2.2.2.2⟩

theorem lam_eq_of_row {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} {t t₀ : TauC Y u u'}
    (h : (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀) : t.lam = t₀.lam ∧ t.lam' = t₀.lam' :=
  ⟨congrArg (fun r => r.1.1) h, congrArg (fun r => r.2.1.1) h⟩

theorem exists_admissibleWitness_rowTerm {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (t : TauC Y u u') :
    ∃ ξ, AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ :=
  t.rep.2.2.2.2.2.1

end GlobalTheory.AmpTerm

namespace GlobalTheory.AmpTerm


open Formalism.L2.SG.PairVal in
theorem amp_eq_mass_phase : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → Formalism.L2.SG.PairVal.ptOf t₀.toTerm = w → ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w)‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = ((((((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat (ρ * n) t.lam) : ℝ) : ℂ) * G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat (ρ * n) t.lam)) • T := by
  intro D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c ν hν t₀ ρ U U' hmv hrel hpt
  have hG0 : t₀.G ≠ 0 := by
    rw [G_eq_gval]; exact fun h => hG ((gval_of_movesTo hmv).symm.trans h)
  obtain ⟨-, T0, hT0, hform⟩ := GlobalTheory.T.orbital_integrals_terms_one_doubleCoset D X Y u u' hS ν hν t₀ hrel hG0 w hpt.symm
  have hpU : psiInf (gS D) (sgUp U) ≠ 0 := by
    intro h; have := norm_psiInf (gS D) (sgUp U); rw [h, norm_zero] at this; exact zero_ne_one this
  have hpU' : psiInf (gS D) (sgUp U') ≠ 0 := by
    intro h; have := norm_psiInf (gS D) (sgUp U'); rw [h, norm_zero] at this; exact zero_ne_one this
  refine ⟨(((scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) *
      psiInf (gS D) (sgUp U) * (psiInf (gS D) (sgUp U'))⁻¹) • T0, ?_, ?_⟩
  · rw [map_smul, norm_smul, hT0]
    unfold Jw
    rw [map_smul, norm_smul, norm_mul, norm_mul, norm_inv, norm_psiInf, norm_psiInf]
    simp
  · rintro t n m hrow ⟨hn, hm, hlin⟩
    obtain ⟨hlam, hlam'⟩ := lam_eq_of_row hrow
    have hL := GlobalTheory.RatIsomPoint.ratLink_points D X
    obtain ⟨xn, hxn, -⟩ := hL.1 n hn.1
    obtain ⟨xm, hxm, -⟩ := hL.1 m hm.1
    obtain ⟨μR, K, hpin, hK, hOO⟩ := hform t n m xn xm ⟨hn, hm, hlin⟩ hxn hxm
    obtain ⟨-, -, -, -, -, hgrp⟩ :=
      GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv
    obtain ⟨A, A', hA, hA', hnA, hmA', hmv'⟩ := hgrp t n m ⟨hn, hm, hlin⟩
    have hcos := _root_.GlobalTheory.HL.CosetConst.coset_const D X Y u u' hS t₀ t n m hrel hG0 ⟨hn, hm, hlin⟩
    have hvol := _root_.GlobalTheory.CovMass.covol_eq_mass D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t (ρ * n) (U * A) (U' * A')
      hmv' hcos.1 μR hpin K hK
    obtain ⟨ξ, hξ⟩ := exists_admissibleWitness_rowTerm t
    have hchi := _root_.GlobalTheory.AdmWitChar.chiN_kOf_eq_inv_psiInf_sgUp D X Y u u' hS t ξ hξ
    have hterm := (_root_.GlobalTheory.HL.MovedTermPhase.main D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t (ρ * n) (U * A) (U' * A')
      hmv').2 ξ hξ
    have hdat := (_root_.GlobalTheory.HL.DatEq.row_eq_iff_datOf_eq D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv t n m hlam hlam'
      ⟨hn, hm, hlin⟩).1 hrow
    rw [hdat] at hterm
    have hpn := (hL.2.2 u xn n hxn).2 hn A hnA
    have hpm := (hL.2.2 u' xm m hxm).2 hm A' hmA'
    have hU := hmv.2.1
    have hU' := hmv.2.2.1
    unfold ampN
    rw [hchi, hOO, hpn, hpm, hvol, hterm, Formalism.L2.SG.Pf.sgUp_mul hU hA, Formalism.L2.SG.Pf.sgUp_mul hU' hA',
      Formalism.L2.SG.Pf.psiInf_add, Formalism.L2.SG.Pf.psiInf_add, smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp

end GlobalTheory.AmpTerm
end

