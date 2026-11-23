module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0415
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0109
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0407
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTrm
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0416
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
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeSizeZ
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntClLeEncardMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeProdReal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0413
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0414
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudePieriRelevantCellLargeGapStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_pieri_relevantCell_largeGap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (L : LocBessel k r) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (om om' : ι → ℂ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (lI : ∀ I, (RI I).H → L.Wp) (lI' : ∀ I, (RI I).H → L.Wq) (w : R.H) (wI : ∀ I, (RI I).H) (κ₀ κ₁ : κ → ℂ), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → (∀ I, (RI I).IsDS L.ε (muI I) ∧ GapAtLeast L.ε (muI I) h) → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → L.c ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Sset k r L.z, ρ g *ᵥ om = om) → (∀ g ∈ Sset k r L.z', ρ g *ᵥ om' = om') → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∀ I, (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π (RI I).σ L.μW L.μN x v = (innerSL ℂ (lI I v)).smulRight (lI I x)) ∧ (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' (RI I).σ L.μW' L.μN x v = (innerSL ℂ (lI' I v)).smulRight (lI' I x))) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → (∀ I, PI.UpqRep.IsLowUnitH k r L.ε (muI I) (RI I).σ (wI I)) → (∀ I, ∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ I • l v ∧ lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ I • l' v) → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν → (herm Γ (ρ γ *ᵥ om') om * (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)) • amp R l l' w νR γ = ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH μG (RI I).σ (wI I) : ℂ)) • amp (RI I) (lI I) (lI' I) (wI I) νR γ := by
  first | exact @GlobalTheory.CellPieriG.amp_pieri | exact GlobalTheory.CellPieriG.amp_pieri | (intros; apply GlobalTheory.CellPieriG.amp_pieri <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletionMovedLatticeEqLocalCoordinates
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.HL.placesLat_gcoordLat_eq : ∀ (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (𝓞 D.host.E) (VS D).V), GlobalTheory.LocOver.Ext p σ g → (placesOf Z).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Z.M p) g (lattice₂ D Z.M p Λ)) := by
  intro D Z T T' F0 F0' FP G c σ p g Λ hE
  unfold GlobalTheory.HL.GCoord.lat GlobalTheory.HL.Places.lat GlobalTheory.HL.WCoord.lat Formalism.MainNotions.S.LocNG.img Formalism.L2.SG.TermLoc.lattice₂
  rw [Submodule.map_span, Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g (baseChange₂ D p x), ⟨baseChange₂ D p x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    show (c.c p).e (g (baseChange₂ D p x)) = (placesOf Z).bc p (c.e (σ x))
    rw [hE x, c.compat p (σ x)]
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨c.e (σ x), ⟨x, hx, rfl⟩, ?_⟩
    show (placesOf Z).bc p (c.e (σ x)) = (c.c p).e (g (baseChange₂ D p x))
    rw [hE x, c.compat p (σ x)]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiagonalHypothesesOfRowsAndWindow
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem lemmaPG_record : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg C : ℝ, 40 ≤ Cl → Cl ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → Glob0 D x eps CD Cg → Nodes D x eps → DuWin D 3 → AdmissibleBoundsFromSource.hyp D large₂ 3 C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) ∧ Formalism.L2.SG.RowsConc.TFrameAt D ∧ C * large₂.sc.L ≤ (D.R.m : ℝ) - 1 ∧ C ≤ (D.R.k : ℝ) := by
  intro hSM hDs eps CD heps0 heps1 hCD C' Cl Cg C hCl40 hClCD
  have hCl0 : (0 : ℝ) < Cl := by linarith
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.dataConditions_of_global_and_real_rows eps CD heps0 heps1 hCD
  obtain ⟨x2, hx2⟩ := _root_.GlobalTheory.Diag.PG.standingHypotheses_of_glob0_nodes_Tr_bounds eps CD heps0 heps1 hCD C' Cl Cg hCl0 hClCD
  obtain ⟨x3, hx3⟩ := _root_.GlobalTheory.Diag.PG.rankNums_first_half eps CD heps0 heps1 hCD (max C (3 * Real.exp 8))
  refine ⟨max x1 (max x2 x3), ?_⟩
  intro x hx D large₂ hL hC' hTies hAdm hG hN hW
  have hx1' : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2' : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3' : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx

  obtain ⟨-, hAr⟩ := _root_.GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 D
  have hData : StandingNumericalData D 3 := hx1 x hx1' D Cg 3 hG hN hAr hW

  obtain ⟨-, -, -, -, -, hm1, hk, hxe⟩ := hx3 x hx3' _ _ _ _ _ hG.nums
  have hxe0 : (0 : ℝ) ≤ x ^ eps := le_of_lt (lt_trans zero_lt_one hxe)
  have h3 : (3 : ℝ) ≤ max C (3 * Real.exp 8) :=
    le_trans (by have := Real.add_one_le_exp (8 : ℝ); linarith) (le_max_right _ _)
  have hCm : C * large₂.sc.L ≤ (D.R.m : ℝ) - 1 := by
    rw [hL]; exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hxe0) hm1
  have h3m : 3 * large₂.sc.L ≤ (D.R.m : ℝ) - 1 := by
    rw [hL]; exact le_trans (mul_le_mul_of_nonneg_right h3 hxe0) hm1
  have h3k : 3 * Real.exp 8 ≤ (D.R.k : ℝ) := le_trans (le_max_right _ _) hk
  have hCk : C ≤ (D.R.k : ℝ) := le_trans (le_max_left _ _) hk

  have hLpos : 0 < large₂.sc.L := by rw [hL]; linarith
  have hb1 : 1 < large₂.sc.b := by
    show 1 < Real.exp large₂.sc.L
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hLpos
  have hb0 : 0 < large₂.sc.b := lt_trans zero_lt_one hb1
  have hm0 : (0 : ℝ) < (D.R.m : ℝ) := by
    have := D.R.two_le_m
    exact_mod_cast (show 0 < D.R.m by omega)
  have hT1 : ∀ u, (1 : ℝ) ≤ Tr D u := fun u => by
    show (1 : ℝ) ≤ ((D.mem u).A.T : ℝ)
    exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hmb : (D.R.m : ℝ) * Real.log large₂.sc.b ≠ 0 := (mul_pos hm0 (Real.log_pos hb1)).ne'
  obtain ⟨CT0, hCT0⟩ : ∃ c : ℝ, c * ((D.R.m : ℝ) * Real.log large₂.sc.b) = ∑ v, Real.log (Tr D v) :=
    ⟨(∑ v, Real.log (Tr D v)) / ((D.R.m : ℝ) * Real.log large₂.sc.b), div_mul_cancel₀ _ hmb⟩
  have hwin0 : ∀ u, large₂.sc.b ^ ((0 : ℝ) * (D.R.m : ℝ)) ≤ Tr D u ∧
      Tr D u ≤ large₂.sc.b ^ (CT0 * (D.R.m : ℝ)) := by
    intro u
    refine ⟨by rw [zero_mul, Real.rpow_zero]; exact hT1 u, ?_⟩
    rw [Real.rpow_def_of_pos hb0,
      show Real.log large₂.sc.b * (CT0 * (D.R.m : ℝ)) = CT0 * ((D.R.m : ℝ) * Real.log large₂.sc.b) by ring, hCT0]
    calc Tr D u = Real.exp (Real.log (Tr D u)) :=
          (Real.exp_log (lt_of_lt_of_le zero_lt_one (hT1 u))).symm
      _ ≤ Real.exp (∑ v, Real.log (Tr D v)) :=
          Real.exp_le_exp.mpr (Finset.single_le_sum (fun v _ => Real.log_nonneg (hT1 v))
            (Finset.mem_univ u))

  have hHyp0 : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 0 CT0 := hx2 x hx2' D large₂ 0 CT0 hL hC' hG hN hwin0
  have hCnt : Cnt.Hyp0 D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 :=
    (⟨hHyp0, hData, by norm_num⟩ : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 0 CT0 ∧ StandingNumericalData D 3 ∧ (1 : ℝ) ≤ 3)

  have hFr := (GlobalTheory.pgFrame_at_record hSM hDs D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 hTies hCnt hCl40 h3m h3k hAdm).1
  have hwin := _root_.GlobalTheory.levelPrime_size hSM hDs D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 hTies hCnt hCl40 h3m h3k hAdm

  have hHyp : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) :=
    hx2 x hx2' D large₂ (1 / 2) (4 * Cg + 13) hL hC' hG hN hwin
  exact ⟨(⟨hData, hHyp, by norm_num⟩ :
      StandingNumericalData D 3 ∧ StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) ∧ (1 : ℝ) ≤ 3), hFr, hCm, hCk⟩

end GlobalTheory.Diag.PG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitriangularFramesGramEqCellPoint
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocOver

section MatrixFacts

variable {K : Type*} [Field K] {N : ℕ}

theorem upUni_inv_facts {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) :
    IsUpUni U⁻¹ ∧ U * U⁻¹ = 1 ∧ U⁻¹ * U = 1 := by
  have hbt : U.BlockTriangular id := fun i j hij => (hU i j).1 hij
  have hdet : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]
    exact Finset.prod_eq_one fun i _ => (hU i i).2 rfl
  have hu : IsUnit U.det := by rw [hdet]; exact isUnit_one
  have h1 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hu
  have h2 : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hu
  letI := Matrix.invertibleOfIsUnitDet U hu
  have hbt' : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  refine ⟨fun i j => ⟨fun hij => hbt' hij, fun hij => ?_⟩, h1, h2⟩
  subst hij
  have e := congrFun (congrFun h2 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
  · rw [(hU i i).2 rfl, mul_one] at e; simpa using e
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hbt' h, zero_mul]
    · rw [(hU k i).1 h, mul_zero]
  · simp

theorem loUni_inv_facts {L : Matrix (Fin N) (Fin N) K} (hL : IsLoUni L) :
    IsLoUni L⁻¹ ∧ L * L⁻¹ = 1 ∧ L⁻¹ * L = 1 := by
  have hT : IsUpUni L.transpose := fun i j => ⟨fun hij => (hL j i).1 hij, fun hij => by subst hij; simpa using (hL i i).2 rfl⟩
  obtain ⟨h0, -, -⟩ := upUni_inv_facts hT
  have hbt : L.transpose.BlockTriangular id := fun i j hij => (hT i j).1 hij
  have hdet : L.det = 1 := by
    rw [← Matrix.det_transpose, Matrix.det_of_upperTriangular hbt]
    exact Finset.prod_eq_one fun i _ => (hT i i).2 rfl
  have hu : IsUnit L.det := by rw [hdet]; exact isUnit_one
  refine ⟨fun i j => ?_, Matrix.mul_nonsing_inv L hu, Matrix.nonsing_inv_mul L hu⟩
  have e : L⁻¹ i j = (L.transpose)⁻¹ j i := by rw [← Matrix.transpose_nonsing_inv]; rfl
  rw [e]
  exact ⟨fun hij => (h0 j i).1 hij, fun hij => (h0 j i).2 hij.symm⟩

end MatrixFacts

theorem tw_tw {K : Type*} [CommRing K] {r : ℕ} (B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Formalism.MainNotions.BridgeLemma₂.rows_tw (Formalism.MainNotions.BridgeLemma₂.rows_tw B) = B := by
  have hs : ∀ n : ℕ, ((-1 : K) ^ n) * ((-1) ^ n) = 1 := by
    intro n; rw [← mul_pow]; simp
  ext i j
  simp only [Formalism.MainNotions.BridgeLemma₂.rows_tw, Matrix.of_apply]
  linear_combination (B i j * (-1) ^ (r - j.val) * (-1) ^ (r - j.val)) * hs (r - i.val) + B i j * hs (r - j.val)

theorem tw_upUni {K : Type*} [CommRing K] {r : ℕ} {B : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hB : IsUpUni B) : IsUpUni (Formalism.MainNotions.BridgeLemma₂.rows_tw B) := by
  intro i j
  refine ⟨fun hij => by simp [Formalism.MainNotions.BridgeLemma₂.rows_tw, (hB i j).1 hij], fun hij => ?_⟩
  subst hij
  simp only [Formalism.MainNotions.BridgeLemma₂.rows_tw, Matrix.of_apply, (hB i i).2 rfl, mul_one]
  rw [← mul_pow]; simp

variable {D : D7}

theorem zhatL_chg {T T' : D.host.E} {F F₂ : LFlag (D.sp.Y 0) D.R.rS T} {F₁ F₃ : LFlag (D.sp.Y 0) D.R.rS T'}
    {A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E}
    (h₂ : Chg (frame F) A (frame F₂)) (h₃ : Chg (frame F₁) A' (frame F₃)) :
    ZhatL F₂ F₃ = A.conjTranspose * ZhatL F F₁ * A' := by
  ext a b
  have e2 : F₂.fl.fvec a = ∑ c, A c a • F.fl.fvec c := h₂ a
  have e3 : F₃.fl.fvec b = ∑ d, A' d b • F₁.fl.fvec d := h₃ b
  simp only [ZhatL, Zhat, brS, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e2, e3]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [RingHom.id_apply, starRingEnd_apply]
  ring

theorem zhatL_leadMinor {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ : LFlag (D.sp.Y 0) D.R.rS T')
    {A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E} (hA : Uni A) (hA' : Uni A') (l : ℕ) :
    leadMinorE (A.conjTranspose * ZhatL F F₁ * A') l = leadMinorE (ZhatL F F₁) l := by
  unfold leadMinorE
  split_ifs with hl
  · exact Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant D.host.E _ l hl _ _ _
      (fun i => by simp [Matrix.conjTranspose_apply, hA.2 i])
      (fun i j hij => by simp [Matrix.conjTranspose_apply, hA.1 j i hij])
      (fun i => hA'.2 i) (fun i j hij => hA'.1 i j hij)
  · rfl

theorem base_frames_at_point : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ : LFlag (D.sp.Y 0) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → IsInCell (ZhatOM (ZhatL F F₁)) w → (∃ (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T'), Tri D.host.E (frame F) (frame F00) ∧ Tri D.host.E (frame F₁) (frame F'0) ∧ ZhatOM (ZhatL F00 F'0) = ptMat w) ∧ ∀ (F₂ : LFlag (D.sp.Y 0) D.R.rS T) (F₃ : LFlag (D.sp.Y 0) D.R.rS T'), Tri D.host.E (frame F) (frame F₂) → Tri D.host.E (frame F₁) (frame F₃) → IsInCell (ZhatOM (ZhatL F₂ F₃)) w ∧ Gval F₂ F₃ = Gval F F₁ := by
  intro D T T' F F₁ w hT hT' hcell
  obtain ⟨L, U, hL, hU, hZ⟩ := hcell
  refine ⟨?_, ?_⟩
  · obtain ⟨hLi, -, hLL⟩ := loUni_inv_facts hL
    obtain ⟨hUi, hUU, -⟩ := upUni_inv_facts hU
    have hA : Uni (L⁻¹).conjTranspose :=
      ⟨fun a b hba => by simp [Matrix.conjTranspose_apply, (hLi b a).1 hba],
        fun a => by simp [Matrix.conjTranspose_apply, (hLi a a).2 rfl]⟩
    have hA'u := tw_upUni hUi
    have hA' : Uni (Formalism.MainNotions.BridgeLemma₂.rows_tw U⁻¹) := ⟨fun a b hba => (hA'u a b).1 hba, fun a => (hA'u a a).2 rfl⟩
    obtain ⟨F00, h00⟩ := (_root_.GlobalTheory.FlagChange.flag_change D F hT).1 _ hA
    obtain ⟨F'0, h'0⟩ := (_root_.GlobalTheory.FlagChange.flag_change D F₁ hT').1 _ hA'
    refine ⟨F00, F'0, ⟨_, hA, h00⟩, ⟨_, hA', h'0⟩, ?_⟩
    rw [zhatL_chg h00 h'0, Formalism.MainNotions.BridgeLemma₂.rows_ZhatOM_mul, hZ, tw_tw, Matrix.conjTranspose_conjTranspose]
    calc L⁻¹ * (L * ptMat w * U) * U⁻¹ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
      _ = ptMat w := by rw [hLL, hUU, Matrix.one_mul, Matrix.mul_one]
  · rintro F₂ F₃ ⟨A, hA, h2⟩ ⟨A', hA', h3⟩
    have hZ2 := zhatL_chg h2 h3
    constructor
    · have hAl : IsLoUni A.conjTranspose := fun i j =>
        ⟨fun hij => by simp [Matrix.conjTranspose_apply, hA.1 j i hij],
          fun hij => by subst hij; simp [Matrix.conjTranspose_apply, hA.2 i]⟩
      have hAu : IsUpUni A' := fun i j => ⟨fun hij => hA'.1 i j hij, fun hij => by subst hij; exact hA'.2 i⟩
      refine ⟨A.conjTranspose * L, U * Formalism.MainNotions.BridgeLemma₂.rows_tw A', Formalism.MainNotions.BridgeLemma₂.rows_loUni_mul hAl hL,
        Formalism.MainNotions.BridgeLemma₂.rows_upUni_mul hU (tw_upUni hAu), ?_⟩
      rw [hZ2, Formalism.MainNotions.BridgeLemma₂.rows_ZhatOM_mul, hZ]
      simp only [Matrix.mul_assoc]
    · show Gflag F₂.fl F₃.fl = Gflag F.fl F₁.fl
      have hD : ∀ l, Dl F₂.fl F₃.fl l = Dl F.fl F₁.fl l := fun l => by
        show leadMinorE (ZhatL F₂ F₃) l = leadMinorE (ZhatL F F₁) l
        rw [hZ2]; exact zhatL_leadMinor F F₁ hA hA' l
      unfold Gflag
      rw [hD, hD]

end GlobalTheory.LocOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatPassesToLocalCongruence
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IotaLoc

section Gen

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}
  (H : HermSp M V) (Λ : Submodule M.L.O V) (f f' : Fin (r + 1) → V)

theorem cong_add {v w : V} (hv : Cong H Λ f f' v) (hw : Cong H Λ f f' w) : Cong H Λ f f' (v + w) := by
  obtain ⟨a, ha, b, hb, c, hc, hbX, hcX, rfl⟩ := hv
  obtain ⟨a', ha', b', hb', c', hc', hbX', hcX', rfl⟩ := hw
  exact ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', c + c', add_mem hc hc', add_mem hbX hbX',
    add_mem hcX hcX', by abel⟩

theorem cong_neg {v : V} (hv : Cong H Λ f f' v) : Cong H Λ f f' (-v) := by
  obtain ⟨a, ha, b, hb, c, hc, hbX, hcX, rfl⟩ := hv
  exact ⟨-a, neg_mem ha, -b, neg_mem hb, -c, neg_mem hc, neg_mem hbX, neg_mem hcX, by abel⟩

theorem cong_of_mem {v : V} (hv : v ∈ H.smulLat (algebraMap F E (theta M)) Λ) : Cong H Λ f f' v :=
  ⟨v, hv, 0, zero_mem _, 0, zero_mem _, zero_mem _, zero_mem _, by simp⟩

theorem cong_iff_of_sub {v w : V} (h : v - w ∈ H.smulLat (algebraMap F E (theta M)) Λ) :
    Cong H Λ f f' v ↔ Cong H Λ f f' w := by
  constructor
  · intro hv
    have := cong_add H Λ f f' hv (cong_neg H Λ f f' (cong_of_mem H Λ f f' h))
    rwa [show v + -(v - w) = w by abel] at this
  · intro hw
    have := cong_add H Λ f f' hw (cong_of_mem H Λ f f' h)
    rwa [show w + (v - w) = v by abel] at this

end Gen

section Glob

variable {D : D7}

theorem ext_latP (Z : LocDat D) (p : PlF D) {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : Ext p β g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hβΛ : Formalism.HermitianLatticesTheory.gmap β Λ = Λ) {v : Vp D p} (hv : v ∈ lattice₂ D Z.M p Λ) : g v ∈ lattice₂ D Z.M p Λ := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, hy, rfl⟩ := hv
    rw [hg y]
    refine Submodule.subset_span ⟨β y, ?_, rfl⟩
    rw [← hβΛ]
    exact Submodule.mem_map_of_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : g (o • v) = o • g v := by rw [Subring.smul_def, Subring.smul_def, map_smul]
    rw [e]; exact Submodule.smul_mem _ o hv

theorem ext_smulLat (Z : LocDat D) (p : PlF D) {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : Ext p β g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hβΛ : Formalism.HermitianLatticesTheory.gmap β Λ = Λ) (c : (D.s.atP p).Ep) {v : Vp D p}
    (hv : v ∈ (locH Z p).smulLat c (lattice₂ D Z.M p Λ)) : g v ∈ (locH Z p).smulLat c (lattice₂ D Z.M p Λ) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw, rfl⟩ := hv
    show g (c • w) ∈ _
    rw [map_smul]
    exact Submodule.subset_span ⟨g w, ext_latP Z p hg hβΛ hw, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : g (o • v) = o • g v := by rw [Subring.smul_def, Subring.smul_def, map_smul]
    rw [e]; exact Submodule.smul_mem _ o hv

end Glob

theorem iota_typed : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → ∀ β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, Formalism.HermitianLatticesTheory.gmap β Λ = Λ → (∀ a, frame F₂ a = β (frame F₁ a)) → IotaCompat Λ (lf D F0) F₁ F₂ β (gS D) → ∀ (p : PlF D) (g), Ext p β g → (Z.M p).split ≠ none → ∀ x' ∈ lattice₂ D Z.M p Λ, ∀ x ∈ lattice₂ D Z.M p Λ, x' ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F₁))) → x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame (lf D F0)))) → (Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (x - x') ↔ Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (x - g x')) := by
  intro D Z u u' F0 Λ hR F₁ F₂ _ _ β _ hβΛ _ hIota p g hg hsp x' hx'Λ x hxΛ hx' hx
  have hΛ : Submodule.IsLattice D.host.E Λ := hR.2.1.1
  have hLD := _root_.GlobalTheory.IotaDense.iota_dense D p
  obtain ⟨l, hl, hxl⟩ := _root_.GlobalTheory.LocApprox.approx D Z p hLD Λ hΛ (lf D F0) x hxΛ hx
  obtain ⟨l', hl', hxl'⟩ := _root_.GlobalTheory.LocApprox.approx D Z p hLD Λ hΛ F₁ x' hx'Λ hx'
  obtain ⟨a, ha1, ha2⟩ := _root_.GlobalTheory.CrtG.exists_one_here_zero_elsewhere D p
  have hlΛ : l ∈ Λ := (Submodule.mem_inf.1 hl).1
  have hl'Λ : l' ∈ Λ := (Submodule.mem_inf.1 hl').1
  have hβl' : β l' ∈ Λ := by rw [← hβΛ]; exact Submodule.mem_map_of_mem hl'Λ
  have e1 : Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (x - x') ↔
      Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (baseChange₂ D p (l - l')) := by
    apply cong_iff_of_sub
    have e : x - x' - baseChange₂ D p (l - l') = (x - baseChange₂ D p l) - (x' - baseChange₂ D p l') := by rw [map_sub]; abel
    rw [e]; exact sub_mem hxl hxl'
  have e2 : Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (x - g x') ↔
      Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (baseChange₂ D p (l - β l')) := by
    apply cong_iff_of_sub
    have e : x - g x' - baseChange₂ D p (l - β l') = (x - baseChange₂ D p l) - g (x' - baseChange₂ D p l') := by
      rw [map_sub, map_sub, hg l']; abel
    rw [e]; exact sub_mem hxl (ext_smulLat Z p hg hβΛ _ hxl')
  rw [e1, e2, ← _root_.GlobalTheory.IotaLocGlob.locglob D Z p hsp a ha1 ha2 Λ hΛ (lf D F0) F₁ (l - l') (sub_mem hlΛ hl'Λ), ← _root_.GlobalTheory.IotaLocGlob.locglob D Z p hsp a ha1 ha2 Λ hΛ (lf D F0) F₂ (l - β l') (sub_mem hlΛ hβl')]
  have hal : a • l ∈ Lrep Λ (lf D F0) := Submodule.smul_mem _ a hl
  have hal' : a • l' ∈ Lrep Λ F₁ := Submodule.smul_mem _ a hl'
  have h := hIota (a • l') hal' (a • l) hal
  have e3 : β (a • l') = a • β l' := by
    rw [← algebraMap_smul D.host.E a l', LinearEquiv.map_smul, algebraMap_smul]
  rw [e3] at h
  rw [smul_sub, smul_sub]
  exact h

end GlobalTheory.IotaLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowCountsUniformConstantsFamilies
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.RowCounts

theorem uniform_counts : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ c3 cH cS c4 thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm →
    (∀ C ≥ c3, (OwnEv Fm fun C' Cl x i => ∀ u u',
      VanishingOnXAndXPlus.adm20 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A 3 C)) ∧
    (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.HerrCocycleExtensionClass (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cH) ∧
    (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cS) ∧
    (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm21 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A c4) := by
  intro hM Cg cb Cu cT CT C0 A
  obtain ⟨C1a, hC1⟩ := _root_.GlobalTheory.Mass.PrimMeanRow.main 1 one_pos
  obtain ⟨c3, hC3⟩ := GlobalTheory.LoopC.PairMean.main Cg cb Cu cT CT C0 A 3 (max C1a 0) (le_max_right _ _)
  obtain ⟨cH, -, hHH⟩ := GlobalTheory.GramHeight.height_bounds Cg cb Cu cT CT C0 A
  obtain ⟨cS, hSW⟩ := GlobalTheory.LoopC.GenericMean.main Cg cb Cu cT CT C0 A
  obtain ⟨c4, hC4⟩ := GlobalTheory.LoopC.Partner.partners_le Cg cb Cu cT CT C0 A
  refine ⟨c3, cH, cS, c4, 1, fun eps Fm _ hl => ⟨fun C hC => ⟨0, fun x _ i u u' => ?_⟩,
    ⟨0, fun x _ i u u' => ?_⟩, ⟨0, fun x _ i u u' => ?_⟩, ⟨0, fun x _ i u u' => ?_⟩⟩⟩
  · exact hC3 C hC _ _ u u' _ _ hl (_root_.GlobalTheory.Mass.RowsRawMass.main _ u)
      (hC1 _ (le_max_left _ _) _ _ u u' _ _ Cg cb Cu cT CT C0 A hl)
  · exact hHH _ _ u u' _ _ hl
  · exact hSW _ _ u u' _ _ hl
      (_root_.GlobalTheory.Mass.PrimMeanCorankOne.main _ _ u u' _ _ Cg cb Cu cT CT C0 A (Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified hM _))
  · exact hC4 _ _ u u' _ _ hl

end GlobalTheory.RowCounts
end

