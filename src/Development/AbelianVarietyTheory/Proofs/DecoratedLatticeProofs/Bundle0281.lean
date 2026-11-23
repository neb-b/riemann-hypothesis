module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0087
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GrowthOfBasic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbstractDiagonalBoundCollisionsCountedOnce
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

noncomputable section

namespace GlobalTheory

theorem diag_abstract_collisions_once :
    ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (one : H) (Pg B A₁ A₂ : ℝ), 0 ≤ Pg → X.AbsConv → X.NormExpansionOn X.genSet → X.NormExpansionOn X.ngSet → X.GGBound Pg → X.RowOrth → X.CorankPos → Formalism.L2.SG.RowsOther.IdOne X one → X.pairAbs (X.big X.nzSet) ≤ B → X.pairSum (X.one X.genSet) ≤ A₁ → X.pairSum (X.one X.ngSet) ≤ A₂ → ‖X.K0 - one‖ ^ 2 ≤ 2 * Pg * (B + A₁ + A₂) := by
  intro τ Rw I H H₁ _ _ _ _ _ _ X one Pg B A₁ A₂ hPg hA hNg hNn hG hO hC hI hB h1 h2
  have hE := Formalism.FourierDecayAlt.P.equal_index
  have hF := Formalism.FourierDecayAlt.P.subfamilyAlt τ Rw I H H₁ X hA
  obtain ⟨_, _, hng⟩ := Formalism.FourierDecayAlt.P.pair_split_alt τ Rw I H H₁ X hA hO hC

  have hgen : X.PhiEq X.genSet = X.pairSum (X.big X.genSet) + X.pairSum (X.one X.genSet) := by
    let Y : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁ := { X with scal := fun _ _ => True }
    obtain ⟨_, hg, _⟩ := Formalism.FourierDecayAlt.P.pair_split_alt τ Rw I H H₁ Y hA hO hC
    have e1 : Y.nsc Y.genSet = ∅ := by
      ext p; simp [Y, Formalism.FourierDecayAlt.PB.Terms.nsc]
    have e2 : Y.sc Y.genSet = X.one X.genSet := by
      ext p; simp [Y, Formalism.FourierDecayAlt.PB.Terms.sc, Formalism.FourierDecayAlt.PB.Terms.one, Formalism.FourierDecayAlt.PB.Terms.allPairs,
        Formalism.FourierDecayAlt.PB.Terms.genSet]
    have e0 : Y.pairSum ∅ = 0 := by simp [Formalism.FourierDecayAlt.PB.Terms.pairSum]
    rw [e1, e2, e0, add_zero] at hg
    exact hg

  have hS : Summable (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) := by
    have hv := hA.2.1
    have hm : Summable (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖) :=
      hv.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_inner_le_norm _ _) hm
  have hdisj : Disjoint (X.big X.genSet) (X.big X.ngSet) := by
    rw [Set.disjoint_left]
    intro p hp hq
    exact hq.1.1.2 hp.1.1.2
  have hunion : X.pairAbs (X.big X.genSet) + X.pairAbs (X.big X.ngSet) =
      X.pairAbs (X.big X.genSet ∪ X.big X.ngSet) := by
    unfold Formalism.FourierDecayAlt.PB.Terms.pairAbs
    rw [Set.indicator_union_of_disjoint hdisj]
    beta_reduce
    rw [Summable.tsum_add (hS.indicator _) (hS.indicator _), mul_add]
  have hsub : X.big X.genSet ∪ X.big X.ngSet ⊆ X.big X.nzSet := by
    rintro p (hp | hp)
    · exact ⟨⟨hp.1.1.1, hp.1.2.1.1, hp.1.2.2⟩, hp.2⟩
    · exact ⟨⟨hp.1.1.1, hp.1.2.1.1, hp.1.2.2⟩, hp.2⟩
  have hsum : X.pairAbs (X.big X.genSet) + X.pairAbs (X.big X.ngSet) ≤ B := by
    rw [hunion]; exact (hF _ _ hsub).1.trans hB
  have bg : X.pairSum (X.big X.genSet) ≤ X.pairAbs (X.big X.genSet) :=
    (le_abs_self _).trans (hF _ _ le_rfl).2
  have bn : X.pairSum (X.big X.ngSet) ≤ X.pairAbs (X.big X.ngSet) :=
    (le_abs_self _).trans (hF _ _ le_rfl).2
  have g1 : ‖X.part X.genSet‖ ^ 2 ≤ Pg * (X.pairAbs (X.big X.genSet) + A₁) := by
    have := Formalism.FourierDecayAlt.P.price_of_index hE τ Rw I H H₁ X Pg X.genSet hNg hG
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hPg)
    rw [hgen]; linarith
  have g2 : ‖X.part X.ngSet‖ ^ 2 ≤ Pg * (X.pairAbs (X.big X.ngSet) + A₂) := by
    have := Formalism.FourierDecayAlt.P.price_of_index hE τ Rw I H H₁ X Pg X.ngSet hNn hG
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hPg)
    rw [hng]; linarith
  have hK : X.K0 - one = X.part X.genSet + X.part X.ngSet := by
    unfold Formalism.FourierDecayAlt.PB.Terms.K0
    rw [← hI]
    abel
  rw [hK]
  have hpar : ‖X.part X.genSet + X.part X.ngSet‖ ^ 2 ≤
      2 * ‖X.part X.genSet‖ ^ 2 + 2 * ‖X.part X.ngSet‖ ^ 2 := by
    have := norm_add_le (X.part X.genSet) (X.part X.ngSet)
    have h0 := norm_nonneg (X.part X.genSet + X.part X.ngSet)
    nlinarith [sq_nonneg (‖X.part X.genSet‖ - ‖X.part X.ngSet‖), norm_nonneg (X.part X.genSet),
      norm_nonneg (X.part X.ngSet)]
  have hfin : Pg * (X.pairAbs (X.big X.genSet) + A₁) + Pg * (X.pairAbs (X.big X.ngSet) + A₂) ≤
      Pg * (B + A₁ + A₂) := by
    rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ hPg; linarith
  linarith

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoeLatFrameOfEq
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.AdForm.VacStd

theorem coe_latFrame_of_eq {D : D7} (S : HSp D) (hs : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (h : S = Formalism.BasicNotions.Examples₂.posSpace hs N) :
    (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E)) = GlobalTheory.AdForm.intVec D S.rank := by
  subst h
  ext x
  show x ∈ GlobalTheory.PlaceModel.latFrame _ ↔ ∀ k, IsIntegral ℤ (x k)
  rw [GlobalTheory.PlaceModel.mem_latFrame]
  exact Formalism.IndefR.Seed.FrmC.stdLat_std hs N (fun _ => false) N 0 x

theorem gram_of_eq {D : D7} (S : HSp D) (hs : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (h : S = Formalism.BasicNotions.Examples₂.posSpace hs N) : S.gram = 1 := by
  subst h
  refine Matrix.ext fun a b => ?_
  exact (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs N (fun _ => false) N 0 a b).trans
    (by
      by_cases hab : a = b
      · subst hab
        rw [Matrix.one_apply_eq]
        exact (if_pos rfl).trans (by simp [Formalism.BasicNotions.Examples₂.sgn])
      · rw [Matrix.one_apply_ne hab]
        exact if_neg hab)

theorem cartan_of_gram {D : D7} {S : HSp D} (h : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have e : gramAt D S τ = 1 := by rw [gramAt, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e]
  exact ⟨Matrix.mul_one _, by simp, by rw [Matrix.mul_one]; exact Matrix.PosDef.one⟩

end GlobalTheory.AdForm.VacStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionAbsSumBoundOfTwoRowBounds
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem collS_of_rowBounds : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ CT C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → CT ≤ C → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word) (T : TermTie D) (Z : LoopTie D large₂ T u u 1) (C' Cl Cg cb Cu cT C0 : ℝ), thr ≤ C' → thr ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv → TieAt hF hI large₂ u T Z → UnitaryVolumeMass.FormAt D u → BridgeLemma.RowsND T Z C → BridgeLemma.RowsDeg T Z C → CollS Y u := by
  intro hS CT C hC hCT
  have he : (1 : ℝ) ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    nlinarith
  have hC1 : (1 : ℝ) ≤ C := by nlinarith
  obtain ⟨K₀, hK⟩ := _root_.GlobalTheory.Core.Deg.corankSums_expLoss C hC1
  refine ⟨max K₀ 4, ?_⟩
  intro D large₂ X Y hF hI u T Z C' Cl Cg cb Cu cT C0 hC' hCl hH hCc hAbs hTie hFo hn hd
  have hK₀ : K₀ ≤ C' := le_trans (le_max_left _ _) hC'
  have hC'1 : (1 : ℝ) ≤ C' := by linarith [le_max_right K₀ 4]
  have hCl4 : (4 : ℝ) ≤ Cl := le_trans (le_max_right _ _) hCl
  have hHy := Formalism.MainNotions.count_hypotheses_diagonal_words D large₂ C' Cl Cg cb Cu cT CT C0 1 hH.2.1 hH.1 hH.2.2 (by linarith) hC'1 le_rfl u
  have hXi := _root_.GlobalTheory.Core.Deg.xiSizes_explicit hS C hC D large₂ u u C' Cl Cg cb Cu cT CT C0 1 (by linarith) hHy
  have hP := Formalism.L2.SG.LoopsCut.params_at hH X u hCl4 hCT hC1 hK₀
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b D large₂
  have hP1 : Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v
      (Cnt.NT D u) 1 := by
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, _, _⟩ := hP
    refine ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, le_rfl, ?_⟩
    apply Real.one_le_exp
    have hl : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
    have hC0 : (0 : ℝ) ≤ C := by linarith
    positivity
  have hGam0 : 0 ≤ GamS D large₂ := (Real.exp_pos _).le
  have hGam8 : GamS D large₂ ≤ Real.exp ((D.R.k : ℝ) / 8) := by
    unfold GamS
    apply Real.exp_le_exp.2
    have h1 : 8 * large₂.CGam ≤ C' := hH.1.1
    have h2 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hH.1.2.1
    have hL := Formalism.MainNotions.BridgeLemma.d_one_le_L D large₂
    have hM : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
    nlinarith
  obtain ⟨hND, hDG⟩ := hK D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v (Cnt.NT D u) (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) hP1 hXi hGam0 hGam8
  obtain ⟨hJ, hW, hFC, _, _, _, _⟩ := hTie
  have hG := Formalism.L2.SG.LoopTieOf.gammaFixed_of_hypotheses Y hH
  have hm := Formalism.MainNotions.BridgeLemma.d_m_eq D
  have hg : (X.B.g : ℝ) = gg D := by rw [X.g_eq]; unfold gg; push_cast; ring
  have hcls : ∀ s, 2 ≤ s → s ≤ D.R.k → Formalism.L2.SG.LoopsCut.ClassLe (Y.tO u u) (Formalism.L2.SG.LoopsCut.bigS (Y.tO u u) s)
      ((fun s : ℕ => (D.duS u : ℝ) *
        (Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
                  (BridgeLemma.XiB D large₂ u C) * BridgeLemma.rDD D u +
          Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
            (BridgeLemma.XiB D large₂ u C))) s) := by
    intro s h2 hk
    have base := Formalism.L2.SG.LoopTieOf.gam_mul_le hG Z hFo
      (Formalism.L2.SG.LoopTieOf.classS_le T hJ hW hFC Z C hn hd s h2 hk)
    rw [hm, ← hg] at base
    exact base
  have habs := _root_.GlobalTheory.Core.Deg.pairAbs_big_le_sum_classes _ _ _ _ _ (Y.tO u u) D.R.k _ hAbs
    (fun p _ => Formalism.L2.SG.LoopsCut.corank_le_k Y u u p.1 p.2) hcls
  have hdd : ddC X Y u u = (D.duS u : ℝ) * BridgeLemma.rDD D u := Formalism.L2.SG.LoopTieOf.ddC_eq hCc u u
  have hdu : duC X Y u = (D.duS u : ℝ) := hCc.2.2.1 u
  have hdr0 : 0 ≤ (D.duS u : ℝ) * BridgeLemma.rDD D u := hdd ▸ dd_nonneg hCc u u
  have hd0 : (0 : ℝ) ≤ (D.duS u : ℝ) := Nat.cast_nonneg _
  have hgg : ((X.B.g : ℕ) : ℝ) = (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by rw [X.g_eq]; push_cast; ring
  unfold CollS
  rw [hdd, hdu]
  set d : ℝ := (D.duS u : ℝ) with hdef
  set r : ℝ := BridgeLemma.rDD D u with hrdef
  set N := fun s : ℕ => Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) with hN
  set G := fun s : ℕ => Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C D.R.k (2 * D.R.rS + 2) D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
    (BridgeLemma.XiB D large₂ u C) with hGd
  have hsum : ∑ s ∈ Finset.Icc 2 D.R.k, d * (N s * r + G s) =
      d * r * ∑ s ∈ Finset.Icc 2 D.R.k, N s + d * ∑ s ∈ Finset.Icc 2 D.R.k, G s := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  calc _ ≤ ∑ s ∈ Finset.Icc 2 D.R.k, d * (N s * r + G s) := habs
    _ = d * r * ∑ s ∈ Finset.Icc 2 D.R.k, N s + d * ∑ s ∈ Finset.Icc 2 D.R.k, G s := hsum
    _ ≤ d * r * (√(X.B.g : ℝ))⁻¹ ^ (D.R.k * D.R.f) +
        d * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k) / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hND hdr0) (mul_le_mul_of_nonneg_left hDG hd0)
    _ = _ := by rw [hgg]; ring

end GlobalTheory.Core.Deg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColumnDimensionWindowThreeOfColumnCount
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Diag

theorem standingNumericalData_three_of_dataNW_rankMu : ∀ D : D7, DataNW D → (∀ u, GlobalTheory.Core.Rk.RankMu D u) → StandingNumericalData D 3 := by
  intro D hN hR
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h11⟩ := hN
  have hW : GlobalTheory.Diag.PG.DuWin D 3 := GlobalTheory.Diag.PG.duWin_three_of_count D fun u => by
    have := hR u
    unfold GlobalTheory.Core.Rk.RankMu at this
    rw [GlobalTheory.Core.Rk.d0_eq] at this
    exact this
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hW, h11⟩

end GlobalTheory.Core.Diag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingOpenOrbitUnfoldsToAdelicIntegral
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.OpenOrbit

open Set Filter GlobalTheory.Eis

variable {D : D7} {V : HSp D}

theorem io_one_mul (δ : GA D V) (x : GA D V × GA D V) : io V (δ, 1) * io V x = io V (δ * x.1, x.2) := by
  rw [← map_mul]; congr 1; ext <;> simp

section Terms

variable {μ : (AE D)ˣ →* Circle} {φ : GA D (dblSp V) → ℂ} {f₁ f₂ : GA D V → ℂ}

theorem term_eq (hf₁ : ∀ γ ∈ GQ V, ∀ g, f₁ (γ * g) = f₁ g) (δ : GQ V) (x : GA D V × GA D V) :
    dblIntegrand V μ (fun y => φ (io V (δ, 1) * y)) f₁ f₂ x =
      dblIntegrand V μ φ f₁ f₂ ((δ : GA D V) * x.1, x.2) := by
  simp only [dblIntegrand, io_one_mul, hf₁ _ δ.2]

theorem tsum_open_ne_top (hμ : IsHeckeChar D μ) {a : GL (Fin V.rank) (AE D)} {s : ℂ} (hφ : φ ∈ degPS V a μ s)
    {m : Measure (GA D V)} [SFinite m] {𝓕 : Set (GA D V)}
    (h : ∑' q : SiegelCosets V, ∫⁻ x in 𝓕 ×ˢ 𝓕,
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m ≠ ⊤) :
    ∑' δ : GQ V, ∫⁻ x, ‖dblIntegrand V μ (fun y => φ (io V (δ, 1) * y)) f₁ f₂ x‖ₑ
      ∂(m.restrict 𝓕).prod (m.restrict 𝓕) ≠ ⊤ := by
  rw [Measure.prod_restrict]
  refine ne_top_of_le_ne_top h (le_trans (le_of_eq (tsum_congr fun δ => ?_))
    (ENNReal.tsum_comp_le_tsum_of_injective (injective_mk_io (V := V)) (fun q : SiegelCosets V => ∫⁻ x in 𝓕 ×ˢ 𝓕,
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m)))
  set q : SiegelCosets V := mk _ ⟨io V (δ, 1), io_mem_GQ V δ.2 (one_mem _)⟩ with hq
  have e : (mk _ q.out : SiegelCosets V) = mk _ ⟨io V (δ, 1), io_mem_GQ V δ.2 (one_mem _)⟩ := Quotient.out_eq q
  obtain ⟨p, hp⟩ := mk_eq_iff.1 e
  have hE : (fun y => φ (io V (δ, 1) * y)) = fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x) := by
    funext y
    have h1 : io V (δ, 1) = ((p : GQ (dblSp V)) : GA D (dblSp V)) * ((q.out : GQ (dblSp V)) : GA D (dblSp V)) :=
      (congrArg Subtype.val hp).symm
    rw [h1, mul_assoc]
    exact apply_siegelQ_mul V a hμ hφ ⟨Subgroup.mem_subgroupOf.1 p.2, (p : GQ (dblSp V)).2⟩ _
  beta_reduce
  rw [hE]

theorem leftInv_open (hμ : IsHeckeChar D μ) {a : GL (Fin V.rank) (AE D)} {s : ℂ} (hφ : φ ∈ degPS V a μ s)
    (hf₁ : ∀ γ ∈ GQ V, ∀ g, f₁ (γ * g) = f₁ g) (hf₂ : ∀ γ ∈ GQ V, ∀ g, f₂ (γ * g) = f₂ g) :
    LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ (fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y)) f₁ f₂) := by
  rintro ⟨γ₁, γ₂⟩ ⟨h1, h2⟩ ⟨x₁, x₂⟩
  have hs : ∑' δ : GQ V, φ (io V (δ, 1) * io V ((γ₁, γ₂) * (x₁, x₂))) =
      ∑' δ : GQ V, φ (io V (δ, 1) * io V (x₁, x₂)) := by
    let e : GQ V ≃ GQ V := (Equiv.mulLeft (⟨γ₂, h2⟩ : GQ V)⁻¹).trans (Equiv.mulRight ⟨γ₁, h1⟩)
    conv_rhs => rw [← e.tsum_eq]
    refine tsum_congr fun δ => ?_
    simp only [io_one_mul, Prod.mk_mul_mk]
    have := apply_io_mul V a hφ γ₂ ((e δ : GA D V) * x₁) x₂
    rw [apply_detA hμ h2, Circle.coe_one, one_mul] at this
    rw [← this]
    congr 3
    simp [e, mul_assoc]
  simp only [dblIntegrand]
  rw [hs]
  simp only [Prod.mk_mul_mk, hf₁ _ h1, hf₂ _ h2, map_mul, apply_detA hμ h2, one_mul]

end Terms

theorem open_orbit : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ZetaConvH D.sp.cm.sig (gram_hdbl V) m φ (GlobalTheory.Eis.petCoef V m f₁ f₂) ∧ ∫ x, GlobalTheory.Eis.dblIntegrandQ V μ (fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y)) f₁ f₂ x ∂(autMeasure V m).prod (autMeasure V m) = zetaH D.sp.cm.sig (gram_hdbl V) m φ (GlobalTheory.Eis.petCoef V m f₁ f₂) := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  haveI := hm
  have hF : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  set 𝓕 := stdDom (GQ V) with h𝓕
  have hφc : Continuous φ := hφ.2.1
  set E : GA D (dblSp V) → ℂ := fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y) with hEdef
  set H : GA D V × GA D V → ℂ := dblIntegrand V μ φ f₁ f₂ with hHdef
  set T : GQ V → GA D V × GA D V → ℂ := fun δ => dblIntegrand V μ (fun y => φ (io V (δ, 1) * y)) f₁ f₂ with hTdef
  set K : GA D V × GA D V → ℂ := fun p => H (p.1 * p.2, p.1) with hKdef
  have hHc : Continuous H := continuous_dblIntegrand hμ hφc h₁.continuous h₂.continuous
  have hT : ∀ (δ : GQ V) (x : GA D V × GA D V), T δ x = H ((δ : GA D V) * x.1, x.2) := fun δ x => term_eq h₁.1 δ x
  have hTc : ∀ δ : GQ V, Continuous (T δ) := fun δ => by
    rw [show T δ = fun x => H ((δ : GA D V) * x.1, x.2) from funext (hT δ)]
    exact hHc.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hTm : ∀ δ : GQ V, Measurable fun x => ‖T δ x‖ₑ := fun δ => (hTc δ).measurable.enorm
  have hKc : Continuous K := hHc.comp ((continuous_fst.mul continuous_snd).prodMk continuous_fst)

  have hbd : ∑' δ : GQ V, ∫⁻ x, ‖T δ x‖ₑ ∂(m.restrict 𝓕).prod (m.restrict 𝓕) ≠ ⊤ :=
    tsum_open_ne_top hμ hφ ((GlobalTheory.Core.Rk.AbsConv.absConv_unfolded D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂).1 𝓕 hF)
  have hTint : ∀ δ : GQ V, Integrable (T δ) ((m.restrict 𝓕).prod (m.restrict 𝓕)) := fun δ =>
    ⟨(hTc δ).aestronglyMeasurable, lt_of_le_of_lt
      (ENNReal.le_tsum (f := fun δ : GQ V => ∫⁻ x, ‖T δ x‖ₑ ∂(m.restrict 𝓕).prod (m.restrict 𝓕)) δ)
      (lt_top_iff_ne_top.2 hbd)⟩

  have hlin : ∀ x₂, ∫⁻ x₁, ‖H (x₁, x₂)‖ₑ ∂m = ∑' δ : GQ V, ∫⁻ x₁ in 𝓕, ‖T δ (x₁, x₂)‖ₑ ∂m := fun x₂ => by
    rw [hF.lintegral_eq_tsum'' (fun x₁ => ‖H (x₁, x₂)‖ₑ)]
    refine tsum_congr fun δ => ?_
    simp only [hT, Subgroup.smul_def, smul_eq_mul]
  have hlK : ∫⁻ p, ‖K p‖ₑ ∂(m.restrict 𝓕).prod m =
      ∑' δ : GQ V, ∫⁻ x, ‖T δ x‖ₑ ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := by
    rw [lintegral_prod _ hKc.measurable.enorm.aemeasurable]
    have h1 : ∀ x₂, ∫⁻ g, ‖K (x₂, g)‖ₑ ∂m = ∫⁻ x₁, ‖H (x₁, x₂)‖ₑ ∂m := fun x₂ =>
      lintegral_mul_left_eq_self (fun x₁ => ‖H (x₁, x₂)‖ₑ) x₂
    simp_rw [h1, hlin]
    rw [lintegral_tsum (fun δ => ((hTm δ).lintegral_prod_left').aemeasurable)]
    refine tsum_congr fun δ => ?_
    rw [lintegral_prod_symm _ (hTm δ).aemeasurable]
  have hKint : Integrable K ((m.restrict 𝓕).prod m) :=
    ⟨hKc.aestronglyMeasurable, show ∫⁻ p, ‖K p‖ₑ ∂(m.restrict 𝓕).prod m < ⊤ by rw [hlK]; exact lt_top_iff_ne_top.2 hbd⟩
  have hHint : ∀ᵐ x₂ ∂(m.restrict 𝓕), Integrable (fun x₁ => H (x₁, x₂)) m := by
    filter_upwards [hKint.prod_right_ae] with x₂ hx
    have := hx.comp_mul_left x₂⁻¹
    simpa [hKdef, mul_inv_cancel_left] using this

  have hli : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) := leftInv_open hμ hφ h₁.1 h₂.1
  have hQ : dblIntegrandQ V μ E f₁ f₂ = dblIntegrand V μ E f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
    funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk hli _ _)
  have hmp : MeasurePreserving (Prod.map (sec (GQ V)) (sec (GQ V))) ((autMeasure V m).prod (autMeasure V m))
      ((m.restrict 𝓕).prod (m.restrict 𝓕)) := measurePreserving_sec.prod measurePreserving_sec
  have S3 : ∫ q, dblIntegrandQ V μ E f₁ f₂ q ∂(autMeasure V m).prod (autMeasure V m) =
      ∫ x, dblIntegrand V μ E f₁ f₂ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := by
    rw [hQ]; exact hmp.integral_comp (measurableEmbedding_sec.prodMap measurableEmbedding_sec) _
  have S4 : ∫ x, dblIntegrand V μ E f₁ f₂ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) =
      ∑' δ : GQ V, ∫ x, T δ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := by
    rw [← integral_tsum (fun δ => (hTc δ).aestronglyMeasurable) hbd]
    congr 1; funext x
    simp only [hTdef, hEdef, dblIntegrand, mul_assoc]
    exact tsum_mul_right.symm
  have S5 : ∀ δ : GQ V, ∫ x, T δ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) =
      ∫ x₂ in 𝓕, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := fun δ => integral_prod_symm _ (hTint δ)
  have S6 : ∑' δ : GQ V, ∫ x₂ in 𝓕, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m =
      ∫ x₂ in 𝓕, ∑' δ : GQ V, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := by
    refine (integral_tsum (fun δ => ?_) ?_).symm
    · exact (((hTc δ).comp continuous_swap).aestronglyMeasurable
        (μ := (m.restrict 𝓕).prod (m.restrict 𝓕))).integral_prod_right'
    · refine ne_top_of_le_ne_top hbd (ENNReal.tsum_le_tsum fun δ => ?_)
      rw [lintegral_prod_symm _ (hTm δ).aemeasurable]
      exact lintegral_mono fun x₂ => enorm_integral_le_lintegral_enorm _
  have S7 : ∀ᵐ x₂ ∂(m.restrict 𝓕), ∑' δ : GQ V, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m = ∫ x₁, H (x₁, x₂) ∂m := by
    filter_upwards [hHint] with x₂ hx
    rw [hF.integral_eq_tsum'' _ hx]
    refine tsum_congr fun δ => ?_
    simp only [hT, Subgroup.smul_def, smul_eq_mul]
  have S8 : ∀ x₂, ∫ x₁, H (x₁, x₂) ∂m = ∫ g, K (x₂, g) ∂m := fun x₂ =>
    (integral_mul_left_eq_self (fun x₁ => H (x₁, x₂)) x₂).symm
  have S9 : ∫ x₂ in 𝓕, ∫ g, K (x₂, g) ∂m ∂m = ∫ g, ∫ x₂ in 𝓕, K (x₂, g) ∂m ∂m := by
    rw [← integral_prod _ hKint, integral_prod_symm _ hKint]
  have MirabolicColumnBlock : ∀ g, ∫ x₂ in 𝓕, K (x₂, g) ∂m = φ (io V (g, 1)) * conj (petCoef V m f₁ f₂ g) := fun g => by
    have hl1 : LeftInv (GQ V) (rTr V g f₁) := fun γ hγ x => (h₁.mul_right g).1 γ hγ x
    have hl2 : LeftInv (GQ V) f₂ := h₂.1
    simp only [petCoef]
    rw [petersson_eq hF hl1 hl2, ← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x₂ => ?_)
    simp only [hKdef, hHdef, dblIntegrand_mul hφ, rTr, map_mul, Complex.conj_conj]
    ring
  refine ⟨?_, ?_⟩
  · rw [zetaConvH_iff]
    exact hKint.integral_prod_right.congr (Eventually.of_forall fun g => MirabolicColumnBlock g)
  · calc ∫ q, dblIntegrandQ V μ E f₁ f₂ q ∂(autMeasure V m).prod (autMeasure V m)
        = ∫ x, dblIntegrand V μ E f₁ f₂ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := S3
      _ = ∑' δ : GQ V, ∫ x, T δ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := S4
      _ = ∑' δ : GQ V, ∫ x₂ in 𝓕, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := tsum_congr S5
      _ = ∫ x₂ in 𝓕, ∑' δ : GQ V, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := S6
      _ = ∫ x₂ in 𝓕, ∫ x₁, H (x₁, x₂) ∂m ∂m := integral_congr_ae S7
      _ = ∫ x₂ in 𝓕, ∫ g, K (x₂, g) ∂m ∂m := integral_congr_ae (Eventually.of_forall S8)
      _ = ∫ g, ∫ x₂ in 𝓕, K (x₂, g) ∂m ∂m := S9
      _ = ∫ g, φ (io V (g, 1)) * conj (petCoef V m f₁ f₂ g) ∂m := integral_congr_ae (Eventually.of_forall MirabolicColumnBlock)
      _ = zetaH D.sp.cm.sig (gram_hdbl V) m φ (petCoef V m f₁ f₂) := (zetaH_eq _ _ _ _).symm

end GlobalTheory.Core.Rk.OpenOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroupStatement
section
theorem GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup : GlobalTheory.Published.HarishChandraModules :=
  GlobalTheory.HcPort.print_harishChandraModules
end

