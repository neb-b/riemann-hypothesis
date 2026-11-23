module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsTies
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0079
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0087
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0082
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0041
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DegreeRatioFormulaStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CriticalLevelLowOfRefined
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsCut
  Formalism.L2.SG.LoopsFinal Formalism.L2.SG.LoopsEv Formalism.FourierDecayAlt

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure ConcAt0 (D : D7) (T : TermTie D) where
  X : HidaSetting D
  Y : Full X
  hF : FinX Y
  hI : SIso D.s (sOf hF)
  jt : JtPin hF hI T
  wr : WRowPin hF hI T
  fc : FibreCount Y

section TransportedAlt

theorem loop_evaluation_threshold_zero (hLC : PN.LoopCores) (hSub : PB.SubFamily) (hS : Formalism.HermitianLatticesTheory.SiegelMassRatio)
    (Cg cb Cw cT CT C0 A C₀ : ℝ) :
    ∃ C'₀ Cl₀ : ℝ, ∀ {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
      (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
        LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
      (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt0 (Fm.D x i) (At x hx i)),
      (∀ C : ℝ, C₀ ≤ C → OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) (u u' : (Fm.D x i).what₂.Word),
        Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cw cT CT C0 A →
          Formalism.MainNotions.BridgeLemma.RowsND (At x hx i) (Yt x hx i u u') C ∧ Formalism.MainNotions.BridgeLemma.RowsDeg (At x hx i) (Yt x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsOne (At x hx i) (Yt x hx i u u') C) →
      (OwnEv Fm fun C' Cl x i =>
        Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cw cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) →
      OwnEv Fm fun C' Cl x i => C'₀ ≤ C' → Cl₀ ≤ Cl →
        ∀ (hx : Fm.x1 < x) (u u' : (Fm.D x i).what₂.Word),
          Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cw cT CT C0 A → ConcTie (Cc x hx i).X (Cc x hx i).Y →
          ((Cc x hx i).Y.tO u u').AbsConv →
          ((Cc x hx i).Y.tO u u').RowBig (epsL (Fm.D x i)) (ddC (Cc x hx i).X (Cc x hx i).Y u u') ∧
          ((Cc x hx i).Y.tO u u').RowNotScalar (epsL (Fm.D x i)) (ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
  obtain ⟨C₃, _, HX⟩ := xiSizesC_of hS Cg cb Cw cT CT C0 A
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (max C₀ C₃) (max CT 1) := ⟨_, rfl⟩
  have hCC₀ : C₀ ≤ C := by rw [hCdef]; exact le_max_of_le_left (le_max_left _ _)
  have hCC₃ : C₃ ≤ C := by rw [hCdef]; exact le_max_of_le_left (le_max_right _ _)
  have hCT : CT ≤ C := by rw [hCdef]; exact le_max_of_le_right (le_max_left _ _)
  have hC : 1 ≤ C := by rw [hCdef]; exact le_max_of_le_right (le_max_right _ _)
  obtain ⟨K₀, hJ⟩ := Formalism.L2.SG.RowsOther.rowLoops_of_input hLC hSub C hC
  obtain ⟨a3, b3, HX'⟩ := HX C hCC₃
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = max 1 C0 := ⟨_, rfl⟩
  have hA₀1 : 1 ≤ A₀ := by rw [hA₀]; exact le_max_left _ _
  refine ⟨max a3 K₀, max b3 (max 4 (3 + 6 * Real.log (3 * A₀))), ?_⟩
  intro eps Fm C1 At Yt Cc HR hFo
  refine (OwnEv.and (HR C hCC₀) hFo).mono ?_
  rintro C' Cl x i ⟨H1, H2⟩ hC' hCl hx u u' hH hT hA
  have ha3 : a3 ≤ C' := le_trans (le_max_left _ _) hC'
  have hK₀ : K₀ ≤ C' := le_trans (le_max_right _ _) hC'
  have hb3 : b3 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCl4 : 4 ≤ Cl := le_trans (le_max_of_le_right (le_max_left _ _)) hCl
  have hClA : 3 + 6 * Real.log (3 * A₀) ≤ Cl := le_trans (le_max_of_le_right (le_max_right _ _)) hCl
  obtain ⟨hn, hd, h1⟩ := H1 hx u u' hH
  have hFo' := H2 hH.1 u
  have hGP : GamPin (Cc x hx i).Y := gammaFixed_of_hypotheses (Cc x hx i).Y hH.1
  have hXiH := HX' C' Cl ha3 hb3 (Fm.D x i) (Fm.L x i) u u' hH
  have hP := params_at hH.1 (Cc x hx i).X u hCl4 hCT hC hK₀
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b (Fm.D x i) (Fm.L x i)
  have hb0 : (0 : ℝ) < (Fm.L x i).sc.b := by linarith
  have hk0 : (0 : ℝ) < (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < (Fm.D x i).R.k)
  have hg : 0 < ((Cc x hx i).X.B.g : ℝ) := by
    have h5 : (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 ≤ ((Cc x hx i).X.B.g : ℝ) := hP.2.2.2.2.1
    have h8 : 0 < (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 := by positivity
    linarith
  have hv : 0 ≤ (Fm.D x i).host.v := by linarith [hP.2.2.2.2.2.2.1]
  have hC0' : (0 : ℝ) ≤ C := by linarith
  have hGam : 0 ≤ GamS (Fm.D x i) (Fm.L x i) := by unfold GamS; exact (Real.exp_pos _).le
  have HS : ∀ s, 2 ≤ s → s ≤ (Fm.D x i).R.k →
      ClassLe ((Cc x hx i).Y.tO u u') (bigS ((Cc x hx i).Y.tO u u') s)
        (A₀ * rowS C (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f s (Fm.L x i).sc.b ((Cc x hx i).X.B.g : ℝ)
          (Fm.D x i).host.v (GamS (Fm.D x i) (Fm.L x i)) (Formalism.MainNotions.BridgeLemma.XiB (Fm.D x i) (Fm.L x i) u C) *
          ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
    intro s h2 hk
    have hX0 := xi_nonneg hXiH s h2 hk
    rw [hA₀]
    exact rowsSC_at (At x hx i) (Cc x hx i).jt (Cc x hx i).wr (Cc x hx i).fc hGP (Yt x hx i u u') hFo' hT
      hH C hn hd s h2 hk (ndRow_nonneg hC0' hb0 hg hv hGam hX0) (degRow_nonneg hC0' hb0 hg hv hGam hX0)
  have H1' : ClassLe ((Cc x hx i).Y.tO u u') (((Cc x hx i).Y.tO u u').nsc ((Cc x hx i).Y.tO u u').genSet)
      (A₀ * oneT C (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f (Fm.L x i).sc.b ((Cc x hx i).X.B.g : ℝ)
        (GamS (Fm.D x i) (Fm.L x i)) * ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
    rw [hA₀]
    exact oneSC_at (At x hx i) (Cc x hx i).jt (Cc x hx i).wr (Cc x hx i).fc hGP (Yt x hx i u u') hFo' hT
      C0 C hC0' h1
  obtain ⟨Al, NT', Gam, Xi, hAl, hP', hX', h6, hAmp⟩ :=
    loopsAmp_at hH hT hA hC hCT hK₀ hA₀1 hCl4 hClA hXiH HS H1'
  exact hJ _ _ _ _ _ ((Cc x hx i).Y.tO u u') (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f Al (Fm.L x i).sc.b
    ((Cc x hx i).X.B.g : ℝ) (Fm.D x i).host.v NT' Gam Xi (ddC (Cc x hx i).X (Cc x hx i).Y u u')
    hAl hP' hX' h6 (dd_nonneg hT u u') hA
    (Formalism.L2.SG.RowsOther.loopsInput_of_amp _ hA.2.2.le _ _ _ _ _ _ _ _ _ _ _ hAmp)

end TransportedAlt

section Fam5

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)
  (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, HidaSetting (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Full (X x hx i))
  (hF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FinX (Y x hx i))
  (hI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SIso (Fm.D x i).s (sOf (hF x hx i)))
  (hCT : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcTie (X x hx i) (Y x hx i))


end Fam5

end Formalism.L2.SG.LoopsTies
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MassDataPosAllOf
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.MassDataX

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc Formalism.L2.SG.Pf.MassDataPos Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DvPosC : Prop := ∀ {D : D7} (X : HidaSetting D) (v : NumberField.InfinitePlace X.B.I.F), 0 < X.dv v

theorem recPosC_of_dv {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hDv : DvPosC) (hX : HypX X hb FdN FdN' u u') :
    RecPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  have hTie := hX.1
  have hcol := (inColumnsAt_holds X hb hK FdN FdN' u u' X0 (Formalism.L2.SG.LocVol.locOf X u u' ψ)
    ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ hX)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < Formalism.L2.SG.RealObj.degX X
    unfold Formalism.L2.SG.RealObj.degX
    exact Finset.prod_pos fun v _ => hDv X v
  · exact Nat.cast_pos.mpr (finrank_Vpi_pos X u)
  · exact Nat.cast_pos.mpr (finrank_Vpi_pos X u')
  · exact massH_pos X u
  · exact massH_pos X u'
  · show (0 : ℝ) < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d
    rw [show (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d = _ from hcol.1]
    exact mul_pos (Nat.cast_pos.mpr (finrank_Vpi_pos X u))
      (div_pos (covolH_pos X hb u hTie) (mul_pos (volH_pos X hb u hTie) (muHpp_pos X hb hK u)))
  · show (0 : ℝ) < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d'
    rw [show (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d' = _ from hcol.2.2.1]
    exact mul_pos (Nat.cast_pos.mpr (finrank_Vpi_pos X u'))
      (div_pos (covolH_pos X hb u' hTie) (mul_pos (volH_pos X hb u' hTie) (muHpp_pos X hb hK u')))

end Formalism.L2.SG.Pf.MassDataX

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups ValuativeRel Formalism.L2.SG.SpectralTiesReal
open Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DensNonnegAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (Lsp : LocSp D T.Y.M) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]),
    0 ≤ supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p

theorem massDataPosAll_of (hP : ProdConvAll) (hSW : PI.VolStabS.MassDataS.SWXS) (hDv : Formalism.L2.SG.Pf.MassDataX.DvPosC)
    (hDN : DensNonnegAll) : MassDataPosAll := by
  intro D T u u' X0 C Th Q i0 i0' νq Lsp ϖ hne hst hCT hdet hC hTh _
  have hK : T.X.LevelSubgroupNormalized := hCT.1
  have hV : 0 < T.X.volK2 := ENNReal.toReal_pos hK.2.2.1.ne' hK.2.2.2.ne
  have hX : Formalism.L2.SG.TypedSets.HypX T.X T.hb (T.Y.FN u) (T.Y.FN u') u u' :=
    ⟨T.measTie, hK, T.Y.FN_fund u, T.Y.FN_fund u'⟩
  exact Formalism.L2.SG.Pf.MassDataPos.massDataPosC_of (hL := Formalism.L2.SG.Pf.MassDataX.locHaarPosC_holds ..)
    (hCv := Formalism.L2.SG.Pf.MassDataX.covolPosC_of (hSW := hSW) (hψ := T.ψ_char) (hC := T.measCompat)
      (hT := T.measTie) (hdet := hdet) ..)
    (hQv := Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of T.X T.hb T.Y u u' X0 T.ψ _ _ C Th _ Q _ _ i0 i0' νq hK hV)
    (hR := Formalism.L2.SG.Pf.MassDataX.recPosC_of_dv T.X T.hb T.Y.hK _ _ u u' X0 T.ψ _ _ C Th _ Q _ _ i0 i0' νq hDv hX)
    (hP := hP D T u u' hne hst) (hCoo := Formalism.L2.SG.Pf.MassDataPos.cooOf_pos T.X u u')
    (hκ := Formalism.L2.SG.WConst.kapN_pos) (hsd := hDN D T u u' Lsp ϖ) (hC := hC) (hTh := hTh) ..

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsSumCPf
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.SpectralTiesReal

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

theorem tprod_alpD_pos (D : D7) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word) :
    0 < ∏' p, alpD u u' p := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  set s := D.R.k - 2 * D.R.rS - 2 with hs
  have hs2 : 2 ≤ s := by omega
  set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hs2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum
  have hαb := Formalism.L2.SG.Pf.alpBound_holds D hk u u'
  have hal0 : ∀ p, 0 < alpD u u' p := fun p => lt_of_lt_of_le (Real.exp_pos _) (hαb p).1
  have hlogα : Summable fun p => Real.log (alpD u u' p) := by
    refine Summable.of_norm_bounded (g := fun p => 2 * a p) (haS.mul_left 2) (fun p => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := Real.log_le_log (Real.exp_pos _) (hαb p).1
    have h2 := Real.log_le_log (hal0 p) (hαb p).2
    rw [Real.log_exp] at h1 h2
    constructor <;> linarith
  rw [← Real.rexp_tsum_eq_tprod hal0 hlogα]
  exact Real.exp_pos _

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

namespace Formalism.L2.SG.Pf.SzHypFam


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem midVolumeChain_of_standingHypotheses {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT ep0 CV : ℝ} (hT : Ties D)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCL : 1 ≤ Cl * large₂.sc.L) (he : 0 ≤ ep0) (hCV : 0 ≤ CV) :
    LocalBesselAndTopKernel.MidVolumeChain D large₂ ep0 CV := by
  intro τ
  rw [Formalism.L2.SG.Pf.SzHypFD.vv_eq_vand hT hH hCL τ]
  have h0 : 0 ≤ vand (lamSH D.R (D.hc τ)) := Formalism.MainNotions.BridgeLemma.szh_vand_nonneg _ (Formalism.MainNotions.BridgeLemma.szh_anti hH τ)
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hx : 0 ≤ CV * D.R.k * D.R.m * large₂.sc.L := by positivity
  have h1 : 1 ≤ Real.exp (CV * D.R.k * D.R.m * large₂.sc.L) := Real.one_le_exp hx
  constructor
  · nlinarith
  · nlinarith


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem familyTopBound_of_one_le_sCl {eps : ℝ} (Fm : FamP eps) (h1 : 1 ≤ sCl Fm) (C0 Cg cb Cu cT CT ep0 CV : ℝ) (he : 0 ≤ ep0)
    (hCV : 0 ≤ CV) : LocalBesselAndTopKernel.FamilyTopBound Fm C0 Cg cb Cu cT CT ep0 CV := by
  refine ⟨0, fun x _ i hh => ?_⟩
  have hL := Formalism.MainNotions.BridgeLemma.one_le_L (Fm.L x i)
  exact midVolumeChain_of_standingHypotheses (Fm.ties x i) hh.2.1 (by nlinarith) he hCV


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem localSplitExponents_of_forty_le_sCl {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) (C0 Cg cb Cu cT CT : ℝ) :
    LocalBesselAndTopKernel.LocalSplitExponents Fm C0 Cg cb Cu cT CT 1 :=
  Formalism.MainNotions.BridgeLemma.family_critical_level_lower_bound Fm (ep0 := 1 / 3) (CV := 0) h40 (by norm_num) le_rfl
    (familyTopBound_of_one_le_sCl Fm (by linarith) C0 Cg cb Cu cT CT (1 / 3) 0 (by norm_num) le_rfl)


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem secondSizeStatement_of_famP {eps : ℝ} (Fm : FamP eps) : LocalBesselAndTopKernel.SecondSizeStatement Fm := fun x i =>
  Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified Formalism.HermitianLattices.Ext.L3.siegelMassRatio (Fm.D x i)


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem familyBesselBoundFirstPart_of_ranksF {eps : ℝ} (Fm : FamP eps) {C0 Cg cb Cu cT CT : ℝ} (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) :
    LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT :=
  Formalism.MainNotions.BridgeLemma.level_formula_family Fm C0 Cg cb Cu cT CT (secondSizeStatement_of_famP Fm)
    (Formalism.MainNotions.BridgeLemma.mass_two_bound_family_holds Fm) hR


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem tFrame_of_ranks {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ}
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) : PX.TFrame Fm Cg cb Cu cT CT C0 :=
  Formalism.MainNotions.BridgeLemma.level_frame_of_sizes Fm Cg cb Cu cT CT C0 1 (by linarith) (familyBesselBoundFirstPart_of_ranksF Fm hR)
    (localSplitExponents_of_forty_le_sCl Fm h40 C0 Cg cb Cu cT CT)

def aSz (C0 : ℝ) : List ℝ → ℝ := fun _ => Real.exp (3 / 4) * (C0 * Real.exp 1)

theorem one_le_aSz {C0 : ℝ} (h1 : 1 ≤ C0) (l : List ℝ) : 1 ≤ aSz C0 l := by
  unfold aSz
  have a := Real.one_le_exp (show (0 : ℝ) ≤ 3 / 4 by norm_num)
  have b := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
  have c : 1 ≤ C0 * Real.exp 1 := by nlinarith
  nlinarith


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem sizes3b_of_ranks {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ} (h1 : 1 ≤ C0)
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) :
    OwnEv Fm fun C' Cl x i => LocalBesselAndTopKernel.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT →
      Formalism.MainNotions.Sizes3b (Fm.D x i) (aSz C0 Fm.cOut) := by
  have hb : LocalBesselAndTopKernel.TheoremThreePassage Fm C0 Cg cb Cu cT CT (Real.exp (3 / 4)) := Formalism.MainNotions.BridgeLemma.family_critical_level_ratio Fm h40 le_rfl
  have hc : LocalBesselAndTopKernel.FamilyLowestKType Fm C0 Cg cb Cu cT CT (Real.exp (3 / 4) * (C0 * Real.exp 1)) :=
    Formalism.MainNotions.BridgeLemma.family_level_ratio_bound Fm C0 Cg cb Cu cT CT _ _ le_rfl (familyBesselBoundFirstPart_of_ranksF Fm hR) hb
  have hA := one_le_aSz h1 Fm.cOut
  have hC1 : Real.exp (3 / 4) ≤ aSz C0 Fm.cOut := by
    unfold aSz
    have b := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
    have c : 1 ≤ C0 * Real.exp 1 := by nlinarith
    have := Real.exp_pos (3 / 4)
    nlinarith
  exact Formalism.MainNotions.sizes3bF Fm C0 Cg cb Cu cT CT _ _ _ (Real.exp_pos _).le hC1 le_rfl hb hc


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem szRowsAt_of_ties {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hD : StandingNumericalData D C0)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hCL : 1 ≤ Cl * large₂.sc.L) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) :
    Formalism.L2.SG.Pf.SzHypOf.SzRowsAt D :=
  ⟨Formalism.MainNotions.BridgeLemma.mass_ratio_of_siegel_cm_unramified Formalism.HermitianLattices.Ext.L3.siegelMassRatio D, hR, Formalism.MainNotions.BridgeLemma.sza_spl_of_data hD,
    fun τ => Formalism.L2.SG.Pf.SzHypFD.fdl_of_ties hT hH hCL τ⟩

section Rows

open Formalism.L2.SG.ThmSOwn

variable (C0 : ℝ)

def RanksRow (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => PX.RanksF Fm C0 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem hTF_of_ranks {𝒞 : FamClass} (hRk : RanksRow C0 𝒞) :
    Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu C0 :=
  closed_with hRk (fun _ => 0) (fun _ => 40) fun Fm _ _ hR _ _ h2 => tFrame_of_ranks Fm h2 hR


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem hA_of_ranks {𝒞 : FamClass} (h1 : 1 ≤ C0) (hRk : RanksRow C0 𝒞) :
    Closed 𝒞 fun Fm _ => 1 ≤ aSz C0 Fm.cOut ∧ OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
        Formalism.MainNotions.Sizes3b (Fm.D x i) (aSz C0 Fm.cOut) :=
  closed_with hRk (fun _ => 0) (fun _ => 40) fun Fm _ _ hR _ _ h2 =>
    ⟨one_le_aSz h1 _, sizes3b_of_ranks Fm h2 h1 hR⟩


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem hRw_of_ranks {𝒞 : FamClass} (hRk : RanksRow C0 𝒞) :
    Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
      AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
        Formalism.L2.SG.Pf.SzHypOf.SzRowsAt (Fm.D x i) :=
  closed_with hRk (fun _ => 0) (fun _ => 1) fun Fm _ _ hR _ _ h2 => by
    obtain ⟨x0, H⟩ := hR
    refine ⟨x0, fun x hx i hh => ?_⟩
    have hL := Formalism.MainNotions.BridgeLemma.one_le_L (Fm.L x i)
    have h2' : 1 ≤ sCl Fm := h2
    exact szRowsAt_of_ties (Fm.ties x i) hh.1 hh.2.1 (by nlinarith) (H x hx i hh)

end Rows

end Formalism.L2.SG.Pf.SzHypFam
end
end

