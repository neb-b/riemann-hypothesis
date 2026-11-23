module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.XLeSpanEXLam
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NeatTies
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0055
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0035
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0039

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXHolds
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FinXP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_Gflag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} (n m : ℕ)
    (F : FlagG S r (n : E)) (F' : FlagG S r (m : E)) : star (Gflag F F') = Gflag F F' := by
  unfold Gflag
  simp only [star_sub, star_mul', star_star, star_natCast]
  ring

theorem greal_holds {D : D7} {X : HidaSetting D} (Y : Full X) : ∀ u u' (t : RT Y u u'), t.G ∈ D.host.F := by
  intro u u' t
  rw [← Formalism.BasicNotions.Examples₂.conj_eq_self_iff D.host, ← Formalism.BasicNotions.Examples₂.star_eq_conj D.host]
  exact star_Gflag _ _ _ _


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem phLoc_int_of_gap {D : D7} (X : HidaSetting D) (hg : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (v : InfinitePlace X.B.I.F) (d : ℝ) :
    Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) d) (Formalism.REAL.muG (X.B.I.ε v)) := by
  have h := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X
    (Formalism.L2.SG.Pf.WuDec.coefWeighted_of_gap X Formalism.L2.SG.Closed.CoefWeightedLoc_holds hg) v
  have hs : Integrable (fun g => star (Formalism.L2.SG.WuDecayPf.coefV X v g)) (Formalism.REAL.muG (X.B.I.ε v)) :=
    h.mono (continuous_star.comp_aestronglyMeasurable h.1) (ae_of_all _ fun g => le_of_eq (norm_star _))
  exact hs.const_mul (d : ℂ)


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem finX_holds (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hRF : Formalism.L2.SG.RowsDef.RowsFinDim) (hFL : Formalism.L2.SG.Pf.FinLeviC)
    (hK : IotaKer) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC := by
  intro D T hg
  obtain ⟨hWD, hph⟩ := hWu D hg T.X
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties T.X
  have hfold : ∀ u, Formalism.L2.SG.WuDecay.FoldOK T.X u T.Y.hK := fun u =>
    Formalism.L2.SG.Closed.FoldOKC_holds hFL D T.X T.Y u hK2 hWD
  exact finX_of_neat T.Y (fun u => Formalism.L2.SG.Pf.neatKu_full D T.X T.Y u)
    (fun u => Formalism.L2.SG.Closed.InHHC_holds D T.X T.Y u hph (hfold u))
    (Formalism.L2.SG.Pf.RowDictPf.finiteDimensional_HHX_of_hypotheses T.X hRF Formalism.L2.SG.Pf.RowDictPf.schur_orthogonality_discrete_series
      (fun v => phLoc_int_of_gap T.X hg v _))
    (fun u u' t => fibFin_holds D T.X T.Y u u' t)
    (fun u u' s₁ s₂ s₁' s₂' h1 h2 h3 h4 => pairIndep_of hK D T.X T.Y u u' s₁ s₂ s₁' s₂' h1 h2 h3 h4)
    (greal_holds T.Y) Formalism.L2.SG.Closed.VolPosC_holds

end Formalism.L2.SG.Pf.FinXP

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.LoopBCovN

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def eN (D : D7) : ℝ := (D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) / 2

def CovNFormula : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), 0 < θ →
    LoopTerm.covN (Y := Y) C u = (θ * (2 * D.host.v) ^ eN D) ^ Fintype.card D.what₂.Tau

theorem rdE_ge_one (D : D7) : 1 ≤ 2 * D.host.v := by
  unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
  have hd : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := by
    have h0 : NumberField.discr D.host.E ≠ 0 := NumberField.discr_ne_zero D.host.E
    have h1 : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h0
    exact_mod_cast h1
  have h2 : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| ^ (1 / (Module.finrank ℚ D.host.E : ℝ)) :=
    Real.one_le_rpow hd (by positivity)
  linarith

theorem covWinN_of (hF : CovNFormula) {D : D7} {X : HidaSetting D} {Y : Full X} (C : Choice X 1) (large₂ : SizeData₂ D) {C1 : ℝ}
    (hC1 : 0 ≤ C1) (hup : eN D * Real.log (2 * D.host.v) ≤ C1 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b)
    (u u' : D.what₂.Word) : LoopTerm.CovWinN (Y := Y) C large₂ C1 u u' := by
  have hbpos : 0 < large₂.sc.b := by
    unfold Scale.b
    exact Real.exp_pos _
  have hv := rdE_ge_one D
  have hv0 : 0 < 2 * D.host.v := by linarith
  have heN : 0 ≤ eN D := by
    unfold eN
    positivity
  have hy1 : 1 ≤ (2 * D.host.v) ^ eN D := Real.one_le_rpow hv heN
  have hlog0 : 0 ≤ eN D * Real.log (2 * D.host.v) := mul_nonneg heN (Real.log_nonneg hv)
  have hyexp : (2 * D.host.v) ^ eN D = Real.exp (Real.log (2 * D.host.v) * eN D) :=
    Real.rpow_def_of_pos hv0 _
  have hcov : ∀ w, LoopTerm.covN (Y := Y) C w = ((2 * D.host.v) ^ eN D) ^ Fintype.card D.what₂.Tau := by
    intro w
    rw [hF D X Y 1 C w one_pos, one_mul]
  have hx : (LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u') ^ (1 / (2 * (Fintype.card D.what₂.Tau : ℝ))) = 1 ∨
      (LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u') ^ (1 / (2 * (Fintype.card D.what₂.Tau : ℝ))) =
        (2 * D.host.v) ^ eN D := by
    rw [hcov u, hcov u', ← pow_add, ← two_mul]
    rcases Nat.eq_zero_or_pos (Fintype.card D.what₂.Tau) with h0 | hpos
    · left
      simp [h0]
    · right
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      have hN : (0 : ℝ) < Fintype.card D.what₂.Tau := by exact_mod_cast hpos
      have h2 : ((2 * Fintype.card D.what₂.Tau : ℕ) : ℝ) * (1 / (2 * (Fintype.card D.what₂.Tau : ℝ))) = 1 := by
        push_cast
        field_simp
      rw [h2, Real.rpow_one]
  have hxb : ∀ z : ℝ, (z = 1 ∨ z = (2 * D.host.v) ^ eN D) → 1 ≤ z ∧ z ≤ (2 * D.host.v) ^ eN D := by
    rintro z (rfl | rfl) <;> exact ⟨by linarith, by linarith⟩
  obtain ⟨hx1, hx2⟩ := hxb _ hx
  have hup' : Real.log (2 * D.host.v) * eN D ≤ Real.log large₂.sc.b * (C1 * (D.R.m : ℝ) ^ 2) := by linarith
  unfold LoopTerm.CovWinN normWin
  refine ⟨le_trans ?_ hx1, le_trans hx2 ?_⟩
  · rw [Real.rpow_def_of_pos hbpos]
    have hneg : Real.log large₂.sc.b * -(C1 * (D.R.m : ℝ) ^ 2) ≤ 0 := by nlinarith
    exact Real.exp_le_one_iff.mpr hneg
  · rw [hyexp, Real.rpow_def_of_pos hbpos]
    exact Real.exp_le_exp.mpr hup'

theorem log_rd_le {D : D7} (large₂ : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt large₂) :
    Real.log (2 * D.host.v) ≤ Real.log large₂.sc.b / 72 := by
  obtain ⟨-, -, -, -, hT, hC, hQ, -⟩ := hS
  obtain ⟨-, -, -, -, -, -, hr1, hr2⟩ := hQ
  have h2v : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  rw [h2v]
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have ht : (1 : ℝ) ≤ D.R.t := hT.1
  have hqd : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    have h1 : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hcond : D.host.rdE ≤ Formalism.MainNotions.szCond large₂ := by
    unfold Formalism.MainNotions.szCond
    calc D.host.rdE ≤ (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) := hr2
      _ ≤ (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) := by gcongr
      _ ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by
        have h0 : (0 : ℝ) ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by positivity
        nlinarith
  have hc1 : (1 : ℝ) ≤ Formalism.MainNotions.szCond large₂ := le_trans hr1 hcond
  have hb0 : 0 < large₂.sc.b := lt_of_lt_of_le (by norm_num) (Formalism.MainNotions.S.two_le_scb large₂)
  have h36 : Formalism.MainNotions.szCond large₂ ^ 36 ≤ Real.sqrt large₂.sc.b := by
    have : Formalism.MainNotions.szCond large₂ ^ 36 ≤ Formalism.MainNotions.szCond large₂ ^ 36 * (D.R.t : ℝ) ^ 150 := by
      have : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht
      nlinarith [pow_pos (lt_of_lt_of_le one_pos hc1) 36]
    exact this.trans hC
  have hl := Real.log_le_log (pow_pos (lt_of_lt_of_le one_pos hc1) 36) h36
  rw [Real.log_pow, Real.log_sqrt hb0.le] at hl
  have hl2 := Real.log_le_log (lt_of_lt_of_le one_pos hr1) hcond
  push_cast at hl
  linarith

theorem eN_le (D : D7) : eN D ≤ (D.R.m : ℝ) ^ 2 / 2 := by
  unfold eN
  have h : (D.R.rS : ℝ) ≤ (D.R.m : ℝ) / 2 := by
    have : 2 * D.R.rS ≤ D.R.m := by unfold Formalism.BasicNotions.Ranks.rS; omega
    have : (2 * D.R.rS : ℝ) ≤ D.R.m := by exact_mod_cast this
    linarith
  have h0 : (0 : ℝ) ≤ D.R.rS := by positivity
  have hm : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
  nlinarith

theorem covWinN_sizes (hF : CovNFormula) {D : D7} {X : HidaSetting D} {Y : Full X} (C : Choice X 1) (large₂ : SizeData₂ D)
    (hS : Formalism.MainNotions.SizesAt large₂) {C1 : ℝ} (hC1 : 1 / 144 ≤ C1) (u u' : D.what₂.Word) :
    LoopTerm.CovWinN (Y := Y) C large₂ C1 u u' := by
  have hv := rdE_ge_one D
  have hl0 : 0 ≤ Real.log (2 * D.host.v) := Real.log_nonneg hv
  have hl := log_rd_le large₂ hS
  have he := eN_le D
  have hb : 0 ≤ Real.log large₂.sc.b := by linarith
  have hm : 0 ≤ (D.R.m : ℝ) ^ 2 := by positivity
  refine covWinN_of hF C large₂ (by linarith) ?_ u u'
  calc eN D * Real.log (2 * D.host.v) ≤ ((D.R.m : ℝ) ^ 2 / 2) * (Real.log large₂.sc.b / 72) :=
        mul_le_mul he hl hl0 (by positivity)
    _ = 1 / 144 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := by ring
    _ ≤ C1 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := by
        apply mul_le_mul_of_nonneg_right _ hb
        exact mul_le_mul_of_nonneg_right hC1 hm

theorem covN_pos (hF : CovNFormula) {D : D7} {X : HidaSetting D} {Y : Full X} {θ : ℝ} (hθ : 0 < θ) (C : Choice X θ)
    (u u' : D.what₂.Word) : 0 < LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u' := by
  rw [hF D X Y θ C u hθ, hF D X Y θ C u' hθ]
  have h1 := rdE_ge_one D
  have h2 : 0 < θ * (2 * D.host.v) ^ eN D := mul_pos hθ (Real.rpow_pos_of_pos (by linarith) _)
  exact mul_pos (pow_pos h2 _) (pow_pos h2 _)

end Formalism.L2.SG.Pf.LoopBCovN
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBTheta
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.LoopBTheta

theorem normWin_one {D : D7} (large₂ : SizeData₂ D) {C1 : ℝ} (hC1 : 0 ≤ C1) : normWin D large₂ C1 1 := by
  have hL : 0 ≤ large₂.sc.L := by
    show 0 ≤ large₂.sc.x ^ large₂.sc.eps
    exact le_of_lt (Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _)
  have hb : (1 : ℝ) ≤ large₂.sc.b := by
    show (1 : ℝ) ≤ Real.exp large₂.sc.L
    exact Real.one_le_exp hL
  have hc : 0 ≤ C1 * (D.R.m : ℝ) ^ 2 := mul_nonneg hC1 (sq_nonneg _)
  refine ⟨?_, ?_⟩
  · exact Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr hc)
  · exact Real.one_le_rpow hb hc

end Formalism.L2.SG.Pf.LoopBTheta
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.OOCore
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.BDatR Formalism.L2.SG.ThmBUseR
  Formalism.L2.SG.Pf.JointAmplitudePoints Formalism.L2.SG.Pf.ThmBChain
open scoped ENNReal

namespace Formalism.L2.SG.Pf.OOCore

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Core

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)

def OOP (w : Point D.host.E (D.R.rS + 1)) : X.Vpi u' →L[ℂ] X.Vpi u :=
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' w)

theorem joint_amplitude_eq_normSq (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) :
    J2of Y u u' ν (toPts w) =
      Complex.normSq ((Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) *
        Formalism.MainNotions.S.hsNormSq (OOP u u' ν w) := by
  have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = toPts w ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g :=
    ⟨w, rfl, hw⟩
  unfold J2of
  rw [dite_eq_left hex]
  have hc : hex.choose = w := toPts_injective hex.choose_spec.1
  rw [hc, Formalism.L2.SG.PackageTie.norm_hsEmb_sq]
  unfold Jw OOP
  rw [Formalism.L2.SG.Pf.LTL.hsNormSq_smul]

variable {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

end Core

end Formalism.L2.SG.Pf.OOCore
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PvalFormExistsRf
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X}

theorem pairAmpConst_holds (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y)
    (hOI : ∀ w w', OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w')) : PairAmpConst Y :=
  pairAmpConst_of (fun w => Formalism.L2.SG.Closed.NeatKu_holds X w Y.hK) hRF Formalism.L2.SG.Pf.iotaRepC_holds
    Formalism.L2.SG.Pf.ampRepNC_holds (fun _ X => chi_n_bilinear X) hOI

variable {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))

theorem pvalForm_exists_rf (hRF : Formalism.L2.SG.Pf.FibreCounting.RowFree Y)
    (hOI : ∀ w w', OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w')) (hN : FibreCountEq hF) :
    ∃ A : AmpDat X, PvalForm W hI A :=
  pvalForm_exists' W hI (AmpCov_holds Y) (pairAmpConst_holds hRF hOI) hN

theorem rowFree_holds : Formalism.L2.SG.Pf.FibreCounting.RowFree Y :=
  Formalism.L2.SG.Pf.Act.rowFree_of (fun w => Formalism.L2.SG.Closed.NeatKu_holds X w Y.hK) Formalism.L2.SG.Pf.iotaRepC_holds

theorem pvalForm_exists_oi (hOI : ∀ w w', OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w'))
    (hN : FibreCountEq hF) : ∃ A : AmpDat X, PvalForm W hI A :=
  pvalForm_exists_rf W hI rowFree_holds hOI hN

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

