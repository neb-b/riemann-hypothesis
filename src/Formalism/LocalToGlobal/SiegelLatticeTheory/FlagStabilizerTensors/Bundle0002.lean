module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SettingExistsMeasured
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

set_option linter.dupNamespace false

namespace Formalism.L2.SG.SettingExistsMeasured

variable {D : D7}

def withMeas (X : HidaSetting D) (mg : Formalism.L2.SG.Measures.MeasG X.B.I.cm.sig X.B.I.J D.R.rS)
    (hg : mg.IsTextNorm)
    (mw : ∀ u, Formalism.L2.SG.Measures.MeasW X.B.I.cm.sig X.B.I.J
      (⟨fun a => crdOf X.B.I X.ιE X.bas (X.eX a), fun a => crdOf X.B.I X.ιE X.bas (X.fY a),
        crdOf X.B.I X.ιE X.bas (X.zu u)⟩ : Formalism.L2.SG.Sub.Frame X.B.I.E X.B.I.n D.R.rS))
    (hw : ∀ u, (mw u).IsTextNorm) : HidaSetting D :=
  { X with measG := mg, measG_norm := hg, measW := mw, measW_norm := hw }

variable (D)

end Formalism.L2.SG.SettingExistsMeasured
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmBUse
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.ThmBUse

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.FourierDecayAlt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Core

variable {D : D7} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
  {Cl Nu : Type} (N : PN.NGData τ D.host.E D.R.rS Cl Nu)

def IsRowPt (D : D7) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  IsBPt D T T' w ∧ ∀ v, 0 < Gpt (T : ℝ) (T' : ℝ) (ptLoc D v w)

def PtTie (T T' : ℕ) : Prop :=
  ∀ γ, PN.IsPt X N γ → ∃ w : Point D.host.E (D.R.rS + 1), RowsConc.toPts w = γ ∧ IsRowPt D T T' w

def WtTie (T T' A : ℕ) (Cw : ℝ) : Prop :=
  ∀ γ (w : Point D.host.E (D.R.rS + 1)), PN.IsPt X N γ → RowsConc.toPts w = γ → IsRowPt D T T' w →
    Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ * N.n γ * (N.NG γ * N.ND γ) ^ (A * (D.R.rS + 1) ^ 2) ≤
      Cw * (wPt D w * ptWeightG D (rhoReal D) T T' w.1 *
        normWt D T T' w ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2))

def NormTie {Ch Cg : ℝ} {T T' : ℕ} {b : ℝ} (Bd : BData D Ch Cg T T' b 0) (Cw Cj Cb TB : ℝ) : Prop :=
  ENNReal.ofReal (Cw * Cj) *
      (ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D Bd) ≤ ENNReal.ofReal TB

end Core

section Sum

variable {D : D7} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
  {Cl Nu : Type} (N : PN.NGData τ D.host.E D.R.rS Cl Nu)

end Sum

section Step

open scoped Classical
open Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData

theorem J2of_nonneg' {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (γ : PN.Pts D.host.E D.R.rS) : 0 ≤ J2of Y u u' ν γ := by
  unfold J2of
  split_ifs <;> positivity

end Step

section Wt

open scoped Classical
open Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc
  Formalism.L2.SG.NGData

def WtTieConc : Prop :=
  ∀ (D : D7) (T T' A : ℕ) (w : Point D.host.E (D.R.rS + 1)), IsRowPt D T T' w →
    Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight (toPts w) * nPt D.host.rdE D.R.k (T * T') (toPts w) *
              (NGPt D.host.rdE (T * T') (toPts w) * NDPt D.host.rdE (toPts w)) ^ (A * (D.R.rS + 1) ^ 2) ≤
      1 * (wPt D w * ptWeightG D (rhoReal D) T T' w.1 *
        normWt D T T' w ^ ((A : ℝ) * ((D.R.rS : ℝ) + 1) ^ 2))

theorem weight_normalized (h : WtTieConc) {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (A : ℕ) :
    WtTie (Y.tO u u') (NOf2 Y u u' νL νB ng) (Tu D u : ℕ) (Tu D u' : ℕ) A 1 := by
  intro γ w _ hw hb
  subst hw
  exact h D _ _ A w hb

end Wt

section FromStmtU

end FromStmtU

end Formalism.L2.SG.ThmBUse
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPinG
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.VolPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def VolPinGC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PrimeHyp D u (Tu D u') → ∀ (t : TT Y u u'),
    t.relevant → t.toTerm.generic → t.G ≠ 0 →
    ∀ w : Point D.host.E (D.R.rS + 1), t.toTerm.atPt w → ∀ μR : Measure X.B.I.Ginf, IsPinnedR t w μR →
    ∀ K : Set X.B.I.Ginf, MeasurableSet K →
      (∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ Formalism.L2.SG.TermOp.ROinf t ∧ s * r ∈ K) →
    ∀ (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D),
      Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U →
      (μR K).toReal = Formalism.L2.SG.PairVal.volIdx D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M t.toTerm w F' L

def VolumeOddGeneric : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ i, 3 ≤ D.host.g i) → PrimeHyp D u (Tu D u') →
    ∀ (t : TT Y u u'), t.relevant → t.toTerm.generic → t.G ≠ 0 →
    ∀ w : Point D.host.E (D.R.rS + 1), t.toTerm.atPt w → ∀ μR : Measure X.B.I.Ginf, IsPinnedR t w μR →
    ∀ K : Set X.B.I.Ginf, MeasurableSet K →
      (∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ Formalism.L2.SG.TermOp.ROinf t ∧ s * r ∈ K) →
    ∀ (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D),
      Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U →
      (μR K).toReal = Formalism.L2.SG.PairVal.volIdx D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M t.toTerm w F' L

end Formalism.L2.SG.VolPin
end
end

