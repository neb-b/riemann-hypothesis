module

public import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
public import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictCore
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcWeil
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselExpansion
section
noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.RotatedPoints Formalism.MainNotions.S.Pv.Frames

section Loc

variable (D : D7)

variable {D}

theorem frame_bounds {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} {v : D.what₂.Tau} {L : LocBessel D.R.k D.R.rS}
    {f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)} {μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hCg : 2 ≤ Cg) (hok : PlaceOKR D Ch Cg T T' b dist v L f μsec) :
    2 ≤ b ∧ 1 ≤ b ^ (3 + Ch) ∧ D.host.rdE ≤ b ^ (3 + Ch) := by
  obtain ⟨⟨hk, -, -, -, -, hStd, -, -⟩, -⟩ := hok
  have hb2 : 2 ≤ b := by
    have h1 := b_ge_of_StdHyp0 hk hStd.to0
    have h2 : (1 : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1))
    nlinarith
  have hka : 0 < kaRe D := hStd.2.2.2.1
  have hk1 : kaRe D ≤ b ^ Ch := hStd.2.2.2.2.1
  have hk2 : (kaRe D)⁻¹ ≤ b ^ Ch := hStd.2.2.2.2.2.1
  have hbC : 1 ≤ b ^ Ch := by
    rcases le_total 1 (kaRe D) with h | h
    · exact h.trans hk1
    · exact ((one_le_inv₀ hka).2 h).trans hk2
  have hb0 : 0 < b := by linarith
  have hb3 : 1 ≤ b ^ (3 + Ch) := by
    rw [Real.rpow_add hb0]
    have : 1 ≤ b ^ (3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    nlinarith
  exact ⟨hb2, hb3, Formalism.MainNotions.TheoremBConstants.rdE_le D b Ch hb2 hka hk2⟩

theorem ch_nonneg {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} {v : D.what₂.Tau} {L : LocBessel D.R.k D.R.rS}
    {f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)} {μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hCg : 2 ≤ Cg) (hok : PlaceOKR D Ch Cg T T' b dist v L f μsec) : 0 ≤ Ch := by
  have hb2 := (frame_bounds hCg hok).1
  obtain ⟨⟨-, -, -, -, -, hStd, -, -⟩, -⟩ := hok
  have hka : 0 < kaRe D := hStd.2.2.2.1
  have hk1 : kaRe D ≤ b ^ Ch := hStd.2.2.2.2.1
  have hk2 : (kaRe D)⁻¹ ≤ b ^ Ch := hStd.2.2.2.2.2.1
  by_contra hc
  push_neg at hc
  have hlt : b ^ Ch < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hc
  rcases le_total 1 (kaRe D) with h | h
  · linarith
  · have := (one_le_inv₀ hka).2 h
    linarith

end Loc

end Formalism.L2.SG.Pf.BesselExpansion
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RConvFExistsPf
section
noncomputable section

namespace Formalism.L2.SG.Pf.RConvFExistsPf

open MeasureTheory
open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates

theorem convergent_reduction_exists : Formalism.L2.SG.Pf.RowDictPf.RConvFExists := by
  intro I μf _ _ hright hsc hborel fund hfund R hR f hf
  haveI := hsc
  haveI := hborel
  haveI : μf.IsMulRightInvariant := hright
  haveI : SigmaFinite (I.muA μf) := rr_muA_sigmaFinite I μf
  haveI : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
  haveI : (I.muA μf).IsMulRightInvariant := rr_muA_right I μf
  have hfd := rr_FD_of I μf fund hfund
  have hreg := rr_IsReg_of I μf fund R hR

  have hemb : Measurable (fun g : I.Gf => ((1, g) : I.GA)) := by fun_prop
  obtain ⟨T, hT⟩ := wk_exists (μ := μf) (U := fun g => R (1, g))
    (fun g z => (rr_norm hfd hreg (1, g) z).le)
    (fun x y => ((rr_weak_meas hfd hreg x y).comp_measurable hemb).aestronglyMeasurable) hf
  exact ⟨T, hf, hT⟩

end Formalism.L2.SG.Pf.RConvFExistsPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RescaleCore
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.RescaleCore

def GramStdND : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ)
    (P : Frame E n r) (T : F), (∀ x, σ (σ x) = x) → IsHermND σ J → P.IsStd σ J T → (gramE σ J (tupH P)).det ≠ 0

end Formalism.L2.SG.Pf.RescaleCore
end
end

