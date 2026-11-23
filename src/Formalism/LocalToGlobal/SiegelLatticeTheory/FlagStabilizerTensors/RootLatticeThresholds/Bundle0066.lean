module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0062
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CutAtHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpOrbCoef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0058
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0064
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXPins
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT Formalism.L2.SG.RealObj
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups
open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ac_le (c Cl L : ℝ) (r k f : ℕ) (hCl : 1000 + |c| ≤ Cl) (hf : 2 ≤ f) (hL : 1 / 2 ≤ L) :
    max (c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) 0 ≤
      Cl * ((2 * r + k + 1 : ℕ) : ℝ) ^ 19 * (f : ℝ) ^ 5 * L / 2 := by
  have hr0 : (0 : ℝ) ≤ r := r.cast_nonneg
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hn : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [hn]
  have hn1 : (1 : ℝ) ≤ 2 * (r : ℝ) + k + 1 := by linarith
  have hrn : (r : ℝ) + 1 ≤ 2 * (r : ℝ) + k + 1 := by linarith
  have hCl0 : 0 ≤ Cl := by linarith [abs_nonneg c]
  have hf' : (2 : ℝ) ≤ f := by exact_mod_cast hf
  have hf5 : (32 : ℝ) ≤ (f : ℝ) ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hf' 5
    norm_num at this
    linarith
  have hP0 : 0 ≤ ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1) := by positivity
  have hn19 : 0 ≤ (2 * (r : ℝ) + k + 1) ^ 19 := by positivity
  have hP : ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1) ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 19 := by
    have h1 : ((r : ℝ) + 1) ^ 2 ≤ (2 * (r : ℝ) + k + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hrn 2
    have h2 : (r : ℝ) * (2 * (r : ℝ) + k + 1) + 1 ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 2 := by
      linarith [mul_nonneg hr0 hk0, mul_nonneg hr0 hr0, mul_nonneg hk0 hk0]
    have h3 : (2 * (r : ℝ) + k + 1) ^ 4 ≤ (2 * (r : ℝ) + k + 1) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
    calc ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1)
        ≤ (2 * (r : ℝ) + k + 1) ^ 2 * (2 * (2 * (r : ℝ) + k + 1) ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 * (2 * (r : ℝ) + k + 1) ^ 4 := by ring
      _ ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 19 := by linarith
  have hA : 0 ≤ Cl * (2 * (r : ℝ) + k + 1) ^ 19 := mul_nonneg hCl0 hn19
  have hRHS : 8 * (Cl * (2 * (r : ℝ) + k + 1) ^ 19) ≤
      Cl * (2 * (r : ℝ) + k + 1) ^ 19 * (f : ℝ) ^ 5 * L / 2 := by
    have hfl : (32 : ℝ) * (1 / 2) ≤ (f : ℝ) ^ 5 * L := mul_le_mul hf5 hL (by norm_num) (by positivity)
    have := mul_le_mul_of_nonneg_left hfl hA
    linarith
  apply max_le
  · have hcP : c * (((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1)) ≤
        |c| * (2 * (2 * (r : ℝ) + k + 1) ^ 19) :=
      (mul_le_mul_of_nonneg_right (le_abs_self c) hP0).trans
        (mul_le_mul_of_nonneg_left hP (abs_nonneg c))
    have hcl : |c| * (2 * (r : ℝ) + k + 1) ^ 19 ≤ Cl * (2 * (r : ℝ) + k + 1) ^ 19 :=
      mul_le_mul_of_nonneg_right (by linarith) hn19
    have e : c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1) =
        c * (((r : ℝ) + 1) ^ 2 * ((r : ℝ) * (2 * (r : ℝ) + k + 1) + 1)) := by ring
    rw [e]
    linarith
  · linarith

end Formalism.L2.SG.Pf.CarrierXAll
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GapClosed
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk

namespace Formalism.L2.SG.GapClosed

theorem gapEv_closed_of (𝒞 : FamClass) (hT : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) :
    Closed 𝒞 fun Fm _ => 𝒞 Fm → Formalism.L2.SG.LoopsTies.GapEv Fm := by
  obtain ⟨e, he, H⟩ := Formalism.L2.SG.ThmSOwn.gapRowT (𝒞 := 𝒞) (Formalism.L2.SG.ResidEvFree.residEv_closed_free 𝒞)
  refine ⟨e, he, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := H eps h1 h2
  exact ⟨K, fun Fm CH hc hL _ => hK Fm CH ⟨hc, hT Fm hc⟩ hL ⟨hc, hT Fm hc⟩⟩

end Formalism.L2.SG.GapClosed

end
end

