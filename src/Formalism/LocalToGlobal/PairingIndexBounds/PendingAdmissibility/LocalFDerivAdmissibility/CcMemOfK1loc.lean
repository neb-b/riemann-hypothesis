module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

@[expose] public section

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem cc_logF : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logF, PowerSeries.coeff_mk]

theorem cc_logX {ι : Type} (K1 : Type) [Field K1] [Algebra (K0 p) K1] (i : ι) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) = 0 := by
  refine PowerSeries.constantCoeff_subst_eq_zero (by simp) _ ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_logF, map_zero]

theorem hasSubst_logX {ι : Type} [Finite ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] :
    MvPowerSeries.HasSubst (fun i : ι => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_logX K1)

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
