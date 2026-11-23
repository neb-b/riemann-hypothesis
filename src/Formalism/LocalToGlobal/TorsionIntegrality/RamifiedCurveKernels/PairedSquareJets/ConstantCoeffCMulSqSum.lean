module

public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementS
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.InverseEndoIntegralHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversalLaw

@[expose] public section

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace PairedSquareConstantCoefficients

section Alg

variable {K : Type} [Field K]

theorem inBlock_mul {ι B : Type} (k : B) (f g : MvPowerSeries ι K) :
    inBlock k (f * g) = inBlock k f * inBlock k g := by
  simp only [HurwitzJetIntegrality.inBlock_eq_rename, map_mul]

theorem tensor_four_mul {ι : Type} (f g : MvPowerSeries ι K) : tens4 (f * g) = tens4 f * tens4 g := by
  unfold tens4
  simp only [inBlock_mul, Finset.prod_mul_distrib]

variable [CharZero K]

theorem inBlock_mvExp {ι B : Type} [Finite ι] (k : B) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : inBlock k (mvExp f) = mvExp (inBlock k f) := by
  unfold inBlock
  exact mvSubst_mvExp hf
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => MvPowerSeries.constantCoeff_X _)

end Alg

end PairedSquareConstantCoefficients

open PairedSquareConstantCoefficients

end Formalism.L2.Th1.G
