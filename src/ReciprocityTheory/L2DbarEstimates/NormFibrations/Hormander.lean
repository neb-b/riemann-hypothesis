module

public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.Imports
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
public import ReciprocityTheory.L2DbarEstimates.Mollifiers.Imports
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Imports
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0005
public import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsAlt
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.Closed
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Imports
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Imports

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory

theorem regMAll (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : F.RegMStatement n M :=
  F.regM n M C.reg (F.extend n M)

theorem hormander (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : HStatement n M :=
  F.hStatement_of n M (E.ap n M) (E.tStarIbp n M) (chain n M) C.reg
    (B.moll_graph (V n) volume ℝ) (B.moll_smooth (V n) volume) (B.moll_support (V n) volume)
    (B.kernel_std (V n) volume)

theorem skoda (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : SStatement n M :=
  H.skoda n M (fun p => hormander n (M × Fin p))
    (fun p => F.needBergmanClosed n (M × Fin p) (regMAll n (M × Fin p)))

theorem tw (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : TWStatement n M :=
  I.tw n M (hormander n M) (F.holoClosedNeed n M (regMAll n M))

theorem ma (n : ℕ) : MAStatement n :=
  I.ma n (I.maCof n)

end ReciprocityTheory.L2DbarEstimates
