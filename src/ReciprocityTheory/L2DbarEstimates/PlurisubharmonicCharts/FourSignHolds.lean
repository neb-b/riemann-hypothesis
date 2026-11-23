module

public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.HyPhi
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0008
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeLoc
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0011
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0004
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourIndep
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0003

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Y

section
variable (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La]

end

theorem four_sign_holds (f : ℕ) : FOURSignStatement f :=
  four_sign f (four_indep f) (four_bound f)

end ReciprocityTheory.L2DbarEstimates.Y
