module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompGood
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.Bundle0001

@[expose] public section

noncomputable section

namespace CrystallineSemistableComparison

theorem comp : ModelComponents := fun l _ K _ ↦ ⟨compSm l K, compGood l K⟩

theorem geo : GeometricGenericComponents := geoMain

end CrystallineSemistableComparison
