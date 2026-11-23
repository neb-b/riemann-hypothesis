module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Half1
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle0008
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.SumCoord
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.TfBaseField
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle0009
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle0007
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle0005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompat
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfEtSide

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.HT

theorem half2 (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (hL : LvEx l K)
    (hF : KFin) : ∃ γ, Half2 (K := K) (tFil l) γ :=
  half2Of l K (tFil l) (crisSurj l) hL rhoEx (coEx l K) homRho homMu (mulRho l K) (firstChern_hodgeTate_rho l K) kForm hF

theorem ht_of (hL : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], LvEx l K)
    (hF : KFin) (hC : DlogClassExistsUnique) (hT : KTop) (hE : EtSideS) : HodgeTateMapExists := fun l _ K _ =>
  (etP l K).elim fun _ he => (half2 l K (hL l K) hF).elim fun _ h2 =>
    (pre_of (half1 (tFil l) he) h2 hF hC).elim fun P => ⟨P, inj_of P (hE l K) hT kForm he.one_ex⟩

end CrystallineSemistableComparison.HT
