module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.IsProperOfProj
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BcOnFalse
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.Bundle0002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.QbLePf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.LevelSystemGood

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {m : ℕ}

theorem qb_le {L : Lev R m} (hL : L.Good) (M : Model l K) (s : ℕ) :
    ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T) := qb_le_pf hL M s

theorem unit_B {L : Lev R m} (hL : L.Good) : IsUnit ((l : L.B)) := unit_B_pf hL

theorem cg_lift [FiniteDimensional ℚ_[l] K] {L : Lev R m} (hL : L.Good) (M : Model l K) (hM : M.Sm) (s : ℕ) (hs : m ≤ s)
    (j : ℕ) : ∃ e : ℕ, LiftP (QA L M s) (l : L.A) s j e := cg_lift_pf hL M hM s hs j

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) (s : ℕ)

theorem chain_good [FiniteDimensional ℚ_[l] K] (hM : M.Sm) (U : Cov M.q) (hU : ∀ α, U.d α + m ≤ s) (hs : m ≤ s)
    (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)
    (hr : ∀ n j x, trM (QA L M s) none (l : L.A) n j (rH (n + 1) j x) = rH n j ((M.HS false j).r n x)) :
    (chainOf hL M s (qb_le hL M s) rH).Good := level_system_good hL M s hM U hU hs rH hr

end

end CrystallineSemistableComparison.Pb.Kap
