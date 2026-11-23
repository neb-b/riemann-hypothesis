module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.ReductionChangeLevel
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.BMapIncl
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

namespace LevelChangeComparison

end LevelChangeComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (S : LevSys (per l K)) (hS : S.Good) (m : ℕ) (M : Model l K)

def nmLevA : NMor (S.L (m + 1)).γ M.p (κA (OK l K) (S.L (m + 1)).I) (S.L m).γ M.p (κA (OK l K) (S.L m).I) (S.dA m) :=
  nmK (S.L (m + 1)).γ (S.L m).γ M.p M.p (S.dA m) (hS.ddp m) (hS.dO m) (𝟙 M.X) (Category.id_comp _)

def nmLevB : NMor (S.L (m + 1)).γB M.q (κA K (S.L (m + 1)).IB) (S.L m).γB M.q (κA K (S.L m).IB) (S.dB m) :=
  nmK (S.L (m + 1)).γB (S.L m).γB M.q M.q (S.dB m) (hS.ddpB m) (hS.dK m) (𝟙 M.gen) (Category.id_comp _)

namespace LevelChangeComparison

end LevelChangeComparison

end

theorem bMap_incl {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) {s s' : ℕ} (h : s ≤ s')
    (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
    (hQ' : ∀ T, QB L M s' T → QA L M s' (((nmB M hL).mor 0).obj T)) (j : ℕ) (z : HO (QA L M s') j) :
    (incl (ts_le L.γB M.q 1 h {⊤})).o.pull j (bMap M s' hL hQ' j z) =
      bMap M s hL hQ j ((incl (ts_le L.γ M.p l h {⊤})).o.pull j z) := by
  have e₁ := CrystallineSemistableComparison.pull_pull L.ι (smB M s' hL hQ').o (incl (ts_le L.γB M.q 1 h {⊤})).o j z
  have e₂ := CrystallineSemistableComparison.pull_pull L.ι (incl (ts_le L.γ M.p l h {⊤})).o (smB M s hL hQ).o j z
  exact e₁.trans (Eq.trans rfl e₂.symm)

end CrystallineSemistableComparison.Pb.Kap
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomGalGoodRHof
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def galS (M : Model l K) (g : K.fixingSubgroup) (n j : ℕ) : M.Hc false n j →ₛₗ[(per l K).σA g] M.Hc false n j :=
  B.galHc (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K g) (galOC_okToOC _) false n j

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (g : K.fixingSubgroup) (M : Model l K)

def nmGA : NMor L.γ M.p (κA (OK l K) L.I) L.γ M.p (κA (OK l K) L.I) (L.σA g) :=
  nmK L.γ L.γ M.p M.p (L.σA g) (hL.σ_dp g) (hL.σ_O g) (𝟙 _) (Category.id_comp _)

def nmGB : NMor L.γB M.q (κA K L.IB) L.γB M.q (κA K L.IB) (L.σB g) :=
  nmK L.γB L.γB M.q M.q (L.σB g) (hL.σB_dp g) (hL.σB_K g) (𝟙 _) (Category.id_comp _)

variable (s : ℕ) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

def homGal : Hom (chainOf hL M s hQ rH) (chainOf hL M s hQ rH) where
  sΛ := (per l K).σA g
  sA := L.σA g
  sB := L.σB g
  fS n j := galS M g n j
  fZn n j := nmHM (nmGA hL g M) l s none n j
  fZ j := nmHO (nmGA hL g M) l s j
  fW j := nmHO (nmGB hL g M) 1 s j
  fV _ := LinearMap.id

def GalRed : Prop :=
  ∀ n j (x : M.Hc false n j), nmHM (nmGA hL g M) l s none n j (rH n j x) = rH n j (galS M g n j x)

end

section
variable {m : ℕ} {L : Lev (per l K) m}
  (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
  (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))

end

end CrystallineSemistableComparison.Pb.Kap
end
end

