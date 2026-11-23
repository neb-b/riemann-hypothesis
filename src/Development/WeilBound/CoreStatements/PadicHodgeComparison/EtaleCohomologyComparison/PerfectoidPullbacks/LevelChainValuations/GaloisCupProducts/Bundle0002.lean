module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomLevGood
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (S : LevSys (per l K)) (hS : S.Good) (m : ℕ) (M : Model l K) (s : ℕ)
  (hQ₁ : ∀ T, QB (S.L (m + 1)) M s T → QA (S.L (m + 1)) M s (((nmB M (hS.lev (m + 1))).mor 0).obj T))
  (hQ₀ : ∀ T, QB (S.L m) M s T → QA (S.L m) M s (((nmB M (hS.lev m)).mor 0).obj T))
  (rH₁ : ∀ n j, M.Hc false n j →ₛₗ[(S.L (m + 1)).lam] HM (QA (S.L (m + 1)) M s) none ((l : (S.L (m + 1)).A) ^ n) j)
  (rH₀ : ∀ n j, M.Hc false n j →ₛₗ[(S.L m).lam] HM (QA (S.L m) M s) none ((l : (S.L m).A) ^ n) j)

def homLev : Hom (chainOf (hS.lev (m + 1)) M s hQ₁ rH₁) (chainOf (hS.lev m) M s hQ₀ rH₀) where
  sΛ := RingHom.id _
  sA := S.dA m
  sB := S.dB m
  fS n j := LinearMap.id
  fZn n j := nmHM (nmLevA S hS m M) l s none n j
  fZ j := nmHO (nmLevA S hS m M) l s j
  fW j := nmHO (nmLevB S hS m M) 1 s j
  fV j := LinearMap.id

end

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) {s s' : ℕ} (h : s ≤ s')
  (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (hQ' : ∀ T, QB L M s' T → QA L M s' (((nmB M hL).mor 0).obj T))
  (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)
  (rH' : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s') none ((l : L.A) ^ n) j)

def inclHM (n j : ℕ) : HM (QA L M s') none ((l : L.A) ^ n) j →ₗ[L.A] HM (QA L M s) none ((l : L.A) ^ n) j :=
  ((incl (ts_le L.γ M.p l h {⊤})).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial)
    (incl_std (ts_le L.γ M.p l h {⊤}) none ((l : L.A) ^ n))).pull j

def homS : Hom (chainOf hL M s' hQ' rH') (chainOf hL M s hQ rH) where
  sΛ := RingHom.id _
  sA := RingHom.id _
  sB := RingHom.id _
  fS n j := LinearMap.id
  fZn n j := inclHM M h n j
  fZ j := (incl (ts_le L.γ M.p l h {⊤})).o.pull j
  fW j := (incl (ts_le L.γB M.q 1 h {⊤})).o.pull j
  fV j := LinearMap.id

end

end CrystallineSemistableComparison.Pb.Kap
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomPullGoodRHof
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {R : Per l K} {m : ℕ} (L : Lev R m) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p)

def nmPullA : NMor L.γ N.p (κA (OK l K) L.I) L.γ M.p (κA (OK l K) L.I) (RingHom.id L.A) :=
  nmK L.γ L.γ N.p M.p (RingHom.id L.A) (DPMorphism.id L.γ).isDPMorphism (fun _ => rfl) u hu

def nmPullB : NMor L.γB N.q (κA K L.IB) L.γB M.q (κA K L.IB) (RingHom.id L.B) :=
  nmK L.γB L.γB N.q M.q (RingHom.id L.B) (DPMorphism.id L.γB).isDPMorphism (fun _ => rfl) (Model.genMap u hu)
    (Model.genMap_q u hu)

end

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ)
  (hQN : ∀ T, QB L N s T → QA L N s (((nmB N hL).mor 0).obj T))
  (hQM : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rHN : ∀ n j, N.Hc false n j →ₛₗ[L.lam] HM (QA L N s) none ((l : L.A) ^ n) j)
  (rHM : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

def homPull : Hom (chainOf hL N s hQN rHN) (chainOf hL M s hQM rHM) where
  sΛ := RingHom.id _
  sA := RingHom.id _
  sB := RingHom.id _
  fS n j := B.pullHc (okToOC l K) (B.schMap u hu) false n j
  fZn n j := nmHM (nmPullA L u hu) l s none n j
  fZ j := nmHO (nmPullA L u hu) l s j
  fW j := nmHO (nmPullB L u hu) 1 s j
  fV j := pullR j (Model.genMap u hu) (Model.genMap_q u hu)

namespace PullbackComparison

end PullbackComparison

end

section
variable {m : ℕ} {L : Lev (per l K) m}
  (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
  (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))
  {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ)

theorem lnMap_id {B : Type} [CommRing B] (k n : ℕ) (y : B ⧸ Ideal.span {(k : B) ^ n}) :
    lnMap (RingHom.id B) k (le_refl n) y = y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

theorem rHof_pull (n j : ℕ) (x : N.Hc false n j) :
    nmHM (nmPullA L u hu) l s none n j (rHof d hc N s n j x) =
      rHof d hc M s n j (B.pullHc (okToOC l K) (B.schMap u hu) false n j x) :=
  (red_nm (d n) (d n) s (nmPullA L u hu) _ _ _ _ _ (hc n) (hc n) _ _ (fun _ _ => rfl) (fun _ => (lnMap_id l n _).symm)
    none j x).symm

end

end CrystallineSemistableComparison.Pb.Kap
end
end

