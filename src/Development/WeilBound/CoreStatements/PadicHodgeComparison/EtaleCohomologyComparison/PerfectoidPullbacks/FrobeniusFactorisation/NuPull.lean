module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0306
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0292
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuFrobeniusCompat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0296
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0284

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem bW_red (r : Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M (n + 1)) :
    (redT r M (Nat.le_succ n)).pull j (bW r M (n + 1) j y) = bW r M n j ((HSW r M j).r n y) := by apply GlobalTheory.T.witt_comparison_reduction_compat

theorem bW_phi (r : Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M n) :
    phiM r M n j (bW r M n j y) = bW r M n j ((Wc.phiS l (B.schFn M.p) r.ρ j).f n y) := by apply _root_.GlobalTheory.CompanionTheory.BaseChangeFrob.phiM_bW

theorem bW_gal (r : Res l K) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ)
    (y : (HSW r M j).M n) : galM r M σ hσ n j (bW r M n j y) = bW r M n j y := by apply _root_.GlobalTheory.CompanionTheory.BWGal.bW_gal

theorem bW_pull (r : Res l K) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ) (y : (HSW r N j).M n) :
    pullM r u hu n j (bW r N n j y) = bW r M n j ((Wc.pullS l r.ρ (B.schMap u hu) j).f n y) := by apply _root_.GlobalTheory.CompanionTheory.CrisBase.pullM_bW

theorem nu_red (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ)
    (x : B.Hc (B.schFn M.p) (okToOC l K) true (n + 1) j) :
    (redT r M (Nat.le_succ n)).pull j (Mid.nu r M (n + 1) j hT x) =
      Mid.nu r M n j hT (B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j x) := by apply _root_.GlobalTheory.CompanionTheory.NuRed.nu_red

theorem nu_phi (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ)
    (x : B.Hc (B.schFn M.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.phiHc (B.schFn M.p) (okToOC l K) n j x) = phiM r M n j (Mid.nu r M n j hT x) := by apply _root_.GlobalTheory.CompanionTheory.NuPhi.nu_phi

theorem nu_gal (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K))
    (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j x) =
      galM r M σ hσ n j (Mid.nu r M n j hT x) := by apply _root_.GlobalTheory.CompanionTheory.NuGalSquare.nu_gal

theorem nu_pull (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) {M M' : Model l K} (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p)
    (n j : ℕ) (x : B.Hc (B.schFn M'.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.pullHc (okToOC l K) (B.schMap u hu) true n j x) = pullM r u hu n j (Mid.nu r M' n j hT x) := by apply _root_.GlobalTheory.CompanionTheory.NuPull.nu_pull

theorem mu_red (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j) :
    B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j (Mid.mu r M (n + 1) j hT t) =
      Mid.mu r M n j hT ((redT r M (Nat.le_succ n)).pull j t) := by apply GlobalTheory.T.teichmuller_mu_reduction_compat

theorem mu_gal (r : Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K))
    (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (t : Mid.HM r M n j) :
    B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j (Mid.mu r M n j hT t) =
      Mid.mu r M n j hT (galM r M σ hσ n j t) := by apply _root_.GlobalTheory.CompanionTheory.MuGal.mu_gal

theorem flatW (r : Res l K) : Module.Flat (WittVector l r.k) (AW r) := by apply _root_.GlobalTheory.CompanionTheory.FlatW.flat_AW

theorem adicA : IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := by apply _root_.GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete

end CrystallineSemistableComparison.Pb
