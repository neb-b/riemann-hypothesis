module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0029
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0025
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0026

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealSupportNonKlt
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem exists_isMultIdeal_support_iff_not_kltAt : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X), IsLogMult p n Δ η m G → ∃ J : X.IdealSheafData, IsMultIdeal p n η m G J ∧ ∀ x : X, x ∈ J.support ↔ ¬ KltAt p n Δ x := by
  intro hP k _ _ X _ _ _ p n hp hdim Δ η m G hL
  have hne : (⊥ : Closeds X) ≠ ⊤ := by
    intro h
    have hx : genericPoint X ∈ ((⊤ : Closeds X) : Set X) := trivial
    rw [← h] at hx
    exact hx
  obtain ⟨Y, hYi, s, hsd, K, B, hR, -⟩ :=
    LogResExist.exists_logRes hP k X p n hp hdim η m G hL.ne_zero ⊥ hne
  haveI := hYi
  haveI := hsd
  haveI := hR.smooth
  have hsm : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth (n := n) (f := s ≫ p)
  obtain ⟨-, -, hYn⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k Y (s ≫ p) hsm
  haveI := hYn
  obtain ⟨J, hJ⟩ := MultIdealExists.exists_isMultIdeal k X p n hp η m G Y s K B hL.ne_zero hL.pos hR
  exact ⟨J, hJ, mem_support_multIdeal_iff k X p n hp hdim Δ η m G Y s K B hL hR J hJ⟩

end GlobalTheory.Discrepancy
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwistStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.multiplier_vanishing_nef_twist : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ (N M T : LB X) (hN : N.IsLB) (hM : M.IsLB) (r : ℕ) (hT : letI := algebraΓOfHom p; IsNef k T), 0 < r → cls T (letI := algebraΓOfHom p; hT.isLB) = (m * r) • cls N hN - r • toPic G - m • cls M hM → (letI := algebraΓOfHom p; IsNef k M) → ∀ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), (0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd) → ∀ (Q : LB Y) (hQ : Q.IsLB), cls Q hQ = CechPic.pull s (cls N hN) - toPic F → ∀ i, 0 < i → Subsingleton (coh (twist (GlobalTheory.structureModule Y) Q) i) := by
  first | exact @_root_.GlobalTheory.Discrepancy.vanishing_logRes_floor | exact _root_.GlobalTheory.Discrepancy.vanishing_logRes_floor | (intros; apply _root_.GlobalTheory.Discrepancy.vanishing_logRes_floor <;> assumption)
end

