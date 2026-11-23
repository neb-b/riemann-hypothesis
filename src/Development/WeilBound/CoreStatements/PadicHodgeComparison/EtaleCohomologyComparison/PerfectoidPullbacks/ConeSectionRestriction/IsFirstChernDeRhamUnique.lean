module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.PowTop
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTwistingLineDataProjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0169
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0009

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem isO1At_exists {R : Type} [CommRing R] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace R N) :
    ∃ D : E.LineData X, IsTautologicalLineAt D N i := _root_.GlobalTheory.CompanionTheory.ConeTwistingSheafMap.main N i

theorem isO1_exists {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (hp : IsProjOver p) :
    ∃ D : E.LineData X, IsTautologicalLine p D := by
  obtain ⟨N, i, hi, hip⟩ := hp
  obtain ⟨D, hD⟩ := isO1At_exists N i
  exact ⟨D, N, i, hi, hip, hD⟩

theorem isTwistingSheaf_pullback {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}} (p : X ⟶ Sp R)
    (D : E.LineData X) (hD : IsTautologicalLine p D) :
    IsTautologicalLine (pullback.snd p (spMap φ)) (D.pb (pullback.fst p (spMap φ))) := GlobalTheory.T.twisting_sheaf_base_change φ p D hD

theorem isFirstChernDeRham_exists {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) :
    ∃ c : HdR q 2, IsFirstChernDeRham q D c := isFirstChernDeRham_exists_of q d D hD

theorem isO1_etale {R : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ Sp R} {D : E.LineData X} (hD : IsTautologicalLine p D) :
    Etale D.f := by
  obtain ⟨N, i, -, -, h, -⟩ := hD
  exact h

theorem powK_ne_zero {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) (c : HdR q 2)
    (hc : IsFirstChernDeRham q D c) : powK q c d ≠ 0 := powK_ne_zero_main q d D hD c hc

end CrystallineSemistableComparison.Pb
