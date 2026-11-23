module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.AsmOnto
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.Bundle0003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0600
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0612
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0609

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.L2

theorem hdg_aff_iso_onto (hA : CrystallineSemistableComparison.Onto.AffOm) (hN : CrystallineSemistableComparison.Onto.OmNat) :
    ∀ (K : Type) [Field K] [CharZero K],
    ∃ (e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ),
      HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (ε : ℕ → ℕ → ℤ), (∀ a b, ε a b = 1 ∨ ε a b = -1) ∧
    (∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q]
      [IsAffine Y] [Smooth p] (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (x : HT.Hdg p a a),
      e q a (HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e p a x))) ∧
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a b c : ℕ) (h : a + b = c)
      (x : HT.Hdg q a a) (y : HT.Hdg q b b),
      e q c (HT.cupH q h h x y) = ε a b • wedgeOm K (Sec q ⊤) h (e q a x) (e q b y)) ∧
    ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q], e q 0 (HT.oneH q) = oneOm K (Sec q ⊤) :=
  asm_onto hA hN _root_.GlobalTheory.CompanionTheory.HodgeFormTop.main _root_.GlobalTheory.CompanionTheory.OmGlue.om_top _root_.GlobalTheory.CompanionTheory.OmNatT.pull_nat _root_.GlobalTheory.CompanionTheory.OmCup.main GlobalTheory.T.hodge_form_one

end CrystallineSemistableComparison.Om.L2
