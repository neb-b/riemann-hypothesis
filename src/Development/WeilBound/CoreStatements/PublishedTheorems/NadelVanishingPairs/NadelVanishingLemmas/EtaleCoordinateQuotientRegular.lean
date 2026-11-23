module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0462

@[expose] public section

theorem _root_.GlobalTheory.T.etale_coordinate_quotient_regular : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ j : Fin n, IsRegularRing (A ⧸ Ideal.span {t j}) := by
  first | exact @_root_.GlobalTheory.isRegularRing_quotient_etaleCoordinate | exact _root_.GlobalTheory.isRegularRing_quotient_etaleCoordinate | (intros; apply _root_.GlobalTheory.isRegularRing_quotient_etaleCoordinate <;> assumption)
