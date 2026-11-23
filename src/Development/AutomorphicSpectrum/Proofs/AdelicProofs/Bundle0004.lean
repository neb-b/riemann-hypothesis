module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ProductFormulaLogNorms
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.WeilBound.CoreStatements.SesquilinearFractions.NIdealSum

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.ProductFormulaLogNormsStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_formula_log_norms : ∀ (k : Type) [Field k] [NumberField k] (x : k), x ≠ 0 → {p | (LogNorms.ofElt x).finSum p ≠ 0}.Finite ∧ (∑ s : k →+* ℂ, Real.log ‖s x‖) + ∑ᶠ p, (LogNorms.ofElt x).finSum p = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.product_formula_embeddings | exact GlobalTheory.CompanionTheory.Ar.Fl.product_formula_embeddings | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.product_formula_embeddings <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumLogIdealEqLogAbsNorm
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem sum_logIdeal_eq_log_norm_absNorm : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ → ∀ p : Nat.Primes, ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) I = Real.log ‖((Ideal.absNorm I : ℕ) : ℂ_[p])‖ :=
  @PositivityTheory.Xgf.sum_logIdeal_eq_log_absNorm

end GlobalTheory.CompanionTheory.Ar.Fl
end

