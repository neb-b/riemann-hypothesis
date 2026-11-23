module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealMulSpanMap
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem logIdeal_mul_span_map : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]), Function.Injective j → (∀ I J : Ideal (𝓞 E), I ≠ ⊥ → J ≠ ⊥ → logIdeal j (I * J) = logIdeal j I + logIdeal j J) ∧ (∀ a : 𝓞 E, logIdeal j (Ideal.span {a}) = Real.log ‖j a‖) ∧ ∀ e : 𝓞 E ≃+* 𝓞 E, ∀ I : Ideal (𝓞 E), logIdeal j (I.map (e : 𝓞 E →+* 𝓞 E)) = logIdeal (j.comp (e : 𝓞 E →+* 𝓞 E)) I :=
  @PositivityTheory.Xgf.log_ideal_mul_span_map

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealSupportFinite
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem finite_logIdeal_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ →
    {p : Nat.Primes | ∃ j : 𝓞 E →+* ℂ_[p], logIdeal j I ≠ 0}.Finite :=
  @PositivityTheory.Xgf.logIdeal_support_finite

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsExtDegreeAdelic
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem logNorms_ext_deg_isAdelic : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') (N : LogNorms k), (N.ext f).deg = N.deg ∧ ((N.ext f).IsAdelic ↔ N.IsAdelic) :=
  @PositivityTheory.Xgf.logNorms_ext_degree_adelic

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsOfNonzeroAdelicStatement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norms_of_nonzero_adelic : ∀ (k : Type) [Field k] [NumberField k] (x : k), x ≠ 0 → (LogNorms.ofElt x).IsAdelic := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.isAdelic_ofElt | exact GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.isAdelic_ofElt | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.isAdelic_ofElt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicLogIdealMaxElement
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_logIdeal_attained : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]) (I : Ideal (𝓞 E)), Function.Injective j → I ≠ ⊥ → ∃ a ∈ I, a ≠ 0 ∧ (∀ b ∈ I, ‖j b‖ ≤ ‖j a‖) ∧ logIdeal j I = Real.log ‖j a‖ :=
  @PositivityTheory.Xgf.padic_logIdeal_max_element

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.RatProductFormula
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem rat_product_formula_complex : ∀ r : ℚ, r ≠ 0 → {p : Nat.Primes | Real.log ‖(r : ℂ_[p])‖ ≠ 0}.Finite ∧ Real.log ‖(r : ℂ)‖ + ∑ᶠ p : Nat.Primes, Real.log ‖(r : ℂ_[p])‖ = 0 :=
  PositivityTheory.Xgf.rat_product_formula

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumEmbeddingsBaseChange
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem finrank_mul_sum_comp_eq : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (F : (k →+* A) → ℝ), (Module.finrank ℚ k : ℝ) * ∑ j : k' →+* A, F (j.comp f) = (Module.finrank ℚ k' : ℝ) * ∑ j : k →+* A, F j :=
  PositivityTheory.Xgf.sum_embeddings_base_change

end GlobalTheory.CompanionTheory.Ar.Fl
end

