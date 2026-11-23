module

public import Mathlib
public import Formalism.PeriodIntegrals.GTDefs
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal

@[expose] public section

noncomputable section

namespace PI.GTS

open Formalism.BasicNotions MvPolynomial

private theorem fockF_eq_sum_lemma {σ : Type*} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  apply Finset.sum_subset hS
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]

theorem fockF_smul_self {σ : Type*} (c : ℂ) (f : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (c • f) (c • f) = (c * star c) * Formalism.REAL.fockF f f := by
  rw [fockF_eq_sum_lemma (c • f) _ f.support MvPolynomial.support_smul,
    fockF_eq_sum_lemma f f f.support subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem re_normFock_smul {N : ℕ} (lam : DomWeight N) (c : ℂ) (x : MvPolynomial (Fin N × Fin N) ℂ) :
    (normFock lam (c • x) (c • x)).re = ‖c‖ ^ 2 * (normFock lam x x).re := by
  unfold normFock
  rw [fockF_smul_self, mul_div_assoc]
  have hc : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [show star c = (starRingEnd ℂ) c from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hc, Complex.re_ofReal_mul]

end PI.GTS
