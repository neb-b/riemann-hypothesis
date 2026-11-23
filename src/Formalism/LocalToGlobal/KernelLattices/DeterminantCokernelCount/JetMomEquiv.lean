module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA

@[expose] public section

noncomputable section

namespace Formalism.L2.Ker.I3.JetMomEq

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.Ker.I3.JetMomA

section Clauses

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ) {q : ℕ} [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q]) {N N' r : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
  (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (μ : Meas q r)

end Clauses

section Stmts

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ) {q : ℕ} [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q])


end Stmts

section Zero

variable {D : D7} {q : ℕ} [Fact q.Prime]

theorem wPh_of_int (T : Tor D) {N N' : ℕ} (x : VC D N N') (m : ℤ) (h : qH D T x = m) :
    wPh D T q x = Complex.exp ((Real.pi : ℂ) * Complex.I * (qH D T x : ℂ)) := by
  have hE : Complex.exp ((Real.pi : ℂ) * Complex.I * (qH D T x : ℂ)) = (-1 : ℂ) ^ m := by
    rw [h, show (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * (Real.pi * Complex.I) by
      push_cast; ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  unfold wPh
  split_ifs with hq
  · rfl
  · rw [hE]
    have hex : ∃ s : ℂ, ∃ (k : ℕ) (m' : ℤ), (q : ℝ) ^ k * qH D T x = (m' : ℝ) ∧ s = (-1 : ℂ) ^ m' :=
      ⟨(-1 : ℂ) ^ m, 0, m, by rw [h]; simp, rfl⟩
    obtain ⟨k, m', hm', hs⟩ := Classical.epsilon_spec hex
    rw [hs]
    rw [h] at hm'
    have hm'' : m' = (q : ℤ) ^ k * m := by exact_mod_cast hm'.symm
    have hodd : Odd ((q : ℤ) ^ k) := by
      have := ((Fact.out : q.Prime).odd_of_ne_two hq).pow (n := k)
      exact_mod_cast this
    rw [hm'', zpow_mul, hodd.neg_one_zpow]

end Zero

section Imp

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ) {q : ℕ} [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q]) {N N' r : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
  (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (μ : Meas q r)

end Imp

section Rec

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ)

end Rec

section Merged

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {q : ℕ} [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q]) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (μ : Meas q r)
  (G : VC D N N' → ℂ)

end Merged

variable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ) (q : ℕ) [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q])

end Formalism.L2.Ker.I3.JetMomEq
