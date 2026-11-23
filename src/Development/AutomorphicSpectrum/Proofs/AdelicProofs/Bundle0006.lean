module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0030

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianLatticeDegreeEqBundleDegreeStatement
section
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_lattice_degree_eq_bundle_degree : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L)) (Fl : HermLattice L i), LinearIndependent (𝓞 L) f → i = B.rank F → Function.Injective c → (∀ j, c (f j) = Pi.single j 1) → Fl.lattice = LinearMap.range c → (∀ σ, Fl.metric σ = gramMat B σ (fun j => (f j : B.carrier))) → Fl.degree = B.degreeWith F f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith | exact GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianMetricLogNormFormula
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem deg_eq_of_local_two_curves : ∀ (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E] (τ : E →+* k) (N : LogNorms k) (ρ : k) (a r : E) (p q d : ℕ) (n n' : (k →+* ℂ) → ℝ) (x : ℝ) (t t' : Nat.Primes → E), ρ ≠ 0 → a ≠ 0 → 0 < d → r ^ 2 = -(d : E) → -(∑ s, Real.log (n s)) / Module.finrank ℚ k = x → -(∑ s, Real.log (n' s)) / Module.finrank ℚ k = x → (∀ s, N.inf s = Real.log ‖s ρ‖ + ((p : ℝ) / 2 * (Real.log (n s) + Real.log d / 2) - (q : ℝ) / 2 * (Real.log (n' s) + Real.log d / 2)) + Real.log ‖s (τ a)‖ / 2) → (∀ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t' ℓ)‖ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖) → (∀ (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]), Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖ = -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite → (∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j + q * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖ - q * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((q : ℝ) - p) * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (τ r)‖)) → N.IsAdelic ∧ N.deg = ((p : ℝ) - q) / 2 * (x - Real.log (rootDiscr E) + Real.log (Real.sqrt d)) + q * (2 * Real.log (Real.sqrt d) - Real.log (rootDiscr E)) := by
  intro k E _ _ _ _ τ N ρ a r p q d n n' x t t' hρ ha hd hr hn hn' hinf ht ht2 hfin hloc
  let N' : LogNorms k :=
    ⟨fun s => N.inf s + (q : ℝ) / 2 * (Real.log (n' s) - Real.log (n s)), N.fin⟩
  have h := _root_.GlobalTheory.CompanionTheory.Ar.Fl.LocalSum.deg_of_local_formulas k E τ N' ρ a r p q d n x t t' hρ ha hd hr hn
    (fun s => by
      change N.inf s + (q : ℝ) / 2 * (Real.log (n' s) - Real.log (n s)) = _
      rw [hinf s]
      ring)
    ht ht2 hfin (fun ℓ j => hloc ℓ j)
  have hf : (Module.finrank ℚ k : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hs : ∑ s, Real.log (n' s) = ∑ s, Real.log (n s) := by
    have e := hn'.trans hn.symm
    rw [div_left_inj' hf] at e
    linarith
  have hsum : ∑ s, N'.inf s = ∑ s, N.inf s := by
    change ∑ s, (N.inf s + (q : ℝ) / 2 * (Real.log (n' s) - Real.log (n s))) = _
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hs]
    simp
  have hdeg : N'.deg = N.deg := by
    unfold LogNorms.deg
    rw [hsum]
    rfl
  exact ⟨h.1, hdeg ▸ h.2⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LinearIndependentCoordinatesDenominatorStatement
section
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_independent_coordinates_denominator : ∀ (L : Type) [Field L] [NumberField L] (M : Type) [AddCommGroup M] [Module (𝓞 L) M] [Module.Finite (𝓞 L) M] [Module.IsTorsionFree (𝓞 L) M] (i : ℕ) (f : Fin i → M), LinearIndependent (𝓞 L) f → i = Module.finrank (𝓞 L) M → ∃ c : M →ₗ[𝓞 L] (Fin i → L), Function.Injective c ∧ (∀ j, c (f j) = Pi.single j 1) ∧ ∀ x, ∃ (D : 𝓞 L) (a : Fin i → 𝓞 L), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧ ∀ j, (D : L) * c x j = a j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.Coords.coordinates_of_maximal_independent | exact GlobalTheory.CompanionTheory.Ar.Lines.Coords.coordinates_of_maximal_independent | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.Coords.coordinates_of_maximal_independent <;> assumption)
end

