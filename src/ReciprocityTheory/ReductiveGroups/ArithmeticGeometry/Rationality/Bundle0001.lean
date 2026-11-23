module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BasisChangeSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

def BasisChangeStatement : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) [Fintype ι] (P : MvPolynomial ι K) (d : ℕ),
    P.IsHomogeneous d → (∀ μ, ‖AddMonoidAlgebra.coeff P μ‖ ≤ 1) →
    ∀ (A : ι → ι → K) (C : ℝ), 1 ≤ C → (∀ i k, ‖A i k‖ ≤ C) →
      ∀ μ, ‖AddMonoidAlgebra.coeff (MvPolynomial.bind₁ (fun i => ∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) P)
        μ‖ ≤ C ^ d

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BetaPf
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open Finset

theorem exists_int_avoid {f : ℕ} (Z : Finset (Fin f → ℝ)) (hZ : ∀ z ∈ Z, z ≠ 0) :
    ∃ t : Fin f → ℤ, ∀ z ∈ Z, ∑ j, z j * (t j : ℝ) ≠ 0 := by
  classical
  let P : (Fin f → ℝ) → Polynomial ℝ := fun z => ∑ j, Polynomial.C (z j) * Polynomial.X ^ (j : ℕ)
  have hP : ∀ z ∈ Z, P z ≠ 0 := by
    intro z hz h0
    apply hZ z hz
    funext j
    have h1 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p (j : ℕ)) h0
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single j (fun i _ hij => by
      rw [if_neg (fun h => hij (Fin.ext h.symm)), mul_zero]) (by simp)] at h1
    simpa using h1
  obtain ⟨T, hT⟩ : ∃ T : ℕ, (T : ℝ) ∉ Z.biUnion (fun z => (P z).roots.toFinset) := by
    by_contra h
    push_neg at h
    have hinf : Set.Infinite (Set.range (fun n : ℕ => (n : ℝ))) :=
      Set.infinite_range_of_injective Nat.cast_injective
    exact hinf ((Z.biUnion (fun z => (P z).roots.toFinset)).finite_toSet.subset
      (by rintro _ ⟨n, rfl⟩; exact h n))
  refine ⟨fun j => (T : ℤ) ^ (j : ℕ), fun z hz h0 => ?_⟩
  apply hT
  rw [Finset.mem_biUnion]
  refine ⟨z, hz, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hP z hz), Polynomial.IsRoot]
  simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  push_cast at h0
  exact h0

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FiniteDetectStatement
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

section Defs

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    Submodule F (F ⊗[K] V) :=
  Submodule.span F ((fun u => (1 : F) ⊗ₜ[K] u) '' (U : Set V))

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

end Defs

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

noncomputable def ordAt {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F]
    [Algebra R F] [IsFractionRing R F] (v : IsDedekindDomain.HeightOneSpectrum R) (x : F) : ℤ :=
  -WithZero.log (v.valuation F x)

def QuotLocalStatement : Prop :=
  ∀ (O Q : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup Q] [Module O Q] (ρ : ℕ), Nonempty (Module.Basis (Fin ρ) O Q) →
    ∀ (c : Fin ρ → (Q →ₗ[O] O)) (th : Fin ρ → Q),
      (Matrix.of fun i j => c i (th j)).det ≠ 0 →
      Module.length O (Q ⧸ Submodule.span O (Set.range th)) ≤
        IsDiscreteValuationRing.addVal O (Matrix.of fun i j => c i (th j)).det

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

