module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.RationalSupMetrics.AevalCoordProd
section
set_option linter.unusedSectionVars false

namespace MultiProjectiveCoordinates.Val

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mh_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem mh_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mh_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem mh_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  exact mh_add hf (mh_neg hg)

theorem map_aeval_int {σ R S : Type*} [CommRing R] [Algebra ℤ R] [CommRing S] [Algebra ℤ S]
    (φ : R →+* S) (z : σ → R) (f : MvPolynomial σ ℤ) :
    φ (aeval z f) = aeval (fun p => φ (z p)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, aeval_C, eq_intCast (algebraMap ℤ R), eq_intCast (algebraMap ℤ S), map_intCast]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X]

theorem aeval_scale {R : Type*} [CommRing R] [Algebra ℤ R] (z : (Σ k, ι k) → R) (t : K → R)
    {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval (fun p : Σ k, ι k => z p * t p.1) g = aeval z g * ∏ k, t k ^ d k := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_assoc]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← hg m hm k, ← Finset.prod_pow_eq_pow_sum]

variable {Ω : Type} [Field Ω]

theorem mem_of_form (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  have h := aeval_scale (fun p => (C (y p) : MvPolynomial K Ω)) (fun k => X k) hg
  rw [← map_aeval_int (C : Ω →+* MvPolynomial K Ω) y g, h0, map_zero, zero_mul] at h
  exact h

theorem form_vanish (y : (Σ k, ι k) → Ω) {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}
    (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (h0 : aeval y g = 0) : aeval z g = 0 :=
  hz.2 g (mem_of_form y hg h0)

end MultiProjectiveCoordinates.Val
end

-- bundled from Development.WeilBound.CoreStatements.RationalSupMetrics.AevalEqZeroOfMem
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace MultiProjectiveCoordinates

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

end MultiProjectiveCoordinates
end

