module

public import Mathlib

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LatticeBoundTests
open NumberField

section Trace
variable (E : Type) [Field E] [NumberField E] [IsCMField E]

def trBil : 𝓞 E →ₗ[ℤ] 𝓞 E →ₗ[ℤ] ℝ :=
  LinearMap.mk₂ ℤ (fun x y => ∑ σ : E →+* ℂ, (σ (x : E) * starRingEnd ℂ (σ (y : E))).re)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun k x y => by simp [Finset.mul_sum, mul_assoc, mul_add])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun k x y => by simp [Finset.mul_sum, mul_add, mul_left_comm])

omit [IsCMField E] in
theorem trBil_apply (x y : 𝓞 E) :
    trBil E x y = ∑ σ : E →+* ℂ, (σ (x : E) * starRingEnd ℂ (σ (y : E))).re := rfl

omit [IsCMField E] in
theorem trBil_symm (x y : 𝓞 E) : trBil E x y = trBil E y x := by
  rw [trBil_apply, trBil_apply]
  exact Finset.sum_congr rfl fun σ _ => by simp [mul_comm]

omit [IsCMField E] in
theorem trBil_posDef :
    (Matrix.of fun i j => trBil E (RingOfIntegers.basis E i) (RingOfIntegers.basis E j)).PosDef := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun t ht => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial, trBil_apply]
    exact Finset.sum_congr rfl fun σ _ => by simp [mul_comm]
  · set u : (E →+* ℂ) → ℂ := fun σ => ∑ i, (t i : ℂ) * σ (RingOfIntegers.basis E i : E) with hu
    have key : star t ⬝ᵥ (Matrix.of fun i j => trBil E (RingOfIntegers.basis E i)
        (RingOfIntegers.basis E j)).mulVec t = ∑ σ, Complex.normSq (u σ) := by
      have : ∀ σ, Complex.normSq (u σ) = ∑ i, ∑ j, t i * ((σ (RingOfIntegers.basis E i : E) *
          starRingEnd ℂ (σ (RingOfIntegers.basis E j : E))).re * t j) := by
        intro σ
        rw [← Complex.ofReal_re (Complex.normSq (u σ)), ← Complex.mul_conj, hu]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, Finset.sum_mul_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp; ring
      simp only [this, dotProduct, Matrix.mulVec, Matrix.of_apply, trBil_apply, star_trivial,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm (γ := E →+* ℂ)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm (γ := E →+* ℂ)]
    rw [key]
    refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) fun h0 => ht ?_
    have hz : ∀ σ, u σ = 0 := fun σ => Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 h0.symm σ
        (Finset.mem_univ _))
    have li := Fintype.linearIndependent_iff.1 (canonicalEmbedding.latticeBasis E).linearIndependent
      (fun i => (t i : ℂ)) (by
        funext σ
        have := hz σ
        simpa [hu, canonicalEmbedding.latticeBasis_apply, integralBasis_apply] using this)
    funext i
    exact_mod_cast li i

end Trace

end GlobalTheory.LatticeBoundTests
