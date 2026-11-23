module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

@[expose] public section

set_option autoImplicit false

noncomputable section

open DividedPowers Polynomial TensorProduct

namespace GlobalTheory.PDA.Model

def xd (n : ℕ) : ℚ[X] := monomial n ((n.factorial : ℚ)⁻¹)

theorem xd_zero : xd 0 = 1 := by simp [xd]

theorem xd_mul (m n : ℕ) : xd m * xd n = ((m + n).choose m : ℚ[X]) * xd (m + n) := by
  have h : (((m + n).choose m : ℕ) : ℚ[X]) = C (((m + n).choose m : ℕ) : ℚ) := by simp
  rw [h, xd, xd, xd, monomial_mul_monomial, C_mul_monomial]
  congr 1
  have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hmn : ((m + n).factorial : ℚ) ≠ 0 := by exact_mod_cast (m + n).factorial_ne_zero
  have := Nat.add_choose_mul_factorial_mul_factorial m n
  rw [← Nat.choose_symm_add] at this
  have h2 : (((m + n).choose m : ℕ) : ℚ) * m.factorial * n.factorial = (m + n).factorial := by
    exact_mod_cast this
  field_simp
  linarith

theorem xd_li : LinearIndependent ℤ xd := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have := congrArg (fun p : ℚ[X] ↦ p.coeff i) hg
  simp only [finsetSum_coeff, xd, coeff_zero, AddMonoidAlgebra.coeff_smul_apply, coeff_monomial] at this
  rw [Finset.sum_eq_single i (by intro j _ hj; simp [hj]) (by intro h; exact absurd hi h)] at this
  have hm : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  simpa [hm] using this

def L : Subalgebra ℤ ℚ[X] :=
  (Submodule.span ℤ (Set.range xd)).toSubalgebra
    (xd_zero ▸ Submodule.subset_span ⟨0, rfl⟩)
    (by
      intro x y hx hy
      refine Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ Submodule.span ℤ (Set.range xd))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
      · rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
        rw [xd_mul, ← nsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      · intro y _; simp
      · intro y _; simp
      · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
      · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
      · intro r x y _ _ h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
      · intro r x y _ _ h; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h)

def bL : Module.Basis ℕ ℤ L := Module.Basis.span xd_li

theorem bL_coe (n : ℕ) : (bL n : ℚ[X]) = xd n := Module.Basis.span_apply xd_li n ▸ rfl

theorem bL_zero : bL 0 = 1 := Subtype.ext (by rw [bL_coe, xd_zero]; rfl)

theorem bL_mul (m n : ℕ) : bL m * bL n = ((m + n).choose m : L) * bL (m + n) :=
  Subtype.ext (by simp [bL_coe, xd_mul])

def pdPoly (B : Type) [CommRing B] : PDPoly B where
  P := B ⊗[ℤ] L
  e := Algebra.TensorProduct.basis B bL
  e_zero := by simp [bL_zero, Algebra.TensorProduct.one_def]
  e_mul m n := by
    simp only [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, bL_mul]
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, tmul_smul]

variable {B : Type} [CommRing B] {J : Ideal B}

end GlobalTheory.PDA.Model
