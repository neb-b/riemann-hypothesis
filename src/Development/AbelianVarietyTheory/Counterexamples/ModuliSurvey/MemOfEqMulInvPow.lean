module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.JointModelGuards

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem mem_of_eq_mul_inv_pow (W : ValuationSubring ℂ) {x a : ℂ} (ha : a ∈ W) (n : ℕ) (h : x = a * x⁻¹ ^ n) :
    x ∈ W := by
  rcases W.mem_or_inv_mem x with hx | hx
  · exact hx
  · rw [h]; exact mul_mem ha (pow_mem hx n)

theorem exists_root_and_zeta (l : Level H) (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃ r z : c.V W, (((c.V W).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W).subtype z : c.F) : ℂ) = zeta l.A := by
  have hr : H.rt0 ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hz : zeta l.A ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h => by
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    exact hd (by simpa using this)
  have hrW : H.rt0 ∈ W := mem_of_eq_mul_inv_pow W (a := -(H.d : ℂ)) (neg_mem (natCast_mem W _)) 1 (by
    rw [← H.sqrt_neg_disc_sq]; field_simp)
  have hp : IsPrimitiveRoot (zeta l.A) l.A := Complex.isPrimitiveRoot_exp l.A l.A_pos.ne'
  have hz0 : zeta l.A ≠ 0 := hp.ne_zero l.A_pos.ne'
  have hzW : zeta l.A ∈ W := mem_of_eq_mul_inv_pow W (a := 1) (one_mem W) (l.A - 1) (by
    have h1 : zeta l.A * zeta l.A ^ (l.A - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel l.A_pos]; exact hp.pow_eq_one
    rw [one_mul, inv_pow]
    exact eq_inv_of_mul_eq_one_left h1)
  exact ⟨⟨⟨_, hr⟩, hrW⟩, ⟨⟨_, hz⟩, hzW⟩, rfl, rfl⟩

end GlobalTheory.JointModelGuards
